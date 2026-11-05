// ==UserScript==
// @name         Google Chat Stalker
// @namespace    https://github.com/chromecrash/google-chat-stalker
// @version      9.1
// @description  Locally logs Google Chat messages (formatting, edits, deletions, all attachment types), reaction history, AND people's presence status / last-online times in IndexedDB, with a combined log viewer (Messages + Presence tabs)
// @author       chromecrash
// @homepageURL  https://github.com/chromecrash/google-chat-stalker
// @supportURL   https://github.com/chromecrash/google-chat-stalker/issues
// @updateURL    https://github.com/chromecrash/google-chat-stalker/raw/refs/heads/main/google-chat-stalker.user.js
// @downloadURL  https://github.com/chromecrash/google-chat-stalker/raw/refs/heads/main/google-chat-stalker.user.js
// @match        https://chat.google.com/*
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      google.com
// @connect      googleusercontent.com
// @connect      googleapis.com
// @connect      gstatic.com
// @run-at       document-idle
// ==/UserScript==

(function () {
    'use strict';

    // With @grant the script runs sandboxed. Console helpers must be handed
    // to the real page window (Firefox needs exportFunction for that). The
    // proxy keeps the simple `pageWindow.name = fn` assignments working.
    const realPageWindow = typeof unsafeWindow !== 'undefined' ? unsafeWindow : window;

    function exposeGlobal(name, fn) {
        try {
            if (typeof exportFunction === 'function' && typeof unsafeWindow !== 'undefined') {
                exportFunction(fn, unsafeWindow, { defineAs: name });
                return;
            }
        } catch { /* fall through */ }

        try {
            (window.wrappedJSObject || realPageWindow)[name] = fn;
        } catch {
            try { realPageWindow[name] = fn; } catch { /* ignore */ }
        }
    }

    const pageWindow = new Proxy({}, {
        set(target, name, value) {
            exposeGlobal(String(name), value);
            return true;
        }
    });

    // --------------------------------------------------
    // Constants and state
    // --------------------------------------------------

    const STORAGE_KEY = 'gchat_logged_messages';
    const UI_KEY = 'gchat_logger_ui';
    const DB_NAME = 'gchat_logger_files';
    const DB_VERSION = 3;
    const DB_STORE = 'attachments';
    const AVATAR_STORE = 'avatars';
    const LOG_STORE = 'logs';
    const MIGRATED_KEY = 'gchat_logger_logs_in_idb';
    const PERSIST_DELAY_MS = 300;        // writes are batched for this long
    const AVATAR_KEY = 'gchat_logger_avatars';

    const MESSAGE_SELECTOR = '.B8q9Gf.qnQFwb.VYsRpc.hu21Y';
    const GROUP_SELECTOR = '.F0wyae.oGsu4';
    const TEXT_SELECTOR = '[jsname="bgckF"]';
    const TIMESTAMP_SELECTOR = '[data-absolute-timestamp]';

    const OWN_ATTR = 'data-gc-logger';
    const UNKNOWN_CONVERSATION = 'Unknown conversation';

    const SCAN_DELAY_MS = 500;
    const AUTO_RETRY_MS = 60000;
    const MAX_AUTO_ATTEMPTS = 5;
    const VIEWER_PAGE_SIZE = 150;

    const MIN_ATTACHMENT_SIZE = 45;

    // Largest attachment that will be stored locally (any type)
    const MAX_FILE_BYTES = 50 * 1024 * 1024;

    // Accuracy tuning
    const CONVERSATION_SETTLE_MS = 800;  // wait after switching chats before scanning
    const EDIT_STABLE_MS = 1200;         // new text must stay unchanged this long to count as an edit
    const PARTIAL_RENDER_MS = 5000;      // ignore "growing text" right after a message is first logged
    const SCROLL_QUIET_MS = 2000;        // never flag while scrolling / loading history
    const MISSING_GRACE_MS = 2500;       // a message must stay gone this long to be flagged

    // Reactions
    const REACTION_SELECTOR = '[jsname="wTe6Qc"]';
    const REACTION_HOST_SELECTOR = '[jsname="o7uNDd"]';
    const REACTION_SCAN_MS = 150;        // reaction changes are checked this soon after they happen
    const REACTION_WARMUP_MS = 3000;     // after opening a chat, let reaction bars finish rendering
    const MAX_REACTION_EVENTS = 200;     // history kept per message
    const REACTION_PROBE = true;         // briefly open Google's hover popup to read WHO reacted
    const REACTION_PROBE_BASELINE = true; // also read the reactor list of reactions already on screen
    const REACTION_POPUP_WAIT_MS = 1800; // how long to wait for the popup to fill
    const REACTION_PROBE_RETRY_MS = 5 * 60 * 1000; // retry a failed read after this long

    // Performance tuning (nothing is skipped permanently, only re-read less often)
    const MIN_SCAN_INTERVAL_MS = 1000;   // never run page scans more often than this
    const FULL_RESCAN_MS = 8000;         // re-read an unchanged message at least this often
    const STUB_SCAN_MS = 2500;           // how often to look for "message deleted" rows
    const AVATAR_RETRY_MS = 30000;       // how often to retry finding a missing profile photo

    // Presence logger
    const P_DB_NAME = 'gchat-presence';  // same database the standalone presence script used
    const P_STORE = 'events';
    const P_SEL = '[data-availability-context][jsdata*="human/"]';
    const P_HEARTBEAT_MS = 5 * 60 * 1000; // re-log an unchanged status this often
    const P_SCAN_INTERVAL_MS = 30 * 1000; // fallback scan if the observer misses something
    const P_MIN_SCAN_MS = 1500;           // never scan presence more often than this
    const P_ONLINE_RE = /^active$/i;      // what counts as "online"
    const P_NAMES_KEY = 'gchat_presence_names';
    const P_TRACK = new Set([]);          // e.g. new Set(['110165576219178347092']); empty = everyone visible

    const IMAGE_EXT_RE = /^(png|jpe?g|gif|webp|bmp|svg|avif)$/i;
    const VIDEO_EXT_RE = /^(mp4|webm|mov|m4v|ogv)$/i;
    const AUDIO_EXT_RE = /^(mp3|wav|ogg|m4a|flac|aac)$/i;
    // Image types the browser can actually render as a preview
    const RENDERABLE_IMAGE_TYPE_RE = /^image\/(png|jpe?g|gif|webp|bmp|svg\+xml|avif)$/i;

    // Text Google shows in place of a deleted message
    const DELETED_RE =
        /^(this message (was|has been) deleted|message deleted|you deleted this message|[^\n]{0,60} deleted this message)/i;

    // Standalone "Message deleted by its author" rows Google leaves in the list
    const STUB_RE =
        /^(this message (was|has been) deleted|message deleted|you deleted this message)\b/i;

    let database = null;
    let scanTimer = null;
    let scanQueued = false;
    let chain = Promise.resolve();
    let observer = null;
    let previousVisibleIds = new Set();
    let previousChatPath = '';
    let lastSeenPath = '';
    let pathSince = 0;
    let storageAlertShown = false;
    let lastScrollAt = 0;
    let newDataAvailable = false;
    let renderToken = 0;
    let renderLimit = VIEWER_PAGE_SIZE;
    let escHandler = null;
    let logCache = null;       // the whole log, kept in memory
    let dbLogs = false;        // true once the log lives in IndexedDB
    let persistTimer = null;
    let persistFull = false;
    let persistInFlight = Promise.resolve();
    let storageInfo = '';
    let storageInfoAt = 0;
    const persistIds = new Set();      // logs changed since the last write
    const persistedSig = new Map();    // id -> signature of what IndexedDB holds
    let lastScanAt = 0;
    let scanDue = 0;
    let lastScanMs = 0;
    let lastStubScanAt = 0;

    // Per message element: what was last read from it (see readMessage)
    const scanCache = new WeakMap();
    // Annotation elements we inserted, found without searching the whole page
    const annotationIndex = new Map();

    const liveElements = new Map();
    const pendingMarkers = new Set();
    const missingSince = new Map();
    const pendingEdits = new Map();
    let reactionTimer = null;

    const ui = loadUiPrefs();

    function exclusive(task) {
        const run = chain.then(task);
        chain = run.catch(() => {});
        return run;
    }

    function loadUiPrefs() {
        const defaults = {
            chat: 'all',
            sort: 'newest',
            status: 'all',
            tab: 'messages',
            pfilter: 'all',
            psort: 'recent'
        };

        try {
            return {
                ...defaults,
                ...JSON.parse(localStorage.getItem(UI_KEY) || '{}')
            };
        } catch {
            return defaults;
        }
    }

    function saveUiPrefs() {
        try {
            localStorage.setItem(UI_KEY, JSON.stringify(ui));
        } catch { /* ignore */ }
    }

    // --------------------------------------------------
    // IndexedDB (attachment blobs)
    // --------------------------------------------------

    function openDatabase() {
        return new Promise((resolve, reject) => {
            const request = indexedDB.open(DB_NAME, DB_VERSION);

            request.onupgradeneeded = function () {
                const db = request.result;

                [DB_STORE, AVATAR_STORE, LOG_STORE].forEach(name => {
                    if (!db.objectStoreNames.contains(name)) {
                        db.createObjectStore(name, { keyPath: 'id' });
                    }
                });
            };

            request.onblocked = function () {
                console.warn(
                    '[GC Logger] The database upgrade is waiting for your other ' +
                    'Google Chat tabs to be closed or reloaded.'
                );
            };

            request.onsuccess = function () {
                const db = request.result;

                // Let a newer script version upgrade the database instead of blocking it.
                db.onversionchange = () => {
                    db.close();

                    if (database === db) {
                        database = null;
                    }
                };

                database = db;
                resolve(db);
            };

            request.onerror = function () {
                reject(request.error);
            };
        });
    }

    function storeImage(id, blob, mimeType) {
        return new Promise((resolve, reject) => {
            const transaction = database.transaction(DB_STORE, 'readwrite');

            transaction.objectStore(DB_STORE).put({
                id: id,
                blob: blob,
                mimeType: mimeType,
                savedAt: new Date().toISOString()
            });

            transaction.oncomplete = () => resolve(true);
            transaction.onerror = () => reject(transaction.error);
            transaction.onabort = () => reject(transaction.error);
        });
    }

    function getStoredImage(id) {
        return new Promise((resolve, reject) => {
            if (!database) {
                resolve(null);
                return;
            }

            const transaction = database.transaction(DB_STORE, 'readonly');
            const request = transaction.objectStore(DB_STORE).get(id);

            request.onsuccess = () => resolve(request.result || null);
            request.onerror = () => reject(request.error);
        });
    }

    function deleteImage(id) {
        return new Promise(resolve => {
            if (!database) {
                resolve();
                return;
            }

            const transaction = database.transaction(DB_STORE, 'readwrite');

            transaction.objectStore(DB_STORE).delete(id);

            transaction.oncomplete = () => resolve();
            transaction.onerror = () => resolve();
            transaction.onabort = () => resolve();
        });
    }

    function clearImageDatabase() {
        return new Promise((resolve, reject) => {
            if (!database) {
                resolve();
                return;
            }

            const transaction = database.transaction(
                [DB_STORE, AVATAR_STORE, LOG_STORE],
                'readwrite'
            );

            transaction.objectStore(DB_STORE).clear();
            transaction.objectStore(AVATAR_STORE).clear();
            transaction.objectStore(LOG_STORE).clear();

            transaction.oncomplete = () => resolve();
            transaction.onerror = () => reject(transaction.error);
        });
    }

    // --------------------------------------------------
    // File-name / type helpers
    // --------------------------------------------------

    // Returns the extension of a file name, or '' when there is none
    // (an "extension" must contain at least one letter, so "5.52" is not one).
    function extensionOf(name) {
        const match = String(name || '').trim().match(/\.([a-z0-9]{1,5})$/i);

        return match && /[a-z]/i.test(match[1]) ? match[1] : '';
    }

    function isNonImageName(name) {
        const ext = extensionOf(name);

        return !!ext && !IMAGE_EXT_RE.test(ext);
    }

    // Parses Chat's attachment endpoint:
    //   https://chat.google.com/api/get_attachment_url?url_type=...&attachment_token=...
    // url_type FIFE_URL / THUMBNAIL_URL are image-preview endpoints and refuse
    // non-image files; the same token is used with DOWNLOAD_URL for the file.
    function parseChatAttachmentUrl(url) {
        try {
            const u = new URL(url, location.href);

            if (
                !/(^|\.)chat\.google\.com$/i.test(u.hostname) ||
                !/\/api\/get_attachment_url$/.test(u.pathname) ||
                !u.searchParams.get('attachment_token')
            ) {
                return null;
            }

            return {
                url: u,
                contentType: u.searchParams.get('content_type') || '',
                urlType: u.searchParams.get('url_type') || ''
            };
        } catch {
            return null;
        }
    }

    // Returns the download-endpoint version of a Chat attachment URL ('' if
    // the URL is not a Chat attachment URL).
    function chatDownloadUrl(url) {
        const info = parseChatAttachmentUrl(url);

        if (!info) {
            return '';
        }

        const u = new URL(info.url.href);

        u.searchParams.set('url_type', 'DOWNLOAD_URL');
        u.searchParams.delete('sz');

        return u.href;
    }

    function namesMatch(a, b) {
        const x = String(a || '').trim().toLowerCase();
        const y = String(b || '').trim().toLowerCase();

        return !!x && !!y && (x === y || x.includes(y) || y.includes(x));
    }

    function formatBytes(bytes) {
        if (!bytes || bytes < 0) {
            return '';
        }

        const units = ['B', 'KB', 'MB', 'GB'];
        let value = bytes;
        let unit = 0;

        while (value >= 1024 && unit < units.length - 1) {
            value /= 1024;
            unit++;
        }

        return (unit === 0 ? value : value.toFixed(value < 10 ? 1 : 0)) + ' ' + units[unit];
    }

    function mimeExtension(mime) {
        return {
            'application/pdf': 'pdf',
            'application/zip': 'zip',
            'application/json': 'json',
            'text/plain': 'txt',
            'text/csv': 'csv',
            'video/mp4': 'mp4',
            'video/webm': 'webm',
            'audio/mpeg': 'mp3',
            'audio/ogg': 'ogg',
            'audio/wav': 'wav'
        }[String(mime || '').toLowerCase().split(';')[0]] || '';
    }

    // --------------------------------------------------
    // Saved-attachment display helpers
    // --------------------------------------------------

    // Object URLs are kept (not revoked on load) so "Save image as" and
    // "Open image in new tab" keep working. One URL per attachment id.
    const objectUrlCache = new Map();

    function imageUrlFor(id, blob) {
        let url = objectUrlCache.get(id);

        if (!url) {
            url = URL.createObjectURL(blob);
            objectUrlCache.set(id, url);
        }

        return url;
    }

    function revokeImageUrl(id) {
        const url = objectUrlCache.get(id);

        if (url) {
            URL.revokeObjectURL(url);
            objectUrlCache.delete(id);
        }
    }

    function revokeAllImageUrls() {
        objectUrlCache.forEach(url => URL.revokeObjectURL(url));
        objectUrlCache.clear();
    }

    function imageFileName(attachment, stored) {
        const mime = (stored.mimeType || stored.blob.type || '').toLowerCase();
        const ext = {
            'image/png': 'png',
            'image/jpeg': 'jpg',
            'image/gif': 'gif',
            'image/webp': 'webp',
            'image/bmp': 'bmp',
            'image/svg+xml': 'svg',
            'image/avif': 'avif'
        }[mime] || 'png';

        const base = String(attachment.name || 'image')
            .replace(/[^a-z0-9._-]+/gi, '_')
            .replace(/\.[a-z0-9]{2,5}$/i, '')
            .slice(0, 50) || 'image';

        return base + '_' + attachment.id.slice(-6) + '.' + ext;
    }

    // Keeps the original name and extension for non-image files.
    function fileDownloadName(attachment, stored) {
        const mime = stored.mimeType || stored.blob.type || '';
        let base = String(attachment.name || '')
            .trim()
            .replace(/[\\/:*?"<>|]+/g, '_')
            .slice(0, 120);

        if (!base || base === 'Attachment') {
            base = 'attachment_' + attachment.id.slice(-6);
        }

        if (!extensionOf(base)) {
            const ext = mimeExtension(mime);

            if (ext) {
                base += '.' + ext;
            }
        }

        return base;
    }

    // Image + Download link. Works even if the page blocks the right-click menu.
    function makeSavedImage(attachment, stored) {
        const url = imageUrlFor(attachment.id, stored.blob);

        const wrap = document.createElement('div');
        wrap.className = 'gc-saved-wrap';

        const img = document.createElement('img');
        img.src = url;
        img.alt = attachment.name || 'Saved image';
        img.className = 'gc-logger-saved-thumb';
        img.addEventListener('contextmenu', event => event.stopPropagation());

        const download = document.createElement('a');
        download.className = 'gcl-link gc-saved-dl';
        download.href = url;
        download.download = imageFileName(attachment, stored);
        download.textContent = 'Download';

        wrap.append(img, download);

        return wrap;
    }

    // Any saved attachment: image, video/audio player, or a plain download link.
    function makeSavedMedia(attachment, stored) {
        const mime = (stored.mimeType || stored.blob.type || '').toLowerCase();

        if (attachment.type === 'image' || mime.startsWith('image/')) {
            return makeSavedImage(attachment, stored);
        }

        const url = imageUrlFor(attachment.id, stored.blob);

        const wrap = document.createElement('div');
        wrap.className = 'gc-saved-wrap';

        if (attachment.type === 'video' || mime.startsWith('video/')) {
            const video = document.createElement('video');
            video.className = 'gc-saved-player';
            video.controls = true;
            video.preload = 'metadata';
            video.src = url;
            wrap.appendChild(video);
        } else if (attachment.type === 'audio' || mime.startsWith('audio/')) {
            const audio = document.createElement('audio');
            audio.className = 'gc-saved-player';
            audio.controls = true;
            audio.preload = 'metadata';
            audio.src = url;
            wrap.appendChild(audio);
        }

        const download = document.createElement('a');
        download.className = 'gcl-link gc-saved-dl';
        download.href = url;
        download.download = fileDownloadName(attachment, stored);
        download.textContent =
            'Download ' + (attachment.name || 'file') +
            (stored.blob.size ? ' (' + formatBytes(stored.blob.size) + ')' : '');

        wrap.appendChild(download);

        return wrap;
    }

    // --------------------------------------------------
    // Profile pictures
    // --------------------------------------------------

    // sender name -> { url, orig, saved, attempts, lastAttemptAt }
    const avatarMap = loadAvatarMap();

    function loadAvatarMap() {
        try {
            return JSON.parse(localStorage.getItem(AVATAR_KEY) || '{}') || {};
        } catch {
            return {};
        }
    }

    function saveAvatarMap() {
        try {
            localStorage.setItem(AVATAR_KEY, JSON.stringify(avatarMap));
        } catch { /* ignore */ }
    }

    function avatarDbPut(id, blob, mimeType) {
        return new Promise((resolve, reject) => {
            const transaction = database.transaction(AVATAR_STORE, 'readwrite');

            transaction.objectStore(AVATAR_STORE).put({
                id: id,
                blob: blob,
                mimeType: mimeType,
                savedAt: new Date().toISOString()
            });

            transaction.oncomplete = () => resolve(true);
            transaction.onerror = () => reject(transaction.error);
            transaction.onabort = () => reject(transaction.error);
        });
    }

    function avatarDbGet(id) {
        return new Promise((resolve, reject) => {
            if (!database) {
                resolve(null);
                return;
            }

            const request = database
                .transaction(AVATAR_STORE, 'readonly')
                .objectStore(AVATAR_STORE)
                .get(id);

            request.onsuccess = () => resolve(request.result || null);
            request.onerror = () => reject(request.error);
        });
    }

    // Ask Google's image server for a larger version of the same photo.
    function upscaleAvatarUrl(url) {
        return url
            .replace(/=s\d+(?:-[a-z0-9-]+)?$/i, '=s96-c')
            .replace(/=w\d+-h\d+(?:-[a-z0-9-]+)?$/i, '=s96-c')
            .replace(/\/s\d+(?:-c)?\/(?=[^/]*$)/i, '/s96-c/');
    }

    // Google Chat marks profile photos with this class.
    const AVATAR_IMG_CLASS = 'hy2WD';

    function avatarCandidates(root, area) {
        const found = [];

        for (const img of root.querySelectorAll('img')) {
            if (
                isOwnNode(img) ||
                area.contains(img) ||
                img.closest(MESSAGE_SELECTOR)
            ) {
                continue;
            }

            const raw = img.currentSrc || img.src || '';

            if (!/^https?:/i.test(raw)) {
                continue;
            }

            const known = img.classList.contains(AVATAR_IMG_CLASS);

            if (!known && !/googleusercontent\.com|ggpht\.com/i.test(raw)) {
                continue;
            }

            const rect = img.getBoundingClientRect();
            const size = Math.max(rect.width, rect.height);

            // Skip tiny reaction / read-receipt icons and oversized images.
            if (size < 20 || (!known && size > 80)) {
                continue;
            }

            found.push({ rect: rect, raw: raw });
        }

        return found;
    }

    // Climbs from the message bubble until it finds a profile photo that sits
    // to its left and lines up with it vertically. Messages that continue a
    // group (no photo shown) simply find nothing and are skipped.
    function findAvatarUrl(area) {
        const areaRect = area.getBoundingClientRect();
        let node = area.parentElement;

        for (
            let depth = 0;
            node && node !== document.body && depth < 14;
            depth++, node = node.parentElement
        ) {
            if (node.getAttribute('role') === 'main') {
                break;
            }

            const matches = avatarCandidates(node, area)
                .filter(item => {
                    const center = item.rect.top + item.rect.height / 2;

                    return (
                        item.rect.left <= areaRect.left + 4 &&
                        center >= areaRect.top - 30 &&
                        center <= areaRect.bottom + 10
                    );
                })
                .sort((a, b) =>
                    Math.abs(a.rect.top - areaRect.top) -
                    Math.abs(b.rect.top - areaRect.top)
                );

            if (matches.length) {
                return matches[0].raw;
            }
        }

        return '';
    }

    // Messages where no profile photo was found are not searched again for a
    // while (the search reads page layout, which is expensive).
    const avatarMiss = new WeakMap();

    function captureAvatar(area, group, sender) {
        if (!sender || sender === 'Unknown' || avatarMap[sender]) {
            return;
        }

        const missedAt = avatarMiss.get(area);

        if (missedAt && Date.now() - missedAt < AVATAR_RETRY_MS) {
            return;
        }

        const raw = findAvatarUrl(area);

        if (!raw) {
            avatarMiss.set(area, Date.now());
            return;
        }

        avatarMap[sender] = {
            url: upscaleAvatarUrl(raw),
            orig: raw,
            saved: false,
            attempts: 0,
            lastAttemptAt: 0
        };

        saveAvatarMap();
        markNewData();
    }

    async function downloadPendingAvatars() {
        if (!database) {
            return;
        }

        let changed = false;

        for (const [sender, entry] of Object.entries(avatarMap)) {
            const now = Date.now();

            if (
                entry.saved ||
                (entry.attempts || 0) >= MAX_AUTO_ATTEMPTS ||
                (entry.lastAttemptAt && now - entry.lastAttemptAt < AUTO_RETRY_MS)
            ) {
                continue;
            }

            entry.attempts = (entry.attempts || 0) + 1;
            entry.lastAttemptAt = now;
            changed = true;

            const urls = [...new Set([entry.url, entry.orig].filter(Boolean))];

            for (const url of urls) {
                try {
                    let response;

                    try {
                        response = await fetch(url, { credentials: 'include' });
                    } catch {
                        response = await fetch(url, { credentials: 'omit' });
                    }

                    if (!response.ok) {
                        throw new Error('HTTP ' + response.status);
                    }

                    const blob = await response.blob();

                    if (!blob.size || !blob.type.startsWith('image/')) {
                        throw new Error('Not an image');
                    }

                    await avatarDbPut(sender, blob, blob.type);
                    entry.saved = true;
                    break;
                } catch (error) {
                    console.warn('[GC Logger] Could not save avatar:', sender, error);
                }
            }
        }

        if (changed) {
            saveAvatarMap();
        }
    }

    // Round avatar for the viewer: profile photo if known, letter otherwise.
    async function buildAvatarElement(sender) {
        const avatar = document.createElement('div');
        avatar.className = 'gcl-avatar';
        avatar.style.background = avatarColor(sender);
        avatar.textContent = (sender.trim()[0] || '?').toUpperCase();

        const entry = avatarMap[sender];

        if (!entry) {
            return avatar;
        }

        const cacheKey = 'avatar_' + sender;
        let src = objectUrlCache.get(cacheKey) || '';

        if (!src && entry.saved) {
            try {
                const stored = await avatarDbGet(sender);

                if (stored && stored.blob) {
                    src = imageUrlFor(cacheKey, stored.blob);
                }
            } catch { /* fall back to the remote URL */ }
        }

        src = src || entry.url || entry.orig;

        if (!src) {
            return avatar;
        }

        const img = document.createElement('img');
        img.className = 'gcl-avatar-img';
        img.alt = '';
        img.draggable = false;
        img.referrerPolicy = 'no-referrer';

        img.onload = () => {
            avatar.style.background = 'transparent';
            avatar.style.color = 'transparent';
        };

        // Broken photo: drop it and the letter circle shows instead.
        img.onerror = () => img.remove();

        img.src = src;
        avatar.appendChild(img);

        return avatar;
    }

    // --------------------------------------------------
    // Log storage (localStorage)
    // --------------------------------------------------

    // Older versions logged the thumbnail of a file card (alt = "report.pdf")
    // as an "image". Flag those as preview thumbnails and give their download
    // another chance with the improved downloader.
    function migrateAttachment(item) {
        if (!item) {
            return item;
        }

        // A Chat file whose stored URL is the image-preview endpoint: point it
        // at the real download endpoint and give it fresh download attempts.
        const info = parseChatAttachmentUrl(item.url);

        if (
            info &&
            !item.blobSaved &&
            info.urlType !== 'DOWNLOAD_URL' &&
            (item.thumbnail ||
                isNonImageName(item.name) ||
                (info.contentType && !RENDERABLE_IMAGE_TYPE_RE.test(info.contentType)))
        ) {
            const url = chatDownloadUrl(item.url);

            return {
                ...item,
                id: attachmentId(url),
                url: url,
                previewUrl: item.previewUrl || item.url,
                type: classifyAttachment(url, '', item.name || '', ''),
                thumbnail: false,
                blobSaved: false,
                attempts: 0,
                lastAttemptAt: 0,
                saveError: ''
            };
        }

        if (
            item.type === 'image' &&
            !item.thumbnail &&
            isNonImageName(item.name)
        ) {
            return {
                ...item,
                thumbnail: true,
                ...(item.blobSaved
                    ? {}
                    : { attempts: 0, lastAttemptAt: 0, saveError: '' })
            };
        }

        return item;
    }

    function normalizeLog(log) {
        const { versions, ...rest } = log;
        const edits = Array.isArray(log.edits) ? log.edits.slice() : [];

        if (Array.isArray(versions)) {
            for (const oldMessage of versions) {
                if (!edits.some(edit => edit.message === oldMessage)) {
                    edits.push({ message: oldMessage, editedAt: null });
                }
            }
        }

        return {
            ...rest,
            attachments: Array.isArray(log.attachments)
                ? log.attachments.map(migrateAttachment)
                : [],
            edits: edits,
            reactions: Array.isArray(log.reactions) ? cloneData(log.reactions) : null,
            reactionEvents: Array.isArray(log.reactionEvents)
                ? cloneData(log.reactionEvents)
                : [],
            reactionUsers: log.reactionUsers && typeof log.reactionUsers === 'object'
                ? cloneData(log.reactionUsers)
                : {},
            status:
                !log.status || log.status === 'present' ? 'saved' : log.status
        };
    }

    // The whole log is kept in memory. It is stored in IndexedDB, one record
    // per message, and only the records that changed are written (batched).
    // localStorage (about 5 MB, synchronous) is only used if IndexedDB is
    // unavailable, and to hold the old log until it has been moved.
    // Callers may modify the returned objects and then call saveLogs.

    function readLogsFromLocalStorage() {
        try {
            const logs = JSON.parse(localStorage.getItem(STORAGE_KEY) || '[]');

            return logs.map(normalizeLog);
        } catch (error) {
            console.error('[GC Logger] Could not read logs:', error);

            return [];
        }
    }

    function getLogs() {
        if (!logCache) {
            logCache = readLogsFromLocalStorage();
        }

        return logCache;
    }

    function logSig(log) {
        const json = JSON.stringify(log);

        return json.length + ':' + hashText(json);
    }

    function idbGetAllLogs() {
        return new Promise((resolve, reject) => {
            const request = database
                .transaction(LOG_STORE, 'readonly')
                .objectStore(LOG_STORE)
                .getAll();

            request.onsuccess = () => resolve(request.result || []);
            request.onerror = () => reject(request.error);
        });
    }

    function idbWriteLogs(puts, deletes) {
        return new Promise((resolve, reject) => {
            const transaction = database.transaction(LOG_STORE, 'readwrite');
            const store = transaction.objectStore(LOG_STORE);

            puts.forEach(log => store.put(log));
            deletes.forEach(id => store.delete(id));

            transaction.oncomplete = () => resolve();
            transaction.onerror = () => reject(transaction.error);
            transaction.onabort = () => reject(transaction.error);
        });
    }

    // Loads the log into memory; on first run moves the old localStorage log
    // into IndexedDB (verified before the old copy is removed).
    async function loadLogs() {
        if (!database) {
            dbLogs = false;
            logCache = readLogsFromLocalStorage();

            return;
        }

        let stored = await idbGetAllLogs();

        if (localStorage.getItem(MIGRATED_KEY) !== '1') {
            const raw = localStorage.getItem(STORAGE_KEY);
            // A corrupt old log throws here and is left untouched.
            const legacy = raw ? JSON.parse(raw).map(normalizeLog) : [];
            const have = new Set(stored.map(log => log.id));
            const missing = legacy.filter(log => !have.has(log.id));

            if (missing.length) {
                await idbWriteLogs(missing, []);
                stored = await idbGetAllLogs();
            }

            const after = new Set(stored.map(log => log.id));

            if (!legacy.every(log => after.has(log.id))) {
                throw new Error('Moving the log to IndexedDB could not be verified');
            }

            localStorage.setItem(MIGRATED_KEY, '1');
            localStorage.removeItem(STORAGE_KEY);

            if (legacy.length) {
                console.info(
                    '[GC Logger] Moved ' + legacy.length +
                    ' logged messages from localStorage to IndexedDB.'
                );
            }
        }

        stored.forEach(log => persistedSig.set(log.id, logSig(log)));
        logCache = stored.map(normalizeLog);
        dbLogs = true;

        // One full pass writes anything normalizeLog upgraded.
        queuePersist();
    }

    function queuePersist(touchedIds) {
        if (touchedIds) {
            touchedIds.forEach(id => persistIds.add(id));
        } else {
            persistFull = true;
        }

        if (!persistTimer) {
            persistTimer = setTimeout(flushLogs, PERSIST_DELAY_MS);
        }
    }

    function flushLogs() {
        clearTimeout(persistTimer);
        persistTimer = null;
        persistInFlight = persistInFlight.then(doFlush).catch(() => {});

        return persistInFlight;
    }

    async function doFlush() {
        if (!dbLogs || !database || !logCache) {
            return;
        }

        const full = persistFull;
        const ids = [...persistIds];

        persistFull = false;
        persistIds.clear();

        if (!full && !ids.length) {
            return;
        }

        const logs = logCache;
        const puts = [];
        const deletes = [];
        const sigs = new Map();

        if (full) {
            const seen = new Set();

            for (const log of logs) {
                seen.add(log.id);

                const sig = logSig(log);

                if (persistedSig.get(log.id) !== sig) {
                    puts.push(log);
                    sigs.set(log.id, sig);
                }
            }

            for (const id of persistedSig.keys()) {
                if (!seen.has(id)) {
                    deletes.push(id);
                }
            }
        } else {
            const byId = new Map(logs.map(log => [log.id, log]));

            for (const id of ids) {
                const log = byId.get(id);

                if (!log) {
                    if (persistedSig.has(id)) {
                        deletes.push(id);
                    }

                    continue;
                }

                const sig = logSig(log);

                if (persistedSig.get(id) !== sig) {
                    puts.push(log);
                    sigs.set(id, sig);
                }
            }
        }

        if (!puts.length && !deletes.length) {
            return;
        }

        try {
            await idbWriteLogs(puts, deletes);

            sigs.forEach((sig, id) => persistedSig.set(id, sig));
            deletes.forEach(id => persistedSig.delete(id));
        } catch (error) {
            console.error('[GC Logger] Could not save logs to IndexedDB:', error);

            // Everything stays in memory; try the whole log again shortly.
            persistFull = true;

            if (!persistTimer) {
                persistTimer = setTimeout(flushLogs, 5000);
            }

            if (!storageAlertShown) {
                storageAlertShown = true;
                alert(
                    'Could not save the message log to IndexedDB. ' +
                    'Browser storage may be full or blocked. The log is kept in ' +
                    'memory and will be retried; export your logs to be safe.'
                );
            }
        }
    }

    function saveLogsToLocalStorage(logs) {
        try {
            localStorage.setItem(STORAGE_KEY, JSON.stringify(logs));
            updateLauncher(logs.length);
            return true;
        } catch (error) {
            console.error('[GC Logger] Could not save logs:', error);

            if (!storageAlertShown) {
                storageAlertShown = true;
                alert(
                    'Could not save the message log. ' +
                    'Browser localStorage may be full or unavailable. ' +
                    'Export your logs and clear old chats to free space.'
                );
            }

            return false;
        }
    }

    // touchedIds (optional): ids of the logs that may have changed. Without
    // it every log is compared against what is stored.
    function saveLogs(logs, touchedIds) {
        logCache = logs;

        if (dbLogs) {
            updateLauncher(logs.length);
            queuePersist(touchedIds);

            return true;
        }

        return saveLogsToLocalStorage(logs);
    }

    // --------------------------------------------------
    // General helpers
    // --------------------------------------------------

    // Plain copy of stored data. Records read from IndexedDB are cross-origin
    // (Xray) wrappers in Firefox userscripts: new objects cannot be added to them.
    function cloneData(value) {
        return JSON.parse(JSON.stringify(value));
    }

    function hashText(value) {
        let hash = 2166136261;

        for (let i = 0; i < value.length; i++) {
            hash ^= value.charCodeAt(i);
            hash = Math.imul(hash, 16777619);
        }

        return (hash >>> 0).toString(16);
    }

    // Strips size / auth params so the same image keeps the same identity
    // even when Google re-serves it with a different thumbnail size.
    function normalizeAttachmentUrl(url) {
        try {
            const u = new URL(url, location.href);

            ['sz', 'w', 'h', 'width', 'height', 'authuser'].forEach(key =>
                u.searchParams.delete(key)
            );

            u.hash = '';
            u.pathname = u.pathname.replace(/=[whs]\d+(?:-[a-z0-9]+)*$/i, '');

            return u.href;
        } catch {
            return String(url || '');
        }
    }

    function attachmentId(url) {
        return 'attachment_' + hashText(normalizeAttachmentUrl(url));
    }

    function cleanMessage(text) {
        return String(text || '')
            .replace(/\u00a0/g, ' ')
            .replace(/\r\n?/g, '\n')
            .replace(/[ \t]+\n/g, '\n')
            .replace(/\s*\(edited\)\s*$/i, '')
            .trim();
    }

    function formatTime(value) {
        if (value === null || value === undefined || value === '') {
            return 'Unknown time';
        }

        let date;

        if (typeof value === 'number') {
            date = new Date(value);
        } else if (/^\d+$/.test(String(value))) {
            date = new Date(Number(value));
        } else {
            date = new Date(value);
        }

        return isNaN(date.getTime()) ? String(value) : date.toLocaleString();
    }

    function formatDay(value) {
        const date = new Date(value);

        if (isNaN(date.getTime())) {
            return 'Unknown date';
        }

        return date.toLocaleDateString(undefined, {
            weekday: 'short',
            year: 'numeric',
            month: 'short',
            day: 'numeric'
        });
    }

    function formatAgo(ts) {
        if (!ts) {
            return '';
        }

        const seconds = Math.max(0, Math.round((Date.now() - ts) / 1000));

        if (seconds < 60) {
            return 'just now';
        }

        const minutes = Math.floor(seconds / 60);

        if (minutes < 60) {
            return minutes + ' min ago';
        }

        const hours = Math.floor(minutes / 60);

        if (hours < 24) {
            return hours + ' h ago';
        }

        return Math.floor(hours / 24) + ' d ago';
    }

    function logTime(log) {
        return typeof log.timestamp === 'number'
            ? log.timestamp
            : (log.loggedAt || 0);
    }

    // The URL path identifies the chat; the display name can fluctuate.
    function chatKeyOf(log) {
        const path = String(log.conversationKey || '').split('|')[0];
        return path || log.conversation || 'unknown';
    }

    // --------------------------------------------------
    // Rich formatting capture
    // --------------------------------------------------

    const RICH_COLOR_RE = /^(?:rgba?\(\s*[\d.]+\s*(?:,\s*[\d.]+\s*){2,3}\)|#[0-9a-f]{3,8})$/i;
    const RICH_TAGS = new Set([
        'B', 'I', 'U', 'S', 'CODE', 'PRE', 'BLOCKQUOTE',
        'UL', 'OL', 'LI', 'DIV', 'BR', 'SPAN'
    ]);

    function escapeHtml(s) {
        return s
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;');
    }

    // Turns a message element into a small whitelisted HTML string.
    // Returns '' when the message has no formatting at all.
    function serializeRich(root) {
        if (!root) {
            return '';
        }

        const isMono = cs => /mono|consolas|courier/i.test(cs.fontFamily);

        function walk(node, parentStyle) {
            if (node.nodeType === 3) {
                const t = node.nodeValue.replace(/\u00a0/g, ' ');

                if (!t.trim() && t.includes('\n')) {
                    return '';
                }

                return escapeHtml(t);
            }

            if (node.nodeType !== 1 || isOwnNode(node)) {
                return '';
            }

            const tag = node.tagName.toUpperCase();

            if (tag === 'SCRIPT' || tag === 'STYLE') {
                return '';
            }

            if (tag === 'BR') {
                return '<br>';
            }

            if (tag === 'IMG') {
                return escapeHtml(node.getAttribute('alt') || '');
            }

            const cs = getComputedStyle(node);

            if (cs.display === 'none') {
                return '';
            }

            let inner = '';

            node.childNodes.forEach(child => {
                inner += walk(child, cs);
            });

            if (!inner) {
                return '';
            }

            const isLink = tag === 'A';

            if (
                (parseInt(cs.fontWeight, 10) || 400) >= 600 &&
                (parseInt(parentStyle.fontWeight, 10) || 400) < 600
            ) {
                inner = '<b>' + inner + '</b>';
            }

            if (cs.fontStyle === 'italic' && parentStyle.fontStyle !== 'italic') {
                inner = '<i>' + inner + '</i>';
            }

            if (!isLink && cs.textDecorationLine.includes('underline')) {
                inner = '<u>' + inner + '</u>';
            }

            if (cs.textDecorationLine.includes('line-through')) {
                inner = '<s>' + inner + '</s>';
            }

            if (
                !isLink &&
                cs.color !== parentStyle.color &&
                RICH_COLOR_RE.test(cs.color)
            ) {
                inner = '<span style="color:' + cs.color + '">' + inner + '</span>';
            }

            const isBlock = /^(block|flex|grid|list-item|table)/.test(cs.display);

            if (isMono(cs) && !isMono(parentStyle)) {
                return (tag === 'PRE' || isBlock)
                    ? '<pre>' + inner + '</pre>'
                    : '<code>' + inner + '</code>';
            }

            if (
                tag === 'BLOCKQUOTE' ||
                (parseFloat(cs.borderLeftWidth) >= 2 && cs.borderLeftStyle !== 'none')
            ) {
                return '<blockquote>' + inner + '</blockquote>';
            }

            if (tag === 'UL' || tag === 'OL') {
                const name = tag.toLowerCase();
                return '<' + name + '>' + inner + '</' + name + '>';
            }

            if (tag === 'LI' || cs.display === 'list-item') {
                return '<li>' + inner + '</li>';
            }

            if (isBlock) {
                return '<div>' + inner + '</div>';
            }

            return inner;
        }

        const rootStyle = getComputedStyle(root);
        let html = '';

        root.childNodes.forEach(child => {
            html += walk(child, rootStyle);
        });

        return /<(b|i|u|s|code|pre|blockquote|ul|ol|li|span)\b/.test(html)
            ? html
            : '';
    }

    // Rebuilds stored HTML as DOM nodes, keeping only whitelisted tags/colors.
    function renderRichHtml(html) {
        if (!html) {
            return null;
        }

        const doc = new DOMParser().parseFromString(
            '<body>' + html + '</body>',
            'text/html'
        );

        function clone(node) {
            if (node.nodeType === 3) {
                return document.createTextNode(node.nodeValue);
            }

            if (node.nodeType !== 1) {
                return null;
            }

            const tag = node.tagName.toUpperCase();
            const target = RICH_TAGS.has(tag)
                ? document.createElement(tag.toLowerCase())
                : document.createDocumentFragment();

            if (tag === 'SPAN') {
                const color = node.style.color;

                if (color && RICH_COLOR_RE.test(color)) {
                    target.style.color = color;
                }
            }

            node.childNodes.forEach(child => {
                const c = clone(child);

                if (c) {
                    target.appendChild(c);
                }
            });

            return target;
        }

        const wrap = document.createElement('div');
        wrap.className = 'gc-rich';

        doc.body.childNodes.forEach(child => {
            const c = clone(child);

            if (c) {
                wrap.appendChild(c);
            }
        });

        return wrap;
    }

    // --- Parse quoted messages to render them normally ---
    function formatMessageHTML(text, html) {
        if (!text) return document.createTextNode('');

        const quoteRegex = /(?:Quoted\s*)+Sent by\s*([^\n]+)\n([\s\S]*?)(?:End quote\s*press L to link back to original quote\s*)+([\s\S]*)/i;
        const match = text.match(quoteRegex);

        if (match) {
            const sender = match[1].trim();
            const quotedText = match[2].trim();
            const replyText = match[3].trim();

            const wrapper = document.createElement('div');

            const quoteBlock = document.createElement('div');
            quoteBlock.className = 'gc-parsed-quote';

            const quoteSender = document.createElement('div');
            quoteSender.className = 'gc-parsed-quote-sender';
            quoteSender.textContent = sender;

            const quoteContent = document.createElement('div');
            quoteContent.className = 'gc-parsed-quote-text';
            quoteContent.textContent = quotedText;

            quoteBlock.appendChild(quoteSender);
            quoteBlock.appendChild(quoteContent);
            wrapper.appendChild(quoteBlock);

            if (replyText) {
                const reply = document.createElement('div');
                reply.className = 'gc-parsed-reply';
                reply.textContent = replyText;
                wrapper.appendChild(reply);
            }

            return wrapper;
        }

        if (html) {
            const rich = renderRichHtml(html);

            if (rich) {
                return rich;
            }
        }

        return document.createTextNode(text);
    }

    function getConversation() {
        const main = document.querySelector('[role="main"]');
        const name =
            (main?.getAttribute('aria-label') || '').trim() ||
            UNKNOWN_CONVERSATION;

        return {
            name: name,
            path: location.pathname,
            key: location.pathname + '|' + name
        };
    }

    // True once the chat URL has stayed the same long enough that the DOM
    // can be trusted to show that chat (prevents mislabelling messages while
    // Google is still swapping the old chat out for the new one).
    function conversationSettled(conversation) {
        const now = Date.now();

        if (conversation.path !== lastSeenPath) {
            lastSeenPath = conversation.path;
            pathSince = now;
        }

        return now - pathSince >= CONVERSATION_SETTLE_MS;
    }

    function getSender(area, group) {
        const selector =
            '[data-sender-name], [data-name], [data-hovercard-id], [email]';

        const element =
            group?.querySelector(selector) || area.querySelector(selector);

        if (!element) {
            return 'Unknown';
        }

        return (
            element.getAttribute('data-sender-name') ||
            element.getAttribute('data-name') ||
            element.getAttribute('data-hovercard-id') ||
            element.getAttribute('email') ||
            element.innerText ||
            'Unknown'
        ).trim() || 'Unknown';
    }

    function getTimestamp(area) {
        const raw = area
            .querySelector(TIMESTAMP_SELECTOR)
            ?.getAttribute('data-absolute-timestamp');

        return raw && Number.isFinite(Number(raw)) ? Number(raw) : null;
    }

    function getMessageId(area, textElement, sender, timestamp, message, attachments) {
        if (textElement && textElement.id) {
            return location.pathname + '|' + textElement.id;
        }

        const explicitId =
            area.getAttribute('data-message-id') ||
            area.getAttribute('data-id') ||
            area.id;

        if (explicitId) {
            return location.pathname + '|' + explicitId;
        }

        if (timestamp !== null) {
            return 'message_' + hashText(
                [location.pathname, sender, timestamp].join('|')
            );
        }

        return 'message_' + hashText([
            location.pathname,
            sender,
            message,
            attachments.map(item => item.url).join(',')
        ].join('|'));
    }

    function isOwnNode(node) {
        const element =
            node && node.nodeType === 1 ? node : node && node.parentElement;

        return !!(element && element.closest && element.closest('[' + OWN_ATTR + ']'));
    }

    function isOwnMutation(record) {
        if (isOwnNode(record.target)) {
            return true;
        }

        if (record.type !== 'childList') {
            return false;
        }

        const nodes = [...record.addedNodes, ...record.removedNodes];

        return nodes.length > 0 && nodes.every(isOwnNode);
    }

    // Only mutations inside the chat pane can contain messages.
    function isRelevantMutation(record) {
        if (isOwnMutation(record)) {
            return false;
        }

        const node = record.target;
        const element =
            node && node.nodeType === 1 ? node : node && node.parentElement;

        return !!(element && element.closest && element.closest('[role="main"]'));
    }

    function registerAnnotation(className, id, element) {
        annotationIndex.set(className + '|' + id, element);
    }

    function findAnnotation(className, id) {
        const key = className + '|' + id;
        const element = annotationIndex.get(key);

        return element && element.isConnected ? element : null;
    }

    function removeAllAnnotations() {
        annotationIndex.clear();

        document
            .querySelectorAll(
                '.gc-missing-message-wrapper, .gc-logger-history, .gc-missing-message, .gc-logger-saved-images, .gc-reaction-history-host'
            )
            .forEach(element => element.remove());
    }

    // --------------------------------------------------
    // Reaction / emoji detection
    // --------------------------------------------------

    function isLikelyReactionImage(image) {
        const src = (image.currentSrc || image.src || '').toLowerCase();

        if (
            src.includes('notoemoji') ||
            src.includes('/emoji/') ||
            src.includes('twemoji') ||
            src.includes('emoji_u') ||
            /fonts\.gstatic\.com\/s\/e\//.test(src)
        ) {
            return true;
        }

        const alt = (image.alt || '').trim();
        if (alt && /\p{Extended_Pictographic}/u.test(alt) && alt.length <= 16) {
            return true;
        }

        let node = image.parentElement;
        let depth = 0;

        while (node && depth < 8) {
            const ariaLabel = (node.getAttribute('aria-label') || '').toLowerCase();
            const title = (node.getAttribute('title') || '').toLowerCase();
            const tooltip = (node.getAttribute('data-tooltip') || '').toLowerCase();

            if (
                ariaLabel.includes('reaction') ||
                title.includes('reaction') ||
                tooltip.includes('reaction')
            ) {
                return true;
            }

            node = node.parentElement;
            depth++;
        }

        return false;
    }

    // --------------------------------------------------
    // Attachment detection
    // --------------------------------------------------

    function classifyAttachment(url, mimeType, name, hint) {
        // The file name wins: a PSD / PDF / ZIP is a file even when Google
        // shows an <img> preview of it.
        const ext = extensionOf(name);

        if (ext) {
            if (IMAGE_EXT_RE.test(ext)) {
                return 'image';
            }

            if (VIDEO_EXT_RE.test(ext)) {
                return 'video';
            }

            if (AUDIO_EXT_RE.test(ext)) {
                return 'audio';
            }

            return 'file';
        }

        const details = (
            String(url || '') + ' ' +
            String(mimeType || '') + ' ' +
            String(name || '')
        ).toLowerCase();

        if (
            hint === 'image' ||
            mimeType.startsWith('image/') ||
            /\.(png|jpe?g|gif|webp|bmp|svg|avif)(?:[?#]|$)/i.test(details) ||
            /content_type=image%2f(png|jpe?g|gif|webp|bmp|svg|avif)/i.test(details)
        ) {
            return 'image';
        }

        if (
            hint === 'video' ||
            mimeType.startsWith('video/') ||
            /\.(mp4|webm|mov|m4v|ogv)(?:[?#]|$)/i.test(details)
        ) {
            return 'video';
        }

        if (
            hint === 'audio' ||
            mimeType.startsWith('audio/') ||
            /\.(mp3|wav|ogg|m4a|flac|aac)(?:[?#]|$)/i.test(details)
        ) {
            return 'audio';
        }

        return 'file';
    }

    function extractAttachments(area) {
        const attachments = [];
        const thumbs = [];
        const seen = new Set();

        function add(url, name, mimeType, hint, extra) {
            if (!url) {
                return;
            }

            try {
                url = new URL(url, location.href).href;
            } catch {
                return;
            }

            if (url.startsWith('data:') || url.startsWith('blob:')) {
                return;
            }

            const lowerUrl = url.toLowerCase();
            if (
                lowerUrl.includes('notoemoji') ||
                lowerUrl.includes('/emoji/') ||
                lowerUrl.includes('twemoji') ||
                lowerUrl.includes('emoji_u') ||
                /fonts\.gstatic\.com\/s\/e\//.test(lowerUrl)
            ) {
                return;
            }

            const normalized = normalizeAttachmentUrl(url);

            if (seen.has(normalized)) {
                return;
            }

            seen.add(normalized);

            const isThumb = !!(extra && extra.thumbnail);

            const attachment = {
                id: attachmentId(url),
                url: url,
                name: name || '',
                mimeType: mimeType || '',
                type: isThumb
                    ? 'image'
                    : classifyAttachment(url, mimeType || '', name || '', hint),
                blobSaved: false,
                saveError: '',
                attempts: 0,
                lastAttemptAt: 0
            };

            if (isThumb) {
                attachment.thumbnail = true;
            }

            if (extra && extra.previewUrl) {
                attachment.previewUrl = extra.previewUrl;
            }

            attachments.push(attachment);
        }

        for (const image of area.querySelectorAll('img')) {
            if (isLikelyReactionImage(image)) {
                continue;
            }

            const rect = image.getBoundingClientRect();
            const attrW = parseInt(image.getAttribute('width'), 10) || 0;
            const attrH = parseInt(image.getAttribute('height'), 10) || 0;
            const cssW = image.width || 0;
            const cssH = image.height || 0;

            const dims = [rect.width, rect.height, attrW, attrH, cssW, cssH]
                .filter(v => v > 0);

            if (dims.some(v => v < MIN_ATTACHMENT_SIZE)) {
                continue;
            }

            const url = image.currentSrc || image.src;

            if (!url) {
                continue;
            }

            const alt = (image.alt || '').trim();
            const chatInfo = parseChatAttachmentUrl(url);
            const isFileCard =
                isNonImageName(alt) ||
                !!(chatInfo &&
                    chatInfo.contentType &&
                    !RENDERABLE_IMAGE_TYPE_RE.test(chatInfo.contentType));

            // Preview of a file card ("report.pdf"): not an image attachment.
            if (isFileCard) {
                const download = chatDownloadUrl(url);

                if (download) {
                    // Chat file: fetch the real file through the download endpoint.
                    add(download, alt || 'Attachment', '', '', { previewUrl: url });
                } else {
                    // Not a Chat URL: keep the preview only as a fallback.
                    thumbs.push({ url: url, name: alt });
                }

                continue;
            }

            add(url, alt || 'Image', 'image/*', 'image');
        }

        for (const video of area.querySelectorAll('video')) {
            const url =
                video.currentSrc ||
                video.src ||
                video.querySelector('source')?.src;

            if (url) {
                add(url, 'Video', 'video/*', 'video');
            }
        }

        for (const audio of area.querySelectorAll('audio')) {
            const url =
                audio.currentSrc ||
                audio.src ||
                audio.querySelector('source')?.src;

            if (url) {
                add(url, 'Audio', 'audio/*', 'audio');
            }
        }

        for (const link of area.querySelectorAll('a[href]')) {
            const url = link.href;
            const name =
                link.getAttribute('download') ||
                link.innerText.trim() ||
                link.getAttribute('aria-label') ||
                '';

            // Judge by the URL only (link text such as "download" on a website
            // preview card must not turn that website into an attachment).
            const urlOnly = url.toLowerCase();
            let host = '';

            try {
                host = new URL(url, location.href).hostname;
            } catch { /* ignore */ }

            const isGoogleHost =
                /(^|\.)(google\.com|googleusercontent\.com|googleapis\.com)$/i.test(host);

            if (
                link.hasAttribute('download') ||
                (isGoogleHost &&
                    /attachment|download|content_type=|drive\.google\.com/i.test(urlOnly)) ||
                /\.(pdf|docx?|xlsx?|pptx?|zip|txt|csv|psd|png|jpe?g|gif|webp|mp4|mp3)(?:[?#]|$)/i.test(urlOnly)
            ) {
                add(chatDownloadUrl(url) || url, name || 'Attachment', '', '');
            }
        }

        for (const element of area.querySelectorAll('*')) {
            const url =
                element.getAttribute('data-download-url') ||
                element.getAttribute('data-file-url') ||
                element.getAttribute('data-url');

            const name =
                element.getAttribute('data-file-name') ||
                element.getAttribute('data-filename') ||
                '';

            const mimeType = element.getAttribute('data-mime-type') || '';

            if (url && (name || mimeType)) {
                add(url, name || 'Attachment', mimeType, '');
            }
        }

        // Fallback: keep the preview thumbnail of a file card only when the
        // real file was not found, so at least a picture of it is saved.
        const realFiles = attachments.filter(a => a.type !== 'image');

        if (realFiles.length < thumbs.length) {
            for (const thumb of thumbs) {
                if (!realFiles.some(file => namesMatch(file.name, thumb.name))) {
                    add(thumb.url, thumb.name, 'image/*', 'image', { thumbnail: true });
                }
            }
        }

        return attachments;
    }

    function mergeAttachments(log, attachments) {
        let changed = false;

        for (const attachment of attachments) {
            const normalized = normalizeAttachmentUrl(attachment.url);

            // Match by id OR by normalized URL so the same picture served at a
            // different size (or by older versions of this script) is not duplicated.
            const existing = log.attachments.find(
                item =>
                    item.id === attachment.id ||
                    normalizeAttachmentUrl(item.url) === normalized
            );

            if (!existing) {
                log.attachments.push({ ...attachment });
                changed = true;
                continue;
            }

            for (const key of ['url', 'name', 'mimeType', 'type']) {
                if (attachment[key] && existing[key] !== attachment[key]) {
                    existing[key] = attachment[key];
                    changed = true;

                    // A fresh URL gives failed downloads another chance.
                    if (key === 'url' && !existing.blobSaved) {
                        existing.attempts = 0;
                        existing.lastAttemptAt = 0;
                    }
                }
            }
        }

        // Once the real file is known, drop an unsaved preview-only entry for it.
        const realNames = attachments
            .filter(a => !a.thumbnail && a.type !== 'image')
            .map(a => a.name);

        if (realNames.length) {
            const before = log.attachments.length;

            log.attachments = log.attachments.filter(
                item =>
                    !(
                        item.thumbnail &&
                        !item.blobSaved &&
                        realNames.some(name => namesMatch(name, item.name))
                    )
            );

            if (log.attachments.length !== before) {
                changed = true;
            }
        }

        return changed;
    }

    // --------------------------------------------------
    // Attachment downloading (images, files, video, audio)
    // --------------------------------------------------

    function tooLargeError() {
        const error = new Error(
            'Larger than the ' + formatBytes(MAX_FILE_BYTES) + ' storage limit'
        );

        error.fatal = true;

        return error;
    }

    // Cross-origin download that carries your Google cookies, which plain
    // fetch() often cannot (that is what caused HTTP 403).
    function gmFetchBlob(url) {
        return new Promise((resolve, reject) => {
            if (typeof GM_xmlhttpRequest !== 'function') {
                reject(new Error('GM_xmlhttpRequest unavailable'));
                return;
            }

            GM_xmlhttpRequest({
                method: 'GET',
                url: url,
                responseType: 'blob',
                withCredentials: true,
                timeout: 120000,
                onload: response => {
                    if (response.status >= 200 && response.status < 300 && response.response) {
                        let blob = response.response;
                        const typeMatch = /content-type:\s*([^\r\n;]+)/i
                            .exec(response.responseHeaders || '');

                        if (!blob.type && typeMatch) {
                            blob = new Blob([blob], { type: typeMatch[1].trim() });
                        }

                        resolve(blob);
                    } else {
                        reject(new Error('HTTP ' + response.status + ' (GM)'));
                    }
                },
                onerror: () => reject(new Error('Network error (GM)')),
                ontimeout: () => reject(new Error('Timed out (GM)'))
            });
        });
    }

    // Tries each candidate URL with: fetch with cookies -> Tampermonkey
    // cross-origin request (-> fetch without cookies for non-Chat hosts).
    // Throws one combined error describing every failure.
    async function fetchAttachmentBlob(url) {
        const candidates = [url];
        const info = parseChatAttachmentUrl(url);

        if (info && info.url.searchParams.has('allow_caching')) {
            const stripped = new URL(info.url.href);
            stripped.searchParams.delete('allow_caching');
            candidates.push(stripped.href);
        }

        const errors = [];

        for (const candidate of candidates) {
            const isChat = !!parseChatAttachmentUrl(candidate);

            const steps = [
                async () => {
                    const response = await fetch(candidate, {
                        method: 'GET',
                        credentials: 'include'
                    });

                    if (!response.ok) {
                        throw new Error('HTTP ' + response.status);
                    }

                    if (Number(response.headers.get('content-length') || 0) > MAX_FILE_BYTES) {
                        throw tooLargeError();
                    }

                    return response.blob();
                },
                () => gmFetchBlob(candidate)
            ];

            if (!isChat) {
                steps.push(async () => {
                    const response = await fetch(candidate, {
                        method: 'GET',
                        credentials: 'omit'
                    });

                    if (!response.ok) {
                        throw new Error('HTTP ' + response.status + ' (no cookies)');
                    }

                    return response.blob();
                });
            }

            for (const step of steps) {
                try {
                    return await step();
                } catch (error) {
                    if (error.fatal) {
                        throw error;
                    }

                    // "GM_xmlhttpRequest unavailable" is noise, not a failure.
                    if (!/unavailable/.test(error.message)) {
                        errors.push(error.message || 'Download failed');
                    }
                }
            }
        }

        const detail = [...new Set(errors)].join(' / ');
        const kind = info ? ' [' + (info.urlType || '?') + ']' : '';

        throw new Error((detail || 'Download failed') + kind);
    }

    async function downloadAttachment(attachment) {
        try {
            const existing = await getStoredImage(attachment.id);

            if (existing && existing.blob && existing.blob.size > 0) {
                return { ok: true, error: '', size: existing.blob.size };
            }

            const blob = await fetchAttachmentBlob(attachment.url);

            if (!blob.size) {
                throw new Error('Downloaded file was empty');
            }

            if (blob.size > MAX_FILE_BYTES) {
                throw tooLargeError();
            }

            const mimeType =
                blob.type || attachment.mimeType || 'application/octet-stream';

            // A login / consent page is not the file (unless it really is HTML/JSON).
            if (
                (mimeType.includes('text/html') || mimeType.includes('application/json')) &&
                !/\.(html?|json)$/i.test(attachment.name || '')
            ) {
                throw new Error(
                    'Google returned ' + mimeType +
                    ' instead of the file (link expired or not authorised)'
                );
            }

            await storeImage(attachment.id, blob, mimeType);

            return { ok: true, error: '', size: blob.size };
        } catch (error) {
            console.warn('[GC Logger] Could not save attachment:', attachment.url, error);

            return { ok: false, error: error.message || 'Download failed', size: 0 };
        }
    }

    async function downloadPendingAttachments(force) {
        if (!database) {
            return false;
        }

        const logs = getLogs();
        const touched = new Set();
        let changed = false;

        for (const log of logs) {
            for (const attachment of log.attachments) {
                if (attachment.blobSaved) {
                    continue;
                }

                const now = Date.now();

                if (!force) {
                    if ((attachment.attempts || 0) >= MAX_AUTO_ATTEMPTS) {
                        continue;
                    }

                    if (
                        attachment.lastAttemptAt &&
                        now - attachment.lastAttemptAt < AUTO_RETRY_MS
                    ) {
                        continue;
                    }
                }

                attachment.attempts = (attachment.attempts || 0) + 1;
                attachment.lastAttemptAt = now;
                touched.add(log.id);

                const result = await downloadAttachment(attachment);

                attachment.blobSaved = result.ok;
                attachment.saveError = result.ok ? '' : result.error;

                if (result.ok && result.size) {
                    attachment.size = result.size;
                }

                changed = true;
            }
        }

        if (changed) {
            // Re-read so changes made by scanDom during the downloads are not lost.
            const fresh = getLogs();
            const byId = new Map(fresh.map(log => [log.id, log]));

            for (const log of logs) {
                const target = byId.get(log.id);

                if (!target) {
                    continue;
                }

                for (const attachment of log.attachments) {
                    const match = target.attachments.find(a => a.id === attachment.id);

                    if (match) {
                        match.blobSaved = attachment.blobSaved;
                        match.saveError = attachment.saveError;
                        match.attempts = attachment.attempts;
                        match.lastAttemptAt = attachment.lastAttemptAt;

                        if (attachment.size) {
                            match.size = attachment.size;
                        }
                    }
                }
            }

            saveLogs(fresh, touched);
            markNewData();
            scheduleScan();
        }

        return changed;
    }

    function retryFailedDownloads() {
        return exclusive(() => downloadPendingAttachments(true));
    }

    // --------------------------------------------------
    // Reactions (stored on each message's log record)
    // --------------------------------------------------

    function reactionHostOf(area) {
        return area.closest(REACTION_HOST_SELECTOR) ||
            area.querySelector(REACTION_HOST_SELECTOR) ||
            area;
    }

    function readReactions(area) {
        return [...reactionHostOf(area).querySelectorAll(REACTION_SELECTOR)]
            .filter(el => !isOwnNode(el))
            .map(el => ({
                emoji: String(el.dataset.id || '')
                    .replace(/^emoji\//, '')
                    .replace(/^unicode\//, ''),
                count: Number(el.dataset.count || 0),
                pressed: el.getAttribute('aria-pressed')
            }))
            .filter(r => r.emoji)
            .sort((a, b) => a.emoji.localeCompare(b.emoji));
    }

    function reactionSig(area) {
        return readReactions(area)
            .map(r => r.emoji + ':' + r.count + ':' + r.pressed)
            .join('|');
    }

    // Custom emoji have no text form, so show a placeholder.
    function emojiLabel(emoji) {
        return /^custom\//.test(emoji) ? ':custom:' : emoji;
    }

    function diffReactions(before, after) {
        const changes = [];
        const oldMap = new Map(before.map(r => [r.emoji, r]));
        const newMap = new Map(after.map(r => [r.emoji, r]));

        for (const emoji of new Set([...oldMap.keys(), ...newMap.keys()])) {
            const o = oldMap.get(emoji);
            const n = newMap.get(emoji);
            const oc = o ? o.count : 0;
            const nc = n ? n.count : 0;

            const wasMine = !!o && o.pressed === 'true';
            const isMine = !!n && n.pressed === 'true';

            if (oc !== nc) {
                const change = {
                    emoji: emoji,
                    type: nc > oc ? 'added' : 'removed',
                    amount: Math.abs(nc - oc),
                    before: oc,
                    after: nc
                };

                // Google marks your own reaction, so no popup is needed for "You".
                if (nc > oc && isMine && !wasMine) {
                    change.who = ['You'];
                } else if (nc < oc && wasMine && !isMine) {
                    change.who = ['You'];
                }

                changes.push(change);
            } else if (o && n && wasMine !== isMine) {
                changes.push({
                    emoji: emoji,
                    type: isMine ? 'you-reacted' : 'you-unreacted'
                });
            }
        }

        return changes;
    }

    function describeReactionChange(change) {
        const e = emojiLabel(change.emoji);

        const who = Array.isArray(change.who) && change.who.length
            ? ' ' + change.who.join(', ')
            : '';

        switch (change.type) {
            case 'added':
                return { cls: 'added', text: '+ ' + e + who + ' (' + change.before + ' → ' + change.after + ')' };
            case 'removed':
                return { cls: 'removed', text: '− ' + e + who + ' (' + change.before + ' → ' + change.after + ')' };
            case 'you-reacted':
                return { cls: 'you', text: 'You reacted ' + e };
            default:
                return { cls: 'you', text: 'You removed ' + e };
        }
    }

    function shortTime(ts) {
        const d = new Date(ts);
        const time = d.toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' });

        return d.toDateString() === new Date().toDateString()
            ? time
            : d.toLocaleDateString([], { month: 'short', day: 'numeric' }) + ' ' + time;
    }

    // Updates log.reactions / log.reactionEvents. Every observed change is
    // logged immediately (add -> remove gives two events). Changes seen while a
    // chat is still loading are held back. Returns { changed, wait }.
    function applyReactions(log, reactions, now) {
        const result = { changed: false, wait: 0 };

        if (!Array.isArray(log.reactionEvents)) {
            log.reactionEvents = [];
        }

        const next = JSON.stringify(reactions);

        // First sighting (new log, or an older log without reaction data):
        // this is the baseline, not a change.
        if (!Array.isArray(log.reactions)) {
            log.reactions = reactions;
            result.changed = true;

            return result;
        }

        if (JSON.stringify(log.reactions) === next) {
            return result;
        }

        // Just opened this chat: the reaction bars may still be loading.
        const sinceOpen = now - pathSince;

        if (sinceOpen < REACTION_WARMUP_MS) {
            result.wait = REACTION_WARMUP_MS - sinceOpen + 100;

            return result;
        }

        const changes = diffReactions(log.reactions, reactions);

        if (changes.length) {
            result.event = { timestamp: now, changes: changes };
            log.reactionEvents.push(result.event);

            if (log.reactionEvents.length > MAX_REACTION_EVENTS) {
                log.reactionEvents.splice(
                    0,
                    log.reactionEvents.length - MAX_REACTION_EVENTS
                );
            }

            console.log('[GC Logger] Reactions changed:', log.id, changes);
        }

        log.reactions = reactions;
        result.changed = true;

        return result;
    }

    // Compact in-page history: a small pill that opens a short list.
    // Only the latest changes show at first; "Show N more" expands the rest.
    function createReactionPanel(logId) {
        const host = document.createElement('div');
        host.className = 'gc-reaction-history-host';
        host.setAttribute(OWN_ATTR, '');
        host.dataset.logId = logId;

        const shadow = host.attachShadow({ mode: 'open' });

        shadow.innerHTML = `
            <style>
                :host {
                    display: block;
                    flex: 0 0 100%;
                    margin: 2px 0 0;
                    font: 11px/1.4 'Google Sans', Roboto, Arial, sans-serif;
                    color: #9aa0a6;
                }
                :host([data-side="right"]) { text-align: right; }
                :host([data-side="right"]) .body { margin-left: auto; text-align: left; }
                .pill {
                    display: inline-flex;
                    align-items: center;
                    gap: 4px;
                    padding: 1px 8px;
                    border: 1px solid rgba(154, 160, 166, .3);
                    border-radius: 999px;
                    background: transparent;
                    color: inherit;
                    font: inherit;
                    cursor: pointer;
                    opacity: .7;
                }
                .pill:hover { opacity: 1; border-color: #8ab4f8; color: #8ab4f8; }
                .arrow { font-size: 9px; transition: transform .15s; }
                .pill.open .arrow { transform: rotate(180deg); }
                .body {
                    display: none;
                    max-width: 340px;
                    margin: 4px 0 0;
                    padding: 1px 0 1px 8px;
                    border-left: 2px solid rgba(154, 160, 166, .35);
                }
                .body.open { display: block; }
                .ev { display: flex; gap: 8px; padding: 1px 0; }
                .t { flex: 0 0 auto; min-width: 58px; color: #80868b; white-space: nowrap; }
                .txt { min-width: 0; overflow-wrap: anywhere; }
                .added { color: #81c995; }
                .removed { color: #f28b82; }
                .you { color: #8ab4f8; }
                .more {
                    display: none;
                    margin: 2px 0 0;
                    padding: 0;
                    border: 0;
                    background: none;
                    color: #8ab4f8;
                    font: inherit;
                    cursor: pointer;
                }
                .more.show { display: block; }
                .more:hover { text-decoration: underline; }
            </style>
            <button class="pill" type="button">
                <span>◷</span><span class="label"></span><span class="arrow">▾</span>
            </button>
            <div class="body">
                <div class="list"></div>
                <button class="more" type="button"></button>
            </div>
        `;

        const pill = shadow.querySelector('.pill');
        const body = shadow.querySelector('.body');
        const more = shadow.querySelector('.more');

        pill.addEventListener('click', event => {
            event.stopPropagation();
            pill.classList.toggle('open', body.classList.toggle('open'));
        });

        more.addEventListener('click', event => {
            event.stopPropagation();
            host.dataset.expanded = host.dataset.expanded === '1' ? '0' : '1';
            renderReactionRows(host);
        });

        return host;
    }

    const REACTION_COLLAPSED_ROWS = 3;

    function renderReactionRows(host) {
        const rows = host._rows || [];
        const expanded = host.dataset.expanded === '1';
        const shown = expanded ? rows : rows.slice(0, REACTION_COLLAPSED_ROWS);
        const shadow = host.shadowRoot;
        const list = shadow.querySelector('.list');
        const more = shadow.querySelector('.more');

        list.replaceChildren();

        shown.forEach(item => {
            const row = document.createElement('div');
            row.className = 'ev';

            const t = document.createElement('span');
            t.className = 't';
            t.textContent = shortTime(item.timestamp);

            const text = document.createElement('span');
            text.className = 'txt ' + item.cls;
            text.textContent = item.text;

            row.append(t, text);
            list.appendChild(row);
        });

        const hidden = rows.length - REACTION_COLLAPSED_ROWS;

        more.classList.toggle('show', hidden > 0);
        more.textContent = expanded ? 'Show less' : 'Show ' + hidden + ' more';
    }

    // ---- Who reacted --------------------------------------------------
    // Google only shows reactor names inside a hover popup that lives inside
    // the reaction chip. It is read when it is open (you hovering, or the
    // script opening it briefly after a change).

    function readReactionUsers(chip) {
        const items = chip.querySelectorAll('[jsname="CmABtb"]');
        const users = [];

        items.forEach(item => {
            const name = (item.getAttribute('aria-label') || '').trim();
            const memberEl = item.querySelector('[data-member-id]');
            const id = (memberEl && memberEl.getAttribute('data-member-id')) || name;

            if (name || id) {
                users.push({ id: id, name: name || id });
            }
        });

        return users.length ? users : null;
    }

    function chipsByEmoji(area) {
        const map = new Map();

        reactionHostOf(area).querySelectorAll(REACTION_SELECTOR).forEach(el => {
            if (isOwnNode(el)) {
                return;
            }

            const emoji = String(el.dataset.id || '')
                .replace(/^emoji\//, '')
                .replace(/^unicode\//, '');

            if (emoji) {
                map.set(emoji, el);
            }
        });

        return map;
    }

    const probeFailedAt = new Map();
    let probeChain = Promise.resolve();

    function sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }

    function fireHover(target, enter) {
        const base = { bubbles: true, cancelable: true, relatedTarget: document.body };

        if (enter) {
            target.dispatchEvent(new MouseEvent('mouseover', base));
            target.dispatchEvent(new MouseEvent('mouseenter', { ...base, bubbles: false }));
        } else {
            target.dispatchEvent(new MouseEvent('mouseout', base));
            target.dispatchEvent(new MouseEvent('mouseleave', { ...base, bubbles: false }));
        }
    }

    // Opens the hover popup of one chip, reads the names, closes it again.
    async function probeChip(chip) {
        const existing = readReactionUsers(chip);

        if (existing) {
            return existing;
        }

        const target = chip.querySelector('[jsname="fYOGq"]') || chip;

        try {
            fireHover(target, true);

            const until = Date.now() + REACTION_POPUP_WAIT_MS;

            while (Date.now() < until) {
                await sleep(100);

                const users = readReactionUsers(chip);

                if (users) {
                    await sleep(150);

                    return readReactionUsers(chip) || users;
                }
            }

            return null;
        } finally {
            fireHover(target, false);
        }
    }

    function userNames(list) {
        return list.map(u => u.name);
    }

    function storeUsers(log, emoji, users) {
        if (!log.reactionUsers || typeof log.reactionUsers !== 'object') {
            log.reactionUsers = {};
        }

        const before = JSON.stringify(log.reactionUsers[emoji] || null);

        if (users && users.length) {
            log.reactionUsers[emoji] = users;
        } else {
            delete log.reactionUsers[emoji];
        }

        return before !== JSON.stringify(log.reactionUsers[emoji] || null);
    }

    function enqueueProbe(task) {
        probeChain = probeChain.then(task).catch(error => {
            console.warn('[GC Logger] Reactor lookup failed:', error);
        });
    }

    // After a change: read the new reactor list and work out who was added/removed.
    function probeForEvent(area, log, event) {
        if (!REACTION_PROBE) {
            return;
        }

        enqueueProbe(async () => {
            let touched = false;
            const emojis = [...new Set(event.changes.map(c => c.emoji))];

            for (const emoji of emojis) {
                const chip = chipsByEmoji(area).get(emoji);
                const count = chip ? Number(chip.dataset.count || 0) : 0;
                const previous = (log.reactionUsers || {})[emoji] || null;
                let after = null;

                if (!count) {
                    after = [];
                } else {
                    after = await probeChip(chip);
                }

                if (after === null) {
                    probeFailedAt.set(log.id + '|' + emoji, Date.now());

                    continue;
                }

                event.changes.forEach(change => {
                    if (change.emoji !== emoji) {
                        return;
                    }

                    if (
                        (change.type !== 'added' && change.type !== 'removed') ||
                        change.who
                    ) {
                        return;
                    }

                    if (previous) {
                        const beforeIds = new Set(previous.map(u => u.id));
                        const afterIds = new Set(after.map(u => u.id));
                        const who = change.type === 'added'
                            ? after.filter(u => !beforeIds.has(u.id))
                            : previous.filter(u => !afterIds.has(u.id));

                        if (who.length) {
                            change.who = userNames(who);
                        }
                    } else if (change.type === 'added' && change.before === 0 && after.length) {
                        change.who = userNames(after);
                    }
                });

                storeUsers(log, emoji, after);
                touched = true;
            }

            if (touched) {
                saveLogs(getLogs(), new Set([log.id]));
                markNewData();

                if (area.isConnected) {
                    showReactionHistory(reactionHostOf(area), log, area);
                }
            }
        });
    }

    // Reactions already on screen: read who is on them so that the NEXT change
    // can be attributed. Also keeps the stored lists fresh when you hover.
    function learnUsers(area, log, now) {
        if (!REACTION_PROBE) {
            return false;
        }

        let changed = false;

        chipsByEmoji(area).forEach((chip, emoji) => {
            const count = Number(chip.dataset.count || 0);
            const open = readReactionUsers(chip);

            if (open) {
                if (storeUsers(log, emoji, open)) {
                    changed = true;
                }

                return;
            }

            if (
                !REACTION_PROBE_BASELINE ||
                !count ||
                (log.reactionUsers || {})[emoji] ||
                (count === 1 && chip.querySelector('[aria-pressed="true"]')) ||
                now - pathSince < REACTION_WARMUP_MS + 1000
            ) {
                return;
            }

            const key = log.id + '|' + emoji;
            const failed = probeFailedAt.get(key);

            if (failed && now - failed < REACTION_PROBE_RETRY_MS) {
                return;
            }

            probeFailedAt.set(key, now);

            enqueueProbe(async () => {
                if (!chip.isConnected) {
                    return;
                }

                const users = await probeChip(chip);

                if (users) {
                    probeFailedAt.delete(key);
                    storeUsers(log, emoji, users);
                    saveLogs(getLogs(), new Set([log.id]));
                }

                await sleep(400);
            });
        });

        return changed;
    }

    // Reaction-only scan: much lighter than scanDom and not throttled to 1s,
    // so quick add -> remove sequences are both caught.
    function scheduleReactionScan(delay) {
        if (reactionTimer) {
            return;
        }

        reactionTimer = setTimeout(
            reactionScan,
            typeof delay === 'number' ? delay : REACTION_SCAN_MS
        );
    }

    function reactionScan() {
        reactionTimer = null;

        try {
            if (!conversationSettled(getConversation())) {
                scheduleReactionScan(CONVERSATION_SETTLE_MS + 100);

                return;
            }

            const now = Date.now();
            const logs = getLogs();
            const byId = new Map(logs.map(log => [log.id, log]));
            const touchedIds = new Set();
            let retry = 0;

            document.querySelectorAll(MESSAGE_SELECTOR).forEach(area => {
                const info = scanCache.get(area);

                if (!info || info.empty || info.placeholder) {
                    return;
                }

                const log = byId.get(info.id);

                if (!log) {
                    return;
                }

                const result = applyReactions(log, readReactions(area), now);

                if (result.changed) {
                    touchedIds.add(log.id);
                }

                if (result.event) {
                    probeForEvent(area, log, result.event);
                } else if (learnUsers(area, log, now)) {
                    touchedIds.add(log.id);
                }

                if (result.wait) {
                    retry = Math.max(retry, result.wait);
                }

                showReactionHistory(reactionHostOf(area), log, area);
            });

            if (touchedIds.size) {
                saveLogs(logs, touchedIds);
                markNewData();
            }

            if (retry) {
                scheduleReactionScan(retry);
            }
        } catch (error) {
            console.error('[GC Logger] Reaction scan failed:', error);
        }
    }

    // Own messages sit on the right, other people's on the left. Google's hover
    // toolbar widens the message container towards the middle, so the pill must
    // hug the same side as the bubble or it appears to jump when you hover.
    function reactionSide(area) {
        const main = area && area.closest('[role="main"]');

        if (!main) {
            return null;
        }

        const a = area.getBoundingClientRect();

        if (!a.width) {
            return null;
        }

        const m = main.getBoundingClientRect();

        return (m.right - a.right) < (a.left - m.left) ? 'right' : 'left';
    }

    function showReactionHistory(rHost, log, area) {
        const events = log.reactionEvents || [];
        let el = findAnnotation('gc-reaction-history', log.id);

        if (!events.length) {
            el?.remove();

            return;
        }

        if (!el) {
            el = createReactionPanel(log.id);
            registerAnnotation('gc-reaction-history', log.id, el);
        }

        if (el.parentElement !== rHost) {
            rHost.appendChild(el);
            delete el.dataset.side;
        }

        if (!el.dataset.side) {
            const side = reactionSide(area);

            if (side) {
                el.dataset.side = side;
            }
        }

        const sig = events.length + ':' + hashText(JSON.stringify(events[events.length - 1]));

        if (el.dataset.signature === sig) {
            return;
        }

        el.dataset.signature = sig;

        const shadow = el.shadowRoot;
        shadow.querySelector('.label').textContent = String(events.length);
        shadow.querySelector('.pill').title =
            events.length + (events.length === 1 ? ' reaction change' : ' reaction changes');

        el._rows = [];

        [...events].reverse().forEach(event => {
            event.changes.forEach(change => {
                const info = describeReactionChange(change);

                el._rows.push({
                    timestamp: event.timestamp,
                    cls: info.cls,
                    text: info.text
                });
            });
        });

        renderReactionRows(el);
    }

    // --------------------------------------------------
    // In-page annotations (previous versions / saved images / deleted)
    // --------------------------------------------------

    function makeTag(text, title) {
        const tag = document.createElement('span');
        tag.className = 'gc-tag';
        tag.textContent = '(' + text + ')';

        if (title) {
            tag.title = title;
        }

        return tag;
    }

    // Google puts each bubble in a flex row (bubble + reaction avatar). Climb
    // out of such rows so annotations sit ABOVE the bubble instead of beside it.
    function blockAnchor(element) {
        let node = element;

        for (let i = 0; i < 2; i++) {
            const parent = node.parentElement;

            if (!parent || parent === document.body) {
                break;
            }

            const style = getComputedStyle(parent);

            if (
                (style.display === 'flex' || style.display === 'inline-flex') &&
                style.flexDirection.startsWith('row')
            ) {
                node = parent;
            } else {
                break;
            }
        }

        return node;
    }

    function showPreviousVersions(area, log) {
        let history = findAnnotation('gc-logger-history', log.id);

        if (!log.edits.length) {
            history?.remove();
            return;
        }

        const signature = JSON.stringify(
            log.edits.map(edit => [edit.message, edit.html || ''])
        );
        const anchor = blockAnchor(area);

        if (!history) {
            history = document.createElement('div');
            history.className = 'gc-logger-history';
            history.setAttribute(OWN_ATTR, '');
            history.dataset.logId = log.id;
            registerAnnotation('gc-logger-history', log.id, history);
        }

        if (anchor.parentElement && history.nextElementSibling !== anchor) {
            anchor.parentElement.insertBefore(history, anchor);
        }

        if (history.dataset.signature === signature) {
            return;
        }

        history.dataset.signature = signature;
        history.replaceChildren();

        log.edits.forEach(edit => {
            const line = document.createElement('div');
            line.className = 'gc-logger-version';
            line.appendChild(formatMessageHTML(edit.message, edit.html));
            line.appendChild(makeTag(
                'edited',
                edit.editedAt ? 'Replaced ' + formatTime(edit.editedAt) : ''
            ));
            history.appendChild(line);
        });
    }

    async function showSavedImages(area, log, currentAttachments) {
        // File-card thumbnails are not shown in-page (the file card is visible).
        const imageAttachments = (log.attachments || [])
            .filter(a => a.type === 'image' && !a.thumbnail);

        const savedImages = imageAttachments.filter(a => a.blobSaved);

        if (!savedImages.length) {
            findAnnotation('gc-logger-saved-images', log.id)?.remove();
            return;
        }

        // Only show the local copy if the original image is gone from the page.
        if (
            currentAttachments &&
            currentAttachments.some(a => a.type === 'image' && !a.thumbnail)
        ) {
            findAnnotation('gc-logger-saved-images', log.id)?.remove();
            return;
        }

        const signature = JSON.stringify(
            imageAttachments.map(a => [a.id, !!a.blobSaved])
        );

        let annotation = findAnnotation('gc-logger-saved-images', log.id);

        if (annotation && annotation.dataset.signature === signature) {
            return;
        }

        if (!area.parentElement) {
            annotation?.remove();
            return;
        }

        const anchor = blockAnchor(area);
        const parentEl = anchor.parentElement;
        const historyEl = findAnnotation('gc-logger-history', log.id);
        const target = (historyEl && historyEl.parentElement === parentEl)
            ? historyEl
            : anchor;

        if (!annotation) {
            annotation = document.createElement('div');
            annotation.className = 'gc-logger-saved-images';
            annotation.setAttribute(OWN_ATTR, '');
            annotation.dataset.logId = log.id;
            registerAnnotation('gc-logger-saved-images', log.id, annotation);
        }

        annotation.dataset.signature = signature;
        annotation.replaceChildren();

        const heading = document.createElement('div');
        heading.className = 'gc-tag';
        heading.textContent = '(image saved locally)';

        const list = document.createElement('div');
        list.className = 'gc-logger-saved-image-list';

        annotation.append(heading, list);

        if (parentEl && annotation.nextElementSibling !== target) {
            parentEl.insertBefore(annotation, target);
        }

        let appended = 0;

        for (const attachment of savedImages) {
            try {
                const stored = await getStoredImage(attachment.id);

                if (!stored || !stored.blob) {
                    console.warn(
                        '[GC Logger] Saved blob missing for',
                        attachment.id,
                        '- blobSaved was true but IndexedDB has no record.'
                    );
                    continue;
                }

                if (!list.isConnected) {
                    return;
                }

                list.appendChild(makeSavedImage(attachment, stored));
                appended++;
            } catch (error) {
                console.warn('[GC Logger] Could not render saved image:', error);
            }
        }

        if (appended === 0 && list.isConnected) {
            annotation.remove();
        }
    }

    async function showMissingMarker(log, options) {
        if (findAnnotation('gc-missing-message-wrapper', log.id)) {
            return;
        }

        if (pendingMarkers.has(log.id)) {
            return;
        }

        const beforeElement = options && options.beforeElement;
        const afterElement = options && options.afterElement;

        let parent = null;
        let next = null;

        if (beforeElement && beforeElement.isConnected) {
            const row = beforeElement.parentElement;
            if (options && options.exactBefore) {
                parent = beforeElement.parentElement;
                next = beforeElement;
            } else if (row && row.parentElement && row.parentElement !== document.body) {
                parent = row.parentElement;
                next = row;
            } else {
                parent = beforeElement.parentElement;
                next = beforeElement;
            }
        } else if (afterElement && afterElement.isConnected) {
            const row = afterElement.parentElement;
            if (row && row.parentElement && row.parentElement !== document.body) {
                parent = row.parentElement;
                next = row.nextSibling;
            } else {
                parent = afterElement.parentElement;
                next = afterElement.nextSibling;
            }
        }

        if (!parent) {
            return;
        }

        pendingMarkers.add(log.id);

        try {
            const wrapper = document.createElement('div');
            wrapper.className = 'gc-missing-message-wrapper';
            wrapper.setAttribute(OWN_ATTR, '');
            wrapper.dataset.logId = log.id;

            const marker = document.createElement('div');
            marker.className = 'gc-missing-message';

            const label = (options && options.label) || 'possibly deleted';

            if (log.sender && log.sender !== 'Unknown') {
                const senderInfo = document.createElement('div');
                senderInfo.className = 'gc-del-sender';
                senderInfo.textContent = log.sender;
                marker.appendChild(senderInfo);
            }

            function addLine(text, tag, extraClass, html) {
                const line = document.createElement('div');
                line.className = 'gc-logger-version gc-del-line' + (extraClass || '');
                line.appendChild(formatMessageHTML(text, html));
                line.appendChild(makeTag(tag));
                marker.appendChild(line);
            }

            if (Array.isArray(log.edits)) {
                for (const edit of log.edits) {
                    addLine(edit.message, 'edited', ' gc-del-old', edit.html);
                }
            }

            if (log.message) {
                addLine(log.message, label, '', log.html);
            }

            if (log.attachments && log.attachments.length > 0) {
                const list = document.createElement('div');
                list.className = 'gc-logger-saved-image-list';

                let appended = 0;

                for (const attachment of log.attachments) {
                    let rendered = false;

                    if (attachment.blobSaved) {
                        try {
                            const stored = await getStoredImage(attachment.id);

                            if (stored && stored.blob) {
                                list.appendChild(makeSavedMedia(attachment, stored));
                                rendered = true;
                            }
                        } catch (e) { /* ignore */ }
                    }

                    if (!rendered && attachment.type !== 'image') {
                        const fileInfo = document.createElement('div');
                        fileInfo.textContent =
                            'Attachment: ' + (attachment.name || attachment.type);
                        list.appendChild(fileInfo);
                        rendered = true;
                    }

                    if (rendered) {
                        appended++;
                    }
                }

                if (appended > 0) {
                    marker.appendChild(list);
                }

                if (!log.message) {
                    const line = document.createElement('div');
                    line.className = 'gc-del-line';
                    line.appendChild(makeTag(label));
                    marker.appendChild(line);
                }
            }

            wrapper.appendChild(marker);

            if (parent.isConnected && !findAnnotation('gc-missing-message-wrapper', log.id)) {
                // Never leave a second copy behind (e.g. from an older script version).
                document
                    .querySelectorAll('.gc-missing-message-wrapper')
                    .forEach(el => {
                        if (el.dataset.logId === log.id) {
                            el.remove();
                        }
                    });

                parent.insertBefore(wrapper, next);
                registerAnnotation('gc-missing-message-wrapper', log.id, wrapper);
            }
        } finally {
            pendingMarkers.delete(log.id);
        }
    }

    // Places markers for flagged messages. A marker is only drawn when the
    // message sits between two visible messages, so scrolled-away history
    // never gets a marker.
    function manageMissingMarkers(logs, conversation, visibleIds, skipIds) {
        const chatLogs = logs
            .filter(log =>
                chatKeyOf(log) === conversation.path && log.timestamp != null
            )
            .sort((a, b) => a.timestamp - b.timestamp);

        chatLogs.forEach((log, idx) => {
            if (log.status !== 'possibly-missing' && log.status !== 'deleted') {
                return;
            }

            if (visibleIds.has(log.id) || (skipIds && skipIds.has(log.id))) {
                return;
            }

            if (findAnnotation('gc-missing-message-wrapper', log.id)) {
                return;
            }

            let next = null;
            let prev = null;

            for (let i = idx + 1; i < chatLogs.length; i++) {
                if (visibleIds.has(chatLogs[i].id)) {
                    next = chatLogs[i];
                    break;
                }
            }

            for (let i = idx - 1; i >= 0; i--) {
                if (visibleIds.has(chatLogs[i].id)) {
                    prev = chatLogs[i];
                    break;
                }
            }

            if (!next || !prev) {
                return;
            }

            const nextLive = liveElements.get(next.id);
            const beforeElement = nextLive?.group || nextLive?.area;

            if (beforeElement) {
                showMissingMarker(log, { beforeElement: beforeElement });
            }
        });
    }

    // --------------------------------------------------
    // Scanning
    // --------------------------------------------------

    // Finds Google's "Message deleted by ..." rows (they are not message areas).
    function findDeletedStubs() {
        const root = document.querySelector('[role="main"]') || document.body;
        const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
            acceptNode(node) {
                const text = node.nodeValue;

                return text && text.length <= 80 && STUB_RE.test(text.trim())
                    ? NodeFilter.FILTER_ACCEPT
                    : NodeFilter.FILTER_REJECT;
            }
        });

        const stubs = [];
        let node;

        while ((node = walker.nextNode())) {
            const element = node.parentElement;

            if (!element || isOwnNode(element) || element.closest(TEXT_SELECTOR)) {
                continue;
            }

            stubs.push(element);
        }

        return stubs;
    }

    // Climbs to the stub's own row in the message list (the highest ancestor
    // that contains no message areas) so a marker can be inserted before it.
    function stubAnchor(stub) {
        let node = stub;
        let depth = 0;

        while (
            node.parentElement &&
            node.parentElement !== document.body &&
            node.parentElement.getAttribute('role') !== 'main' &&
            !node.parentElement.querySelector(MESSAGE_SELECTOR) &&
            depth < 12
        ) {
            node = node.parentElement;
            depth++;
        }

        return node;
    }

    // Reads everything we log from one message element. This is the expensive
    // part (computed styles, layout reads), so scanDom only calls it when the
    // element's HTML changed, it is still loading, or every FULL_RESCAN_MS.
    function readMessage(area, sig, now) {
        const textElement = area.querySelector(TEXT_SELECTOR);

        const message = textElement
            ? cleanMessage(textElement.innerText || textElement.textContent)
            : '';

        const richHtml = textElement ? serializeRich(textElement) : '';

        const placeholder =
            DELETED_RE.test(message) ||
            (!message && DELETED_RE.test(cleanMessage(area.innerText)));

        const attachments = placeholder ? [] : extractAttachments(area);
        const group = area.closest(GROUP_SELECTOR);
        const sender = getSender(area, group);
        const timestamp = getTimestamp(area);
        const reactions = readReactions(area);

        const id = getMessageId(
            area,
            textElement,
            sender,
            timestamp,
            message,
            attachments
        );

        // Present on the page but still empty (lazy-loading text or an image).
        const empty = !message && !attachments.length && !placeholder;

        return {
            sig: sig,
            reactions: reactions,
            fullAt: now,
            message: message,
            richHtml: richHtml,
            placeholder: placeholder,
            attachments: attachments,
            group: group,
            sender: sender,
            timestamp: timestamp,
            id: id,
            empty: empty,
            volatile: empty
        };
    }

    // Returns a delay (ms) if another scan should be scheduled, else 0.
    function scanDom() {
        const conversation = getConversation();

        if (!conversationSettled(conversation)) {
            return CONVERSATION_SETTLE_MS + 100;
        }

        const now = Date.now();
        const logs = getLogs();
        const logsById = new Map(logs.map(log => [log.id, log]));
        const currentVisibleIds = new Set();
        const ordered = [];
        const presentIds = new Set();
        const stubbed = new Set();
        // Logs this scan may modify (only these are written to IndexedDB)
        const touched = new Set([...previousVisibleIds, ...missingSince.keys()]);
        const sameConversation = previousChatPath === conversation.path;
        let changed = false;
        let followUp = 0;

        if (!sameConversation) {
            missingSince.clear();
            pendingEdits.clear();
        }

        document.querySelectorAll(MESSAGE_SELECTOR).forEach(area => {
            let info = scanCache.get(area);
            const sig = hashText(area.innerHTML) + '|' + reactionSig(area);

            if (
                !info ||
                info.volatile ||
                info.sig !== sig ||
                now - info.fullAt > FULL_RESCAN_MS
            ) {
                info = readMessage(area, sig, now);
                scanCache.set(area, info);
            }

            const {
                message, richHtml, placeholder, attachments,
                group, sender, timestamp, id, reactions
            } = info;

            if (info.empty) {
                // Remember it so it is never mistaken for a removal.
                presentIds.add(id);

                return;
            }

            let log = logsById.get(id);

            // Google shows a "message deleted" stub: keep the original and flag it.
            if (placeholder) {
                if (!log) {
                    return;
                }

                currentVisibleIds.add(id);
                ordered.push({ area: area, ts: timestamp ?? log.timestamp ?? null });
                liveElements.set(id, { area: area, group: group });

                if (log.status !== 'deleted') {
                    log.status = 'deleted';
                    log.deletedAt = now;
                    changed = true;
                    console.log('[GC Logger] Message deleted:', log.message);
                }

                showMissingMarker(log, {
                    beforeElement: group || area,
                    label: 'deleted'
                });

                return;
            }

            currentVisibleIds.add(id);
            ordered.push({ area: area, ts: timestamp });
            liveElements.set(id, { area: area, group: group });

            captureAvatar(area, group, sender);

            // An open inline editor shows draft text, not the real message.
            const isBeingEdited = !!area.querySelector(
                'textarea, [contenteditable="true"]'
            );

            if (!log) {
                log = {
                    id: id,
                    conversation: conversation.name,
                    conversationKey: conversation.key,
                    sender: sender,
                    message: message,
                    html: richHtml,
                    timestamp: timestamp,
                    loggedAt: now,
                    attachments: [],
                    edits: [],
                    reactions: reactions,
                    reactionEvents: [],
                    reactionUsers: {},
                    status: 'saved',
                    url: location.href
                };

                logs.push(log);
                logsById.set(id, log);
                changed = true;

                console.log('[GC Logger] Saved message:', message || '[attachment]');
            } else {
                if (message && !isBeingEdited) {
                    const current = cleanMessage(log.message);

                    if (message === current) {
                        pendingEdits.delete(id);

                        if (log.message !== current) {
                            log.message = current;
                            changed = true;
                        }

                        // Pick up formatting (also backfills older logs).
                        if ((log.html || '') !== richHtml) {
                            log.html = richHtml;
                            changed = true;
                        }
                    } else if (
                        now - (log.loggedAt || 0) < PARTIAL_RENDER_MS &&
                        (message.startsWith(current) || current.startsWith(message))
                    ) {
                        // Google was still rendering the text; not a real edit.
                        if (message.length > current.length) {
                            log.message = message;
                            log.html = richHtml;
                            changed = true;
                        }
                    } else {
                        const pending = pendingEdits.get(id);

                        if (!pending || pending.text !== message) {
                            pendingEdits.set(id, { text: message, since: now });
                            followUp = Math.max(followUp, EDIT_STABLE_MS + 100);
                        } else if (now - pending.since < EDIT_STABLE_MS) {
                            followUp = Math.max(
                                followUp,
                                EDIT_STABLE_MS - (now - pending.since) + 100
                            );
                        } else {
                            if (
                                current &&
                                !log.edits.some(edit => edit.message === current)
                            ) {
                                log.edits.push({
                                    message: current,
                                    html: log.html || '',
                                    editedAt: new Date().toISOString()
                                });
                            }

                            console.log('[GC Logger] Edit detected:', {
                                previous: current,
                                current: message
                            });

                            log.message = message;
                            log.html = richHtml;
                            log.lastEditedDetected = now;
                            pendingEdits.delete(id);
                            changed = true;
                        }
                    }
                }

                if (log.status !== 'saved') {
                    log.status = 'saved';
                    delete log.missingDetectedAt;
                    delete log.deletedAt;
                    changed = true;
                }

                if (sender !== 'Unknown' && sender !== log.sender) {
                    log.sender = sender;
                    changed = true;
                }

                if (chatKeyOf(log) === conversation.path) {
                    const nameKnown = conversation.name !== UNKNOWN_CONVERSATION;

                    if (
                        (nameKnown || !log.conversation) &&
                        (log.conversation !== conversation.name ||
                            log.conversationKey !== conversation.key)
                    ) {
                        log.conversation = conversation.name;
                        log.conversationKey = conversation.key;
                        changed = true;
                    }
                }

                if (timestamp !== null && log.timestamp == null) {
                    log.timestamp = timestamp;
                    changed = true;
                }
            }

            if (mergeAttachments(log, attachments)) {
                changed = true;
            }

            showSavedImages(area, log, attachments).catch(error => {
                console.warn('[GC Logger] Saved-image annotation failed:', error);
            });

            showPreviousVersions(area, log);

            let reactionResult = { changed: false, wait: 0 };

            try {
                reactionResult = applyReactions(log, reactions, now);
            } catch (error) {
                console.warn('[GC Logger] Reaction logging failed:', error);
            }

            if (reactionResult.changed) {
                changed = true;
            }

            if (reactionResult.wait) {
                followUp = Math.max(followUp, reactionResult.wait);
            }

            if (reactionResult.event) {
                probeForEvent(area, log, reactionResult.event);
            }

            showReactionHistory(reactionHostOf(area), log, area);

            findAnnotation('gc-missing-message-wrapper', id)?.remove();
        });

        // ---- Explicit "Message deleted by ..." rows ----
        // Each stub in the list marks one deleted message. Pair stubs with the
        // logged messages that are no longer visible in the same gap.
        let stubs = [];

        if (
            !sameConversation ||
            missingSince.size > 0 ||
            now - lastStubScanAt >= STUB_SCAN_MS
        ) {
            lastStubScanAt = now;
            stubs = findDeletedStubs();
        }

        if (stubs.length) {
            const gaps = new Map();

            for (const stub of stubs) {
                let prevIdx = -1;

                ordered.forEach((item, i) => {
                    if (
                        item.area.compareDocumentPosition(stub) &
                        Node.DOCUMENT_POSITION_FOLLOWING
                    ) {
                        prevIdx = i;
                    }
                });

                if (!gaps.has(prevIdx)) {
                    gaps.set(prevIdx, []);
                }

                gaps.get(prevIdx).push(stub);
            }

            gaps.forEach((gapStubs, prevIdx) => {
                let lower = -Infinity;
                let upper = Infinity;

                for (let i = prevIdx; i >= 0; i--) {
                    if (ordered[i].ts != null) {
                        lower = ordered[i].ts;
                        break;
                    }
                }

                for (let i = prevIdx + 1; i < ordered.length; i++) {
                    if (ordered[i].ts != null) {
                        upper = ordered[i].ts;
                        break;
                    }
                }

                const inGap = logs
                    .filter(log =>
                        chatKeyOf(log) === conversation.path &&
                        !currentVisibleIds.has(log.id) &&
                        !presentIds.has(log.id) &&
                        log.timestamp != null &&
                        log.timestamp > lower &&
                        log.timestamp < upper
                    )
                    .sort((a, b) => a.timestamp - b.timestamp);

                const primary = inGap.filter(log =>
                    log.status !== 'saved' ||
                    previousVisibleIds.has(log.id) ||
                    missingSince.has(log.id)
                );

                let chosen = primary;

                if (chosen.length < gapStubs.length) {
                    const rest = inGap.filter(log => !primary.includes(log));

                    if (rest.length <= gapStubs.length - chosen.length) {
                        chosen = chosen
                            .concat(rest)
                            .sort((a, b) => a.timestamp - b.timestamp);
                    }
                }

                chosen.slice(0, gapStubs.length).forEach((log, i) => {
                    stubbed.add(log.id);
                    missingSince.delete(log.id);

                    if (log.status !== 'deleted') {
                        log.status = 'deleted';
                        log.deletedAt = log.deletedAt || now;
                        delete log.missingDetectedAt;
                        changed = true;

                        console.log('[GC Logger] Message deleted:', log.message || '[attachment]');
                    }

                    const anchor = stubAnchor(gapStubs[i]);
                    const existing = findAnnotation('gc-missing-message-wrapper', log.id);

                    if (existing && existing.nextElementSibling !== anchor) {
                        existing.remove();
                    }

                    showMissingMarker(log, {
                        beforeElement: anchor,
                        exactBefore: true,
                        label: 'deleted'
                    }).catch(error => {
                        console.warn('[GC Logger] Could not show deleted marker:', error);
                    });
                });
            });
        }

        // ---- Disappeared-message detection ----
        // A message only counts as removed if it vanished from the MIDDLE of
        // the visible range and stayed gone for a grace period. Messages that
        // merely scrolled out of Google's virtualised list are ignored.
        if (sameConversation && currentVisibleIds.size > 0) {
            const stamps = [];

            currentVisibleIds.forEach(id => {
                const log = logsById.get(id);

                if (log && log.timestamp != null) {
                    stamps.push(log.timestamp);
                }
            });

            const lo = stamps.length ? Math.min(...stamps) : 0;
            const hi = stamps.length ? Math.max(...stamps) : 0;

            const isShown = id =>
                currentVisibleIds.has(id) || presentIds.has(id);

            // Sorted lazily: only needed when a message actually went missing.
            let chatSortedCache = null;

            const getChatSorted = () =>
                chatSortedCache ||
                (chatSortedCache = logs
                    .filter(log =>
                        chatKeyOf(log) === conversation.path && log.timestamp != null
                    )
                    .sort((a, b) => a.timestamp - b.timestamp));

            // A real deletion leaves the logged messages on BOTH sides of it
            // still on screen. Anything else is just history that is not loaded.
            const neighboursShown = log => {
                const chatSorted = getChatSorted();
                const index = chatSorted.indexOf(log);

                if (index < 0) {
                    return false;
                }

                const skip = other =>
                    other.status !== 'saved' ||
                    (!isShown(other.id) &&
                        (previousVisibleIds.has(other.id) || missingSince.has(other.id)));

                let prev = null;
                let next = null;

                for (let i = index - 1; i >= 0; i--) {
                    if (!skip(chatSorted[i])) {
                        prev = chatSorted[i];
                        break;
                    }
                }

                for (let i = index + 1; i < chatSorted.length; i++) {
                    if (!skip(chatSorted[i])) {
                        next = chatSorted[i];
                        break;
                    }
                }

                return !!prev && !!next && isShown(prev.id) && isShown(next.id);
            };

            const candidates = new Set([
                ...previousVisibleIds,
                ...missingSince.keys()
            ]);

            candidates.forEach(id => {
                if (isShown(id)) {
                    missingSince.delete(id);
                    return;
                }

                const log = logsById.get(id);

                if (
                    !log ||
                    stamps.length < 2 ||
                    chatKeyOf(log) !== conversation.path ||
                    log.timestamp == null ||
                    log.timestamp <= lo ||
                    log.timestamp >= hi ||
                    log.status !== 'saved'
                ) {
                    missingSince.delete(id);
                    return;
                }

                if (now - lastScrollAt < SCROLL_QUIET_MS) {
                    missingSince.set(id, now);
                    followUp = Math.max(followUp, SCROLL_QUIET_MS + 100);
                    return;
                }

                if (!neighboursShown(log)) {
                    missingSince.delete(id);
                    return;
                }

                const since = missingSince.get(id) ?? now;
                missingSince.set(id, since);

                if (now - since >= MISSING_GRACE_MS) {
                    log.status = 'possibly-missing';
                    log.missingDetectedAt = now;
                    missingSince.delete(id);
                    changed = true;

                    console.log(
                        '[GC Logger] Message vanished from the middle of the chat; ' +
                        'it may have been deleted:',
                        log.message
                    );
                } else {
                    followUp = Math.max(
                        followUp,
                        MISSING_GRACE_MS - (now - since) + 150
                    );
                }
            });

            const hasFlagged = logs.some(
                log =>
                    (log.status === 'possibly-missing' || log.status === 'deleted') &&
                    chatKeyOf(log) === conversation.path
            );

            if (hasFlagged) {
                manageMissingMarkers(logs, conversation, currentVisibleIds, stubbed);
            }
        }

        if (currentVisibleIds.size > 0 || !sameConversation) {
            previousVisibleIds = currentVisibleIds;
        }

        previousChatPath = conversation.path;

        if (changed) {
            currentVisibleIds.forEach(id => touched.add(id));
            stubbed.forEach(id => touched.add(id));

            saveLogs(logs, touched);
            markNewData();
        }

        return followUp;
    }

    function scanMessages() {
        if (scanQueued) {
            return chain;
        }

        scanQueued = true;

        return exclusive(async () => {
            scanQueued = false;
            lastScanAt = Date.now();

            try {
                const started = performance.now();
                const followUp = scanDom();
                lastScanMs = performance.now() - started;

                await downloadPendingAttachments(false);
                await downloadPendingAvatars();

                if (followUp) {
                    scheduleScan(followUp);
                }
            } catch (error) {
                console.error('[GC Logger] Scan failed:', error);
            }
        });
    }

    // Throttle (not debounce): a busy page that mutates constantly can no
    // longer postpone scans forever, and scans never run more often than
    // MIN_SCAN_INTERVAL_MS. They run when the browser is idle.
    function scheduleScan(delay) {
        const wanted = Math.max(
            typeof delay === 'number' ? delay : SCAN_DELAY_MS,
            MIN_SCAN_INTERVAL_MS - (Date.now() - lastScanAt),
            0
        );
        const due = Date.now() + wanted;

        // A scan already due sooner will do the job.
        if (scanTimer && scanDue <= due) {
            return;
        }

        clearTimeout(scanTimer);
        scanDue = due;

        scanTimer = setTimeout(() => {
            scanTimer = null;
            scanDue = 0;

            const run = () => scanMessages();

            if (typeof requestIdleCallback === 'function') {
                requestIdleCallback(run, { timeout: 1500 });
            } else {
                run();
            }
        }, wanted);
    }

    // --------------------------------------------------
    // Presence logger (Active / Away / ... per person)
    // --------------------------------------------------
    // Rows are stored in their own IndexedDB database ('gchat-presence'),
    // the same one the standalone presence script used, so existing presence
    // history carries over. Everything is also summarised in memory so the
    // viewer can show current status and last-online times instantly.

    let presenceDb = null;
    let presenceReady = false;
    let presenceError = '';
    let presenceTimer = null;
    let presenceLastScan = 0;
    let presenceScans = 0;
    let presenceWrites = 0;
    let presenceMatched = 0;
    let presenceViewTimer = null;
    let presenceLive = new Set();               // ids visible on screen right now
    const presenceUsers = new Map();            // userId -> summary (see applyPresenceRow)
    const presenceLastStatus = new Map();       // userId -> last status logged this session
    const presenceLastWrite = new Map();        // userId -> time of last write
    const presenceOpen = new Set();             // history blocks the viewer has open
    const presenceNames = loadPresenceNames();  // userId -> display name

    function loadPresenceNames() {
        try {
            return JSON.parse(localStorage.getItem(P_NAMES_KEY) || '{}') || {};
        } catch {
            return {};
        }
    }

    function savePresenceNames() {
        try {
            localStorage.setItem(P_NAMES_KEY, JSON.stringify(presenceNames));
        } catch { /* ignore */ }
    }

    function presenceDisplayName(userId) {
        return presenceNames[userId] || ('User ...' + String(userId).slice(-6));
    }

    function openPresenceDatabase() {
        return new Promise((resolve, reject) => {
            if (typeof indexedDB === 'undefined') {
                reject(new Error('indexedDB is not available'));
                return;
            }

            const request = indexedDB.open(P_DB_NAME, 1);

            request.onupgradeneeded = function () {
                const db = request.result;

                if (!db.objectStoreNames.contains(P_STORE)) {
                    const store = db.createObjectStore(P_STORE, {
                        keyPath: 'id',
                        autoIncrement: true
                    });

                    store.createIndex('userId', 'userId');
                    store.createIndex('ts', 'ts');
                }
            };

            request.onblocked = function () {
                console.warn('[GC Presence] Database open is blocked by another tab.');
            };

            request.onsuccess = function () {
                const db = request.result;

                db.onversionchange = () => {
                    db.close();

                    if (presenceDb === db) {
                        presenceDb = null;
                    }
                };

                presenceDb = db;
                resolve(db);
            };

            request.onerror = function () {
                reject(request.error);
            };
        });
    }

    function presenceTx(mode, fn) {
        return new Promise((resolve, reject) => {
            if (!presenceDb) {
                resolve(null);
                return;
            }

            const transaction = presenceDb.transaction(P_STORE, mode);
            const out = fn(transaction.objectStore(P_STORE));

            transaction.oncomplete = () =>
                resolve(out && typeof out === 'object' && 'result' in out ? out.result : out);
            transaction.onerror = () => reject(transaction.error);
            transaction.onabort = () =>
                reject(transaction.error || new Error('Transaction aborted'));
        });
    }

    function presenceGetAll() {
        return presenceTx('readonly', store => store.getAll()).then(rows => rows || []);
    }

    function presenceAddRow(record) {
        return presenceTx('readwrite', store => store.add(record)).then(
            () => { presenceWrites++; },
            error => console.warn('[GC Presence] Could not save a row:', error)
        );
    }

    // Folds one stored row into the per-user summary. Rows must arrive in
    // time order (they do: ids are assigned in write order).
    function applyPresenceRow(row) {
        if (!row || !row.userId || String(row.userId)[0] === '_' || !row.status) {
            return;
        }

        let user = presenceUsers.get(row.userId);

        if (!user) {
            user = {
                userId: row.userId,
                status: '',
                since: 0,        // when the current status began
                lastObserved: 0, // last time the person was seen at all
                lastActive: 0,   // last time the person was seen Active
                rows: 0,
                changes: []      // [{ ts, status }]
            };
            presenceUsers.set(row.userId, user);
        }

        user.rows++;

        if (row.ts >= user.lastObserved) {
            if (user.status !== row.status || !user.since) {
                user.since = row.ts;
            }

            user.status = row.status;
            user.lastObserved = row.ts;
        }

        if (P_ONLINE_RE.test(row.status) && row.ts > user.lastActive) {
            user.lastActive = row.ts;
        }

        if (row.kind !== 'heartbeat') {
            const lastChange = user.changes[user.changes.length - 1];

            if (!lastChange || lastChange.status !== row.status) {
                user.changes.push({ ts: row.ts, status: row.status });
            }
        }
    }

    async function loadPresence() {
        presenceUsers.clear();

        const rows = await presenceGetAll();

        rows.sort((a, b) => (a.ts - b.ts) || ((a.id || 0) - (b.id || 0)));
        rows.forEach(applyPresenceRow);
    }

    const P_STATUS_WORDS_RE =
        /^(active|away|offline|do not disturb|busy|in a meeting|presence|online|idle)$/i;

    // Turns "Jane Doe, Active" / "Jane Doe (Away)" into "Jane Doe".
    function cleanPresenceName(raw, status) {
        const statusText = String(status || '').trim().toLowerCase();

        const parts = String(raw || '')
            .replace(/\([^)]*\)/g, ',')
            .split(/[,\n|]/)
            .map(part => part.trim())
            .filter(part =>
                part &&
                part.length < 60 &&
                !P_STATUS_WORDS_RE.test(part) &&
                part.toLowerCase() !== statusText &&
                !/^\d{15,}$/.test(part)
            );

        return parts[0] || '';
    }

    // Looks for a person's name and profile photo near their presence dot.
    // It climbs from the dot, but only while the container holds presence
    // dots for ONE person, so it can never borrow a neighbour's photo.
    function presenceIdentity(element, status, userId) {
        let name = '';
        let avatar = '';
        let node = element;

        for (let depth = 0; depth < 10 && node && node !== document.body; depth++, node = node.parentElement) {
            const ids = new Set();

            node.querySelectorAll(P_SEL).forEach(el => {
                const id = (el.getAttribute('jsdata') || '').match(/human\/(\d+)/)?.[1];

                if (id) {
                    ids.add(id);
                }
            });

            if (ids.size > 1 || (ids.size === 1 && !ids.has(userId))) {
                break;
            }

            if (!avatar) {
                for (const img of node.querySelectorAll('img')) {
                    const raw = img.currentSrc || img.src || '';

                    if (!/^https?:/i.test(raw) || isOwnNode(img)) {
                        continue;
                    }

                    const known = img.classList.contains(AVATAR_IMG_CLASS);

                    if (!known && !/googleusercontent\.com|ggpht\.com/i.test(raw)) {
                        continue;
                    }

                    const rect = img.getBoundingClientRect();
                    const size = Math.max(rect.width, rect.height);

                    if (size >= 16 && size <= 96) {
                        avatar = raw;

                        if (!name) {
                            name = cleanPresenceName(img.getAttribute('alt'), status);
                        }

                        break;
                    }
                }
            }

            if (!name) {
                const sources = [node, ...node.querySelectorAll('[data-name], [data-member-name], [aria-label], [title]')]
                    .slice(0, 40);

                for (const source of sources) {
                    if (isOwnNode(source)) {
                        continue;
                    }

                    const value =
                        source.getAttribute('data-name') ||
                        source.getAttribute('data-member-name') ||
                        source.getAttribute('aria-label') ||
                        source.getAttribute('title') ||
                        '';

                    name = cleanPresenceName(value, status);

                    if (name) {
                        break;
                    }
                }
            }

            if (name && avatar) {
                break;
            }
        }

        return { name: name, avatar: avatar };
    }

    // Message senders often carry the same numeric id (e.g. data-member-id
    // "user/human/1101...") next to their display name, which is the most
    // reliable name source when it exists.
    function harvestSenderNames() {
        let found = false;

        document
            .querySelectorAll('[data-member-id*="human/"], [data-user-id*="human/"], [jsdata*="human/"][data-name]')
            .forEach(element => {
                if (isOwnNode(element)) {
                    return;
                }

                const idSource =
                    element.getAttribute('data-member-id') ||
                    element.getAttribute('data-user-id') ||
                    element.getAttribute('jsdata') ||
                    '';
                const id = idSource.match(/human\/(\d+)/)?.[1];

                if (!id) {
                    return;
                }

                const name = cleanPresenceName(
                    element.getAttribute('data-name') ||
                    element.getAttribute('data-sender-name') ||
                    element.innerText ||
                    '',
                    ''
                );

                if (name && presenceNames[id] !== name && !presenceNames['manual:' + id]) {
                    presenceNames[id] = name;
                    found = true;
                }
            });

        return found;
    }

    // Saves a found photo under the person's name so the viewer (and the
    // avatar downloader) can use it exactly like a message sender's photo.
    function rememberPresenceAvatar(name, raw) {
        if (!name || !raw || avatarMap[name]) {
            return false;
        }

        avatarMap[name] = {
            url: upscaleAvatarUrl(raw),
            orig: raw,
            saved: false,
            attempts: 0,
            lastAttemptAt: 0
        };

        saveAvatarMap();

        return true;
    }

    // Debug helper: shows what sits around each presence dot.
    function dumpPresenceDom() {
        document.querySelectorAll(P_SEL).forEach(element => {
            const id = (element.getAttribute('jsdata') || '').match(/human\/(\d+)/)?.[1];
            const status = element.querySelector('span')?.textContent.trim() || '';
            const identity = presenceIdentity(element, status, id);

            console.log('[GC Presence] user', id, '| status:', status, '| found:', identity);

            let node = element;

            for (let i = 0; i < 6 && node && node !== document.body; i++, node = node.parentElement) {
                console.log(
                    '  level ' + i + ':',
                    node.tagName,
                    (node.outerHTML || '').replace(/\s+/g, ' ').slice(0, 400)
                );
            }
        });
    }

    function readPresence() {
        const found = new Map();   // userId -> { status, visible, el }
        let matched = 0;

        document.querySelectorAll(P_SEL).forEach(element => {
            matched++;

            if (element.dataset.isSelfUser === 'true') {
                return;
            }

            const id = (element.getAttribute('jsdata') || '').match(/human\/(\d+)/)?.[1];

            if (!id || (P_TRACK.size && !P_TRACK.has(id))) {
                return;
            }

            const status = element.querySelector('span')?.textContent.trim();

            if (!status) {
                return;
            }

            const visible = element.offsetParent !== null;
            const existing = found.get(id);

            // Prefer a visible element over a hidden duplicate.
            if (!existing || (visible && !existing.visible)) {
                found.set(id, { status: status, visible: visible, el: element });
            }
        });

        presenceMatched = matched;

        return found;
    }

    function scanPresence() {
        try {
            presenceScans++;
            presenceLastScan = Date.now();

            const current = readPresence();
            const now = presenceLastScan;
            let namesChanged = false;
            let wrote = false;

            presenceLive = new Set(current.keys());

            if (harvestSenderNames()) {
                namesChanged = true;
            }

            for (const [userId, info] of current) {
                const status = info.status;

                if (!presenceNames['manual:' + userId]) {
                    const identity = presenceIdentity(info.el, status, userId);

                    if (
                        identity.name &&
                        (!presenceNames[userId] || presenceNames[userId] !== identity.name)
                    ) {
                        presenceNames[userId] = identity.name;
                        namesChanged = true;
                    }

                    if (rememberPresenceAvatar(presenceNames[userId], identity.avatar)) {
                        namesChanged = true;
                    }
                }

                const previous = presenceLastStatus.get(userId);
                let kind = '';

                if (previous !== status) {
                    kind = previous === undefined ? 'start' : 'change';
                } else if (now - (presenceLastWrite.get(userId) || 0) > P_HEARTBEAT_MS) {
                    kind = 'heartbeat';
                }

                if (kind) {
                    const row = {
                        ts: now,
                        userId: userId,
                        status: status,
                        kind: kind,
                        hidden: document.hidden
                    };

                    presenceLastStatus.set(userId, status);
                    presenceLastWrite.set(userId, now);
                    applyPresenceRow(row);
                    presenceAddRow(row);
                    wrote = true;

                    if (kind !== 'heartbeat') {
                        console.log(
                            '[GC Presence]', kind.toUpperCase(), userId + ':',
                            (previous !== undefined ? '"' + previous + '" -> ' : '') +
                            '"' + status + '"'
                        );
                    }
                } else {
                    // Unchanged: keep the in-memory "last seen" times accurate
                    // for the viewer without writing a row.
                    const user = presenceUsers.get(userId);

                    if (user) {
                        user.lastObserved = now;

                        if (P_ONLINE_RE.test(status)) {
                            user.lastActive = now;
                        }
                    }
                }
            }

            if (namesChanged) {
                savePresenceNames();
            }

            if (wrote || namesChanged) {
                schedulePresenceView();
            }
        } catch (error) {
            console.error('[GC Presence] Scan failed:', error);
        }
    }

    // Throttled: busy pages mutate constantly, so scans are spaced out.
    function schedulePresenceScan() {
        if (presenceTimer) {
            return;
        }

        const wait = Math.max(400, P_MIN_SCAN_MS - (Date.now() - presenceLastScan));

        presenceTimer = setTimeout(() => {
            presenceTimer = null;
            scanPresence();
        }, wait);
    }

    function schedulePresenceView() {
        if (ui.tab !== 'presence' || !document.getElementById('gchat-logger-panel')) {
            return;
        }

        if (presenceViewTimer) {
            return;
        }

        presenceViewTimer = setTimeout(() => {
            presenceViewTimer = null;
            updateViewer();
        }, 400);
    }

    function presenceSummaryRows() {
        return [...presenceUsers.values()].map(user => ({
            userId: user.userId,
            name: presenceNames[user.userId] || '',
            currentStatus: user.status,
            statusSince: user.since ? new Date(user.since).toLocaleString() : '',
            lastObserved: user.lastObserved ? new Date(user.lastObserved).toLocaleString() : '',
            lastActive: user.lastActive
                ? new Date(user.lastActive).toLocaleString()
                : 'never seen active',
            rows: user.rows
        }));
    }

    async function exportPresence() {
        const rows = await presenceGetAll();

        const output = {
            exportedAt: new Date().toISOString(),
            names: presenceNames,
            users: presenceSummaryRows(),
            events: rows
        };

        const blob = new Blob(
            [JSON.stringify(output, null, 2)],
            { type: 'application/json' }
        );

        const url = URL.createObjectURL(blob);
        const link = document.createElement('a');

        link.href = url;
        link.download = 'google-chat-presence-' + Date.now() + '.json';
        link.click();

        setTimeout(() => URL.revokeObjectURL(url), 1000);
    }

    async function clearPresence() {
        if (!confirm(
            'Delete ALL logged presence rows? (Chat message logs are not affected.) ' +
            'This cannot be undone.'
        )) {
            return;
        }

        try {
            await presenceTx('readwrite', store => store.clear());
        } catch (error) {
            console.error('[GC Presence] Could not clear:', error);
        }

        presenceUsers.clear();
        presenceLastStatus.clear();
        presenceLastWrite.clear();
        presenceOpen.clear();
        scanPresence();
    }

    async function initPresence() {
        try {
            await openPresenceDatabase();
            await loadPresence();

            presenceReady = true;

            if (presenceDb) {
                presenceAddRow({
                    ts: Date.now(),
                    userId: '_script',
                    status: '',
                    kind: 'session-start'
                });
            }

            console.info(
                '[GC Presence] Ready (' + presenceUsers.size + ' people with history).'
            );
        } catch (error) {
            presenceError = (error && error.message) || String(error);
            console.error('[GC Presence] Could not start:', error);
        }

        scanPresence();
        setInterval(scanPresence, P_SCAN_INTERVAL_MS);
    }

    // ---- presence tab (viewer) -----------------------

    // active | idle | dnd | offline
    function presenceKind(status) {
        const text = String(status || '').toLowerCase();

        if (/do not disturb|dnd|busy|in a meeting|presenting/.test(text)) {
            return 'dnd';
        }

        if (P_ONLINE_RE.test(text) || /^online\b/.test(text)) {
            return 'active';
        }

        if (/away|idle|inactive|be right back|brb/.test(text)) {
            return 'idle';
        }

        return 'offline';
    }

    function presenceStatusClass(status, live) {
        return 'gcl-pst-' + presenceKind(status) + (live ? '' : ' gcl-stale');
    }

    const PRESENCE_ICONS = {
        // filled circle
        active:
            '<svg viewBox="0 0 16 16" width="14" height="14"><circle cx="8" cy="8" r="6" fill="currentColor"/></svg>',
        // clock
        idle:
            '<svg viewBox="0 0 16 16" width="14" height="14" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round">' +
            '<circle cx="8" cy="8" r="6.2"/><path d="M8 4.5V8l2.4 1.6"/></svg>',
        // do not disturb: filled circle with a bar
        dnd:
            '<svg viewBox="0 0 16 16" width="14" height="14"><circle cx="8" cy="8" r="6.5" fill="currentColor"/>' +
            '<rect x="4.5" y="7" width="7" height="2" rx="1" fill="#232528"/></svg>',
        // hollow circle
        offline:
            '<svg viewBox="0 0 16 16" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2">' +
            '<circle cx="8" cy="8" r="5.5"/></svg>'
    };

    function makePresenceIcon(status, live) {
        const kind = presenceKind(status);
        const icon = document.createElement('span');

        icon.className = 'gcl-picon gcl-pst-' + kind + (live ? '' : ' gcl-stale');
        icon.innerHTML = PRESENCE_ICONS[kind];
        icon.title =
            {
                active: 'Active',
                idle: 'Away / idle',
                dnd: 'Do not disturb',
                offline: 'Offline / unknown'
            }[kind] +
            (live ? ' - visible on screen now' : ' - last known, not on screen');

        return icon;
    }

    function presenceLastOnlineText(user, live) {
        if (P_ONLINE_RE.test(user.status) && live) {
            return 'Online now';
        }

        if (!user.lastActive) {
            return 'Never seen active';
        }

        return formatTime(user.lastActive) + ' (' + formatAgo(user.lastActive) + ')';
    }

    function presenceStatusText() {
        const total = presenceUsers.size;
        let activeNow = 0;

        presenceUsers.forEach(user => {
            if (presenceLive.has(user.userId) && P_ONLINE_RE.test(user.status)) {
                activeNow++;
            }
        });

        if (presenceError) {
            return 'Presence logger error: ' + presenceError;
        }

        return (
            total + ' people logged | ' + presenceLive.size + ' visible on screen | ' +
            activeNow + ' active now' +
            (presenceLastScan ? ' | last scan ' + formatAgo(presenceLastScan) : '') +
            ' | ' + presenceWrites + ' rows written this session'
        );
    }

    async function buildPresenceRow(user) {
        const live = presenceLive.has(user.userId);
        const name = presenceDisplayName(user.userId);

        const entry = document.createElement('div');
        entry.className = 'gcl-entry gcl-prow';

        const avatar = await buildAvatarElement(name);

        const content = document.createElement('div');
        content.className = 'gcl-content';

        const top = document.createElement('div');
        top.className = 'gcl-meta';

        const dot = makePresenceIcon(user.status, live);

        const nameEl = document.createElement('span');
        nameEl.className = 'gcl-sender';
        nameEl.textContent = name;

        const rename = document.createElement('button');
        rename.className = 'gcl-chip';
        rename.textContent = 'Rename';
        rename.title = 'Set a display name for this person';
        rename.onclick = () => {
            const value = prompt(
                'Display name for user ' + user.userId + ' (leave empty to reset):',
                presenceNames[user.userId] || ''
            );

            if (value === null) {
                return;
            }

            if (value.trim()) {
                presenceNames[user.userId] = value.trim();
                presenceNames['manual:' + user.userId] = 1;
            } else {
                delete presenceNames[user.userId];
                delete presenceNames['manual:' + user.userId];
            }

            savePresenceNames();
            updateViewer();
        };

        const badge = document.createElement('span');
        badge.className = 'gcl-badge ' + presenceStatusClass(user.status, live);
        badge.textContent = user.status || 'Unknown';

        const idEl = document.createElement('span');
        idEl.className = 'gcl-time';
        idEl.textContent = user.userId;

        top.append(dot, nameEl, badge, rename, idEl);
        content.appendChild(top);

        const grid = document.createElement('div');
        grid.className = 'gcl-pgrid';

        function addInfo(label, value) {
            const l = document.createElement('span');
            l.className = 'gcl-plabel';
            l.textContent = label;

            const v = document.createElement('span');
            v.textContent = value;

            grid.append(l, v);
        }

        addInfo(
            'Status',
            (user.status || 'Unknown') +
            (user.since ? ' since ' + formatTime(user.since) + ' (' + formatAgo(user.since) + ')' : '')
        );
        addInfo('Last online', presenceLastOnlineText(user, live));
        addInfo(
            'Last seen',
            user.lastObserved
                ? formatTime(user.lastObserved) + ' (' + formatAgo(user.lastObserved) + ')'
                : 'never'
        );
        addInfo('Records', user.rows + ' (' + user.changes.length + ' status changes)');

        content.appendChild(grid);

        if (user.changes.length) {
            const details = document.createElement('details');
            details.className = 'gcl-edit-block';
            details.open = presenceOpen.has(user.userId);

            details.addEventListener('toggle', () => {
                if (details.open) {
                    presenceOpen.add(user.userId);
                } else {
                    presenceOpen.delete(user.userId);
                }
            });

            const summary = document.createElement('summary');
            summary.textContent =
                'Status history (' + user.changes.length + ' changes' +
                (user.changes.length > 40 ? ', showing latest 40' : '') + ')';
            details.appendChild(summary);

            user.changes.slice(-40).reverse().forEach(change => {
                const line = document.createElement('div');
                line.className = 'gcl-text gcl-hline';

                const icon = makePresenceIcon(change.status, true);
                icon.title = change.status;

                const label = document.createElement('span');
                label.textContent = formatTime(change.ts) + ' - ' + change.status;

                line.append(icon, label);
                details.appendChild(line);
            });

            content.appendChild(details);
        }

        entry.append(avatar, content);

        return entry;
    }

    async function renderPresence(panel) {
        const list = panel.querySelector('#gcl-pres-list');
        const query = panel.querySelector('#gcl-pres-search').value.trim().toLowerCase();
        const token = ++renderToken;

        let users = [...presenceUsers.values()];

        if (ui.pfilter === 'live') {
            users = users.filter(user => presenceLive.has(user.userId));
        } else if (ui.pfilter === 'active') {
            users = users.filter(
                user => presenceLive.has(user.userId) && P_ONLINE_RE.test(user.status)
            );
        } else if (ui.pfilter === 'notactive') {
            users = users.filter(
                user => !(presenceLive.has(user.userId) && P_ONLINE_RE.test(user.status))
            );
        }

        if (query) {
            users = users.filter(user =>
                [presenceDisplayName(user.userId), user.userId, user.status]
                    .join('\n')
                    .toLowerCase()
                    .includes(query)
            );
        }

        const nowActive = user =>
            presenceLive.has(user.userId) && P_ONLINE_RE.test(user.status) ? 1 : 0;

        if (ui.psort === 'name') {
            users.sort((a, b) =>
                presenceDisplayName(a.userId).localeCompare(presenceDisplayName(b.userId))
            );
        } else if (ui.psort === 'lastonline') {
            users.sort((a, b) =>
                (nowActive(b) - nowActive(a)) || (b.lastActive - a.lastActive)
            );
        } else {
            users.sort((a, b) =>
                (nowActive(b) - nowActive(a)) || (b.lastObserved - a.lastObserved)
            );
        }

        updateViewerStatus();

        if (!users.length) {
            list.className = 'gcl-entries gcl-empty';
            list.textContent = presenceUsers.size
                ? 'No people match the current filters.'
                : 'No presence has been logged yet. Open a chat or the people list ' +
                  'so that presence dots are on screen.';
            return;
        }

        list.className = 'gcl-entries';

        const built = [];

        for (const user of users) {
            built.push(await buildPresenceRow(user));

            if (token !== renderToken) {
                return;
            }
        }

        // Keep the scroll position when the list refreshes by itself.
        const scrollTop = list.scrollTop;

        list.replaceChildren(...built);
        list.scrollTop = scrollTop;
    }

    // --------------------------------------------------
    // Styles
    // --------------------------------------------------

    function createStyles() {
        if (document.getElementById('gchat-logger-styles')) {
            return;
        }

        const style = document.createElement('style');
        style.id = 'gchat-logger-styles';
        style.setAttribute(OWN_ATTR, '');

        style.textContent = `
            /* ---------- Launcher ---------- */
            #gchat-logger-launcher {
                position: fixed;
                right: 18px;
                bottom: 18px;
                z-index: 999999;
                display: flex;
                align-items: center;
                gap: 8px;
                padding: 9px 14px;
                border: 1px solid #3c4043;
                border-radius: 999px;
                background: #202124;
                color: #e8eaed;
                cursor: pointer;
                font: 500 13px 'Google Sans', Roboto, Arial, sans-serif;
                box-shadow: 0 4px 14px #0006;
                opacity: .88;
                transition: opacity .15s, transform .15s;
            }

            #gchat-logger-launcher:hover {
                opacity: 1;
                transform: translateY(-1px);
            }

            #gchat-logger-launcher .gcl-count {
                min-width: 20px;
                padding: 1px 7px;
                border-radius: 999px;
                background: #8ab4f8;
                color: #202124;
                font-size: 11px;
                font-weight: 700;
                text-align: center;
            }

            /* ---------- Viewer shell ---------- */
            #gchat-logger-panel {
                position: fixed;
                inset: 0;
                z-index: 1000000;
                display: flex;
                align-items: center;
                justify-content: center;
                background: rgba(0, 0, 0, .55);
                font: 14px/1.45 'Google Sans', Roboto, Arial, sans-serif;
                color: #e8eaed;
            }

            #gchat-logger-panel * {
                box-sizing: border-box;
            }

            #gchat-logger-panel [hidden] {
                display: none !important;
            }

            .gcl-window {
                display: flex;
                flex-direction: column;
                width: min(1280px, 96vw);
                height: 92vh;
                overflow: hidden;
                border: 1px solid #3c4043;
                border-radius: 14px;
                background: #1b1c1f;
                box-shadow: 0 12px 48px #000a;
            }

            .gcl-header {
                display: flex;
                flex-wrap: wrap;
                align-items: center;
                gap: 10px 14px;
                padding: 12px 16px;
                border-bottom: 1px solid #333639;
                background: #202124;
            }

            .gcl-title {
                margin: 0;
                font-size: 17px;
                font-weight: 600;
            }

            .gcl-tabs {
                display: flex;
                gap: 4px;
                padding: 3px;
                border-radius: 10px;
                background: #2b2d31;
            }

            .gcl-tab {
                padding: 5px 14px;
                border: 0;
                border-radius: 8px;
                background: transparent;
                color: #bdc1c6;
                cursor: pointer;
                font: inherit;
                font-size: 13px;
                font-weight: 600;
            }

            .gcl-tab:hover {
                color: #e8eaed;
            }

            .gcl-tab.gcl-tab-active {
                background: #8ab4f8;
                color: #202124;
            }

            .gcl-status {
                flex: 1;
                min-width: 160px;
                color: #9aa0a6;
                font-size: 12px;
            }

            .gcl-status.gcl-new {
                color: #f9ab00;
            }

            .gcl-actions {
                display: flex;
                flex-wrap: wrap;
                align-items: center;
                gap: 6px;
            }

            .gcl-btn {
                padding: 6px 11px;
                border: 1px solid #4a4d51;
                border-radius: 8px;
                background: #2b2d31;
                color: #e8eaed;
                cursor: pointer;
                font: inherit;
                font-size: 13px;
            }

            .gcl-btn:hover {
                background: #35383d;
            }

            .gcl-btn.gcl-primary {
                border-color: #8ab4f8;
                background: #8ab4f8;
                color: #202124;
                font-weight: 600;
            }

            .gcl-btn.gcl-primary.gcl-pulse {
                animation: gcl-pulse 1.4s ease-in-out infinite;
            }

            .gcl-btn.gcl-danger {
                border-color: #6b3b38;
                color: #f28b82;
            }

            .gcl-btn.gcl-danger:hover {
                background: #3a2220;
            }

            .gcl-check {
                display: flex;
                align-items: center;
                gap: 5px;
                color: #bdc1c6;
                font-size: 12px;
                cursor: pointer;
            }

            @keyframes gcl-pulse {
                0%, 100% { box-shadow: 0 0 0 0 rgba(138, 180, 248, .55); }
                50% { box-shadow: 0 0 0 6px rgba(138, 180, 248, 0); }
            }

            /* ---------- Body ---------- */
            .gcl-body {
                display: flex;
                flex: 1;
                min-height: 0;
            }

            .gcl-sidebar {
                display: flex;
                flex-direction: column;
                width: 280px;
                flex-shrink: 0;
                border-right: 1px solid #333639;
                background: #1e1f22;
            }

            .gcl-sidebar-head {
                padding: 10px;
                border-bottom: 1px solid #2c2e31;
            }

            .gcl-chatlist {
                flex: 1;
                overflow-y: auto;
                padding: 6px;
            }

            .gcl-chat {
                display: block;
                width: 100%;
                margin: 2px 0;
                padding: 8px 10px;
                border: 0;
                border-radius: 8px;
                background: transparent;
                color: inherit;
                cursor: pointer;
                font: inherit;
                text-align: left;
            }

            .gcl-chat:hover {
                background: #2a2c30;
            }

            .gcl-chat.gcl-active {
                background: #2f3b52;
            }

            .gcl-chat-name {
                overflow: hidden;
                font-weight: 600;
                text-overflow: ellipsis;
                white-space: nowrap;
            }

            .gcl-chat-meta {
                display: flex;
                justify-content: space-between;
                gap: 8px;
                color: #9aa0a6;
                font-size: 11px;
            }

            .gcl-chat-flag {
                color: #f28b82;
            }

            .gcl-main {
                display: flex;
                flex: 1;
                flex-direction: column;
                min-width: 0;
            }

            .gcl-toolbar {
                display: flex;
                flex-wrap: wrap;
                align-items: center;
                gap: 8px;
                padding: 10px 14px;
                border-bottom: 1px solid #2c2e31;
            }

            .gcl-input,
            .gcl-select {
                padding: 7px 10px;
                border: 1px solid #4a4d51;
                border-radius: 8px;
                background: #2b2d31;
                color: #e8eaed;
                font: inherit;
                font-size: 13px;
            }

            .gcl-input {
                width: 100%;
            }

            .gcl-toolbar .gcl-input {
                flex: 1;
                min-width: 200px;
                width: auto;
            }

            .gcl-input:focus,
            .gcl-select:focus {
                outline: 2px solid #8ab4f8;
                outline-offset: -1px;
            }

            .gcl-entries {
                flex: 1;
                overflow-y: auto;
                padding: 8px 14px 24px;
            }

            .gcl-empty {
                padding: 40px 10px;
                color: #9aa0a6;
                text-align: center;
            }

            .gcl-day,
            .gcl-chat-heading {
                position: sticky;
                top: -8px;
                z-index: 2;
                margin: 14px 0 6px;
                padding: 4px 0;
                background: #1b1c1f;
                color: #9aa0a6;
                font-size: 12px;
                font-weight: 600;
                letter-spacing: .03em;
                text-transform: uppercase;
            }

            .gcl-chat-heading {
                color: #8ab4f8;
                font-size: 13px;
            }

            /* ---------- Message cards ---------- */
            .gcl-entry {
                display: flex;
                gap: 11px;
                margin: 8px 0;
                padding: 11px 12px;
                border: 1px solid #2f3235;
                border-radius: 10px;
                background: #232528;
            }

            .gcl-entry.gcl-flagged {
                border-color: #6b3b38;
                background: #2a2322;
            }

            .gcl-avatar {
                position: relative;
                display: flex;
                flex-shrink: 0;
                align-items: center;
                justify-content: center;
                width: 34px;
                height: 34px;
                overflow: hidden;
                border-radius: 50%;
                color: #fff;
                font-size: 14px;
                font-weight: 700;
            }

            .gcl-avatar-img {
                position: absolute;
                inset: 0;
                width: 100%;
                height: 100%;
                border-radius: 50%;
                object-fit: cover;
            }

            .gcl-content {
                flex: 1;
                min-width: 0;
                overflow-wrap: anywhere;
            }

            .gcl-meta {
                display: flex;
                flex-wrap: wrap;
                align-items: center;
                gap: 4px 8px;
                margin-bottom: 3px;
            }

            .gcl-sender {
                font-weight: 600;
            }

            .gcl-time {
                color: #9aa0a6;
                font-size: 12px;
            }

            .gcl-chip,
            .gcl-badge {
                padding: 1px 8px;
                border-radius: 999px;
                font-size: 11px;
            }

            .gcl-chip {
                border: 1px solid #3c4043;
                background: transparent;
                color: #9aa0a6;
                cursor: pointer;
                font-family: inherit;
            }

            .gcl-chip:hover {
                border-color: #8ab4f8;
                color: #8ab4f8;
            }

            .gcl-badge.gcl-edited {
                background: rgba(249, 171, 0, .18);
                color: #f9ab00;
            }

            .gcl-badge.gcl-deleted {
                background: rgba(242, 139, 130, .18);
                color: #f28b82;
            }

            .gcl-badge.gcl-react {
                background: rgba(129, 201, 149, .16);
                color: #81c995;
            }

            .gcl-react-block {
                margin-top: 6px;
                font-size: 12px;
            }

            .gcl-react-chips {
                display: flex;
                flex-wrap: wrap;
                gap: 4px;
            }

            .gcl-react-chip {
                padding: 0 7px;
                border: 1px solid #3c4043;
                border-radius: 999px;
                color: #bdc1c6;
                line-height: 18px;
            }

            .gcl-react-chip.gcl-mine {
                border-color: #8ab4f8;
                color: #8ab4f8;
            }

            .gcl-react-history {
                margin-top: 4px;
                color: #9aa0a6;
            }

            .gcl-react-history summary {
                cursor: pointer;
                width: fit-content;
            }

            .gcl-react-row {
                display: flex;
                gap: 10px;
                padding: 1px 0 1px 10px;
                border-left: 2px solid #3c4043;
                white-space: nowrap;
            }

            .gcl-react-time { min-width: 130px; color: #80868b; }
            .gcl-react-added { color: #81c995; }
            .gcl-react-removed { color: #f28b82; }
            .gcl-react-you { color: #8ab4f8; }

            .gcl-badge.gcl-attach {
                background: rgba(138, 180, 248, .16);
                color: #8ab4f8;
            }

            .gcl-text {
                margin: 2px 0;
                white-space: pre-wrap;
            }

            .gcl-edit-block {
                margin-top: 6px;
                color: #bdc1c6;
                font-size: 13px;
            }

            .gcl-edit-block summary {
                cursor: pointer;
                color: #f9ab00;
            }

            .gcl-edit-block .gcl-text {
                margin: 4px 0 4px 10px;
                padding-left: 10px;
                border-left: 2px solid #5f4a14;
            }

            .gcl-attachment {
                margin-top: 8px;
                padding: 8px 10px;
                border: 1px solid #3a3d41;
                border-radius: 8px;
                background: #1f2023;
                font-size: 13px;
            }

            .gcl-attachment img,
            .gcl-attachment video {
                display: block;
                max-width: min(100%, 560px);
                max-height: 400px;
                margin-top: 8px;
                border-radius: 6px;
                object-fit: contain;
            }

            .gcl-attachment audio {
                display: block;
                max-width: 100%;
                margin-top: 8px;
            }

            .gcl-ok { color: #81c995; }
            .gcl-err { color: #f28b82; }

            .gcl-link {
                display: inline-block;
                margin-top: 6px;
                color: #8ab4f8;
                font-size: 12px;
            }

            .gcl-more {
                display: block;
                margin: 16px auto;
            }

            /* ---------- Presence tab ---------- */
            .gcl-pres-note {
                padding: 8px 14px;
                border-bottom: 1px solid #2c2e31;
                color: #9aa0a6;
                font-size: 12px;
            }

            .gcl-picon {
                display: inline-flex;
                align-items: center;
                justify-content: center;
                width: 16px;
                height: 16px;
            }

            .gcl-picon svg { display: block; }

            .gcl-picon.gcl-pst-active { color: #34a853; }
            .gcl-picon.gcl-pst-idle { color: #f9ab00; }
            .gcl-picon.gcl-pst-dnd { color: #ea4335; }
            .gcl-picon.gcl-pst-offline { color: #9aa0a6; }

            .gcl-stale { opacity: .55; }

            .gcl-hline {
                display: flex;
                align-items: center;
                gap: 7px;
            }

            .gcl-badge.gcl-pst-active { background: rgba(52, 168, 83, .2); color: #81c995; }
            .gcl-badge.gcl-pst-idle { background: rgba(249, 171, 0, .18); color: #f9ab00; }
            .gcl-badge.gcl-pst-dnd { background: rgba(234, 67, 53, .2); color: #f28b82; }
            .gcl-badge.gcl-pst-offline { background: rgba(154, 160, 166, .15); color: #9aa0a6; }

            .gcl-pgrid {
                display: grid;
                grid-template-columns: max-content 1fr;
                gap: 2px 12px;
                margin-top: 4px;
                font-size: 13px;
            }

            .gcl-plabel {
                color: #9aa0a6;
            }

            @media (max-width: 800px) {
                .gcl-window { width: 100vw; height: 100vh; border-radius: 0; }
                .gcl-body { flex-direction: column; }
                .gcl-sidebar { width: 100%; max-height: 32%; border-right: 0; border-bottom: 1px solid #333639; }
            }

            /* ---------- In-page annotations (Vencord-style) ---------- */
            .gc-tag {
                margin-left: 5px;
                color: #80868b;
                font-size: 10px;
                white-space: nowrap;
            }

            .gcl-old {
                color: #9aa0a6;
            }

            .gc-logger-history {
                display: block;
                margin: 2px 0 4px;
                padding: 0;
                color: inherit;
                font: 14px/1.45 'Google Sans', Roboto, Arial, sans-serif;
                overflow-wrap: anywhere;
                white-space: pre-wrap;
            }

            .gc-logger-version {
                padding: 1px 0;
                color: rgba(160, 166, 172, .95);
            }

            /* Old versions look like ghosted copies of Google's own bubbles */
            .gc-logger-history .gc-logger-version {
                display: block;
                width: fit-content;
                max-width: 100%;
                margin: 0 0 4px;
                padding: 7px 12px;
                border: 1px dashed rgba(255, 255, 255, .16);
                border-radius: 18px;
                background: rgba(255, 255, 255, .04);
            }

            .gc-missing-message-wrapper {
                display: block;
                width: 100%;
                margin: 4px 0;
                padding: 0 8px;
                box-sizing: border-box;
                clear: both;
            }

            .gc-missing-message {
                max-width: 100%;
                margin: 0;
                padding: 6px 12px;
                border-left: 3px solid #f28b82;
                border-radius: 4px;
                background: rgba(242, 139, 130, .10);
                font: 14px/1.45 'Google Sans', Roboto, Arial, sans-serif;
                overflow-wrap: anywhere;
                white-space: pre-wrap;
            }

            .gc-del-sender {
                margin-bottom: 2px;
                color: #c98b86;
                font-size: 12px;
                font-weight: 600;
            }

            .gc-del-line {
                color: #f4a7a1;
            }

            .gc-del-line.gc-del-old {
                color: rgba(244, 167, 161, .6);
            }

            .gc-missing-message .gc-tag {
                color: #d9847d;
            }

            .gc-logger-saved-images {
                margin: 2px 0;
                padding: 0 12px;
                color: #80868b;
                font: 12px/1.4 Arial, sans-serif;
                white-space: normal;
            }

            .gc-logger-saved-images .gc-tag {
                margin-left: 0;
            }

            .gc-logger-saved-image-list {
                display: flex;
                flex-wrap: wrap;
                gap: 8px;
                margin-top: 4px;
            }

            .gc-logger-saved-thumb,
            .gc-missing-message img {
                display: block;
                max-width: min(100%, 600px);
                max-height: 600px;
                border-radius: 8px;
                object-fit: contain;
            }

            .gc-saved-player {
                display: block;
                max-width: min(100%, 560px);
                max-height: 400px;
                border-radius: 6px;
            }

            .gc-parsed-quote {
                margin: 4px 0 8px 0;
                padding: 8px 12px;
                border-left: 3px solid #555;
                background: rgba(255, 255, 255, 0.05);
                border-radius: 4px;
                font-size: 13px;
                white-space: normal;
            }
            .gc-parsed-quote-sender {
                color: #8ab4f8;
                font-weight: bold;
                margin-bottom: 4px;
            }
            .gc-parsed-quote-text {
                color: #bbb;
                white-space: pre-wrap;
            }
            .gc-parsed-reply {
                margin-top: 4px;
                white-space: pre-wrap;
            }

            .gc-saved-wrap {
                display: block;
            }

            .gc-saved-dl {
                margin-top: 2px;
                font-size: 11px;
            }

            /* ---------- Rich message formatting ---------- */
            .gc-rich { white-space: pre-wrap; }
            .gc-rich div, .gc-rich li { white-space: pre-wrap; }
            .gc-rich ul, .gc-rich ol { margin: 2px 0; padding-left: 22px; }
            .gc-rich blockquote {
                margin: 4px 0;
                padding: 6px 10px;
                border-left: 3px solid #8ab4f8;
                border-radius: 4px;
                background: rgba(255, 255, 255, .06);
            }
            .gc-rich code {
                padding: 1px 5px;
                border-radius: 4px;
                background: rgba(255, 255, 255, .10);
                font-family: 'Roboto Mono', Consolas, monospace;
                font-size: .92em;
            }
            .gc-rich pre {
                margin: 4px 0;
                padding: 8px 10px;
                border-radius: 6px;
                background: rgba(0, 0, 0, .35);
                font-family: 'Roboto Mono', Consolas, monospace;
                font-size: .92em;
                white-space: pre-wrap;
            }
        `;

        document.head.appendChild(style);
    }

    // --------------------------------------------------
    // Launcher
    // --------------------------------------------------

    function addLauncher() {
        if (document.getElementById('gchat-logger-launcher') || !document.body) {
            return;
        }

        const button = document.createElement('button');
        button.id = 'gchat-logger-launcher';
        button.setAttribute(OWN_ATTR, '');
        button.title = 'Open the local chat log viewer';
        button.addEventListener('click', toggleViewer);

        const label = document.createElement('span');
        label.textContent = 'Chat Logs';

        const count = document.createElement('span');
        count.className = 'gcl-count';
        count.textContent = '0';

        button.append(label, count);
        document.body.appendChild(button);

        updateLauncher();
    }

    function updateLauncher(total) {
        const count = document.querySelector('#gchat-logger-launcher .gcl-count');

        if (!count) {
            return;
        }

        if (typeof total !== 'number') {
            total = getLogs().length;
        }

        count.textContent = String(total);
    }

    function markNewData() {
        newDataAvailable = true;
        updateViewerStatus();
    }

    // --------------------------------------------------
    // Viewer
    // --------------------------------------------------

    function toggleViewer() {
        if (document.getElementById('gchat-logger-panel')) {
            closeViewer();
            return;
        }

        openViewer();
    }

    function closeViewer() {
        document.getElementById('gchat-logger-panel')?.remove();

        if (escHandler) {
            document.removeEventListener('keydown', escHandler, true);
            escHandler = null;
        }
    }

    function openViewer() {
        const panel = document.createElement('div');
        panel.id = 'gchat-logger-panel';
        panel.setAttribute(OWN_ATTR, '');

        panel.innerHTML = `
            <div class="gcl-window">
                <div class="gcl-header">
                    <h2 class="gcl-title">Google Chat Logs</h2>
                    <div class="gcl-tabs">
                        <button class="gcl-tab" id="gcl-tab-messages">Messages</button>
                        <button class="gcl-tab" id="gcl-tab-presence">Presence</button>
                    </div>
                    <div class="gcl-status" id="gcl-status"></div>
                    <div class="gcl-actions">
                        <button class="gcl-btn gcl-primary" id="gcl-refresh">Refresh</button>
                        <span id="gcl-msg-actions" style="display: contents">
                            <button class="gcl-btn" id="gcl-export">Export JSON</button>
                            <button class="gcl-btn" id="gcl-export-images" title="Embeds every saved attachment (images, files, video, audio) as base64 - can be large">Export + files</button>
                            <label class="gcl-check" title="Limit exports to the chat selected in the sidebar">
                                <input type="checkbox" id="gcl-export-selected">
                                Selected chat only
                            </label>
                            <button class="gcl-btn" id="gcl-retry">Retry downloads</button>
                            <button class="gcl-btn" id="gcl-debug" title="Copies what the script sees in the last attachment message (tokens removed) to the clipboard">Copy debug info</button>
                            <button class="gcl-btn" id="gcl-reset-flags" title="Mark every possibly-deleted message as present again (confirmed deletions are kept)">Reset possibly deleted</button>
                            <button class="gcl-btn gcl-danger" id="gcl-delete-chat" hidden>Delete this chat</button>
                            <button class="gcl-btn gcl-danger" id="gcl-clear">Clear all</button>
                        </span>
                        <span id="gcl-pres-actions" style="display: contents" hidden>
                            <button class="gcl-btn" id="gcl-pres-export">Export presence</button>
                            <button class="gcl-btn gcl-danger" id="gcl-pres-clear">Clear presence</button>
                        </span>
                        <button class="gcl-btn" id="gcl-close">Close</button>
                    </div>
                </div>
                <div class="gcl-body" id="gcl-body-messages">
                    <aside class="gcl-sidebar">
                        <div class="gcl-sidebar-head">
                            <input class="gcl-input" id="gcl-chat-filter" type="search"
                                placeholder="Find a chat...">
                        </div>
                        <div class="gcl-chatlist" id="gcl-chatlist"></div>
                    </aside>
                    <section class="gcl-main">
                        <div class="gcl-toolbar">
                            <input class="gcl-input" id="gcl-search" type="search"
                                placeholder="Search text, sender, attachments...">
                            <select class="gcl-select" id="gcl-sort" title="Sort order">
                                <option value="newest">Newest first</option>
                                <option value="oldest">Oldest first</option>
                                <option value="chat">Group by chat (A-Z)</option>
                            </select>
                            <select class="gcl-select" id="gcl-status-filter" title="Filter by status">
                                <option value="all">All messages</option>
                                <option value="edited">Edited</option>
                                <option value="reactions">With reactions</option>
                                <option value="missing">Deleted / missing</option>
                                <option value="attachments">With attachments</option>
                                <option value="unsaved">Attachments not saved</option>
                            </select>
                        </div>
                        <div class="gcl-entries" id="gcl-entries"></div>
                    </section>
                </div>
                <div class="gcl-body" id="gcl-body-presence" hidden>
                    <section class="gcl-main">
                        <div class="gcl-toolbar">
                            <input class="gcl-input" id="gcl-pres-search" type="search"
                                placeholder="Search name, user id, status...">
                            <select class="gcl-select" id="gcl-pres-sort" title="Sort order">
                                <option value="recent">Online now, then last seen</option>
                                <option value="lastonline">Online now, then last online</option>
                                <option value="name">Name (A-Z)</option>
                            </select>
                            <select class="gcl-select" id="gcl-pres-filter" title="Filter">
                                <option value="all">Everyone logged</option>
                                <option value="live">Visible on screen now</option>
                                <option value="active">Active now</option>
                                <option value="notactive">Not active now</option>
                            </select>
                        </div>
                        <div class="gcl-pres-note">
                            Status is only recorded while a Google Chat tab is open and the person's
                            presence dot is on screen, so "Last online" means the last time this
                            browser saw them Active. Names are guessed from the page - use Rename to fix them.
                        </div>
                        <div class="gcl-entries" id="gcl-pres-list"></div>
                    </section>
                </div>
            </div>
        `;

        document.body.appendChild(panel);

        const $ = selector => panel.querySelector(selector);

        $('#gcl-sort').value = ui.sort;
        $('#gcl-status-filter').value = ui.status;
        $('#gcl-pres-sort').value = ui.psort;
        $('#gcl-pres-filter').value = ui.pfilter;

        function applyTab() {
            const presence = ui.tab === 'presence';

            $('#gcl-body-messages').hidden = presence;
            $('#gcl-body-presence').hidden = !presence;
            $('#gcl-msg-actions').hidden = presence;
            $('#gcl-pres-actions').hidden = !presence;
            $('#gcl-tab-messages').classList.toggle('gcl-tab-active', !presence);
            $('#gcl-tab-presence').classList.toggle('gcl-tab-active', presence);
        }

        function setTab(tab) {
            ui.tab = tab;
            saveUiPrefs();
            renderLimit = VIEWER_PAGE_SIZE;
            applyTab();
            updateViewer();
        }

        $('#gcl-tab-messages').onclick = () => setTab('messages');
        $('#gcl-tab-presence').onclick = () => setTab('presence');

        panel.addEventListener('mousedown', event => {
            if (event.target === panel) {
                closeViewer();
            }
        });

        $('#gcl-close').onclick = closeViewer;

        $('#gcl-refresh').onclick = async () => {
            scanPresence();
            await scanMessages();
            renderLimit = VIEWER_PAGE_SIZE;
            await updateViewer();
        };

        $('#gcl-export').onclick = () => exportLogs(false, selectedExportChat());
        $('#gcl-export-images').onclick = () => exportLogs(true, selectedExportChat());

        $('#gcl-retry').onclick = async () => {
            await retryFailedDownloads();
            await updateViewer();
        };

        $('#gcl-debug').onclick = async () => {
            const button = $('#gcl-debug');
            const text = collectAttachmentDebug();

            console.log('[GC Logger] Debug info:\n' + text);

            try {
                await navigator.clipboard.writeText(text);
                button.textContent = 'Copied!';
            } catch {
                button.textContent = 'See console';
            }

            setTimeout(() => {
                const b = document.getElementById('gcl-debug');

                if (b) {
                    b.textContent = 'Copy debug info';
                }
            }, 2500);
        };

        $('#gcl-reset-flags').onclick = async () => {
            await resetPossibleFlags();
            await updateViewer();
        };

        $('#gcl-delete-chat').onclick = async () => {
            const chats = buildChatIndex(getLogs());
            const chat = chats.get(ui.chat);

            if (!chat) {
                return;
            }

            if (!confirm(
                'Delete all ' + chat.count + ' logged messages (and saved attachments) from "' +
                chat.name + '"?\n\nMessages currently visible on the page will be logged again. ' +
                'This cannot be undone.'
            )) {
                return;
            }

            await deleteChatLogs(ui.chat);
            ui.chat = 'all';
            saveUiPrefs();
            await updateViewer();
        };

        $('#gcl-clear').onclick = async () => {
            if (!confirm(
                'Delete ALL saved message logs and locally stored attachments? ' +
                '(Presence history is kept - use "Clear presence" on the Presence tab.) ' +
                'This cannot be undone.'
            )) {
                return;
            }

            await clearAllLogs();
            ui.chat = 'all';
            saveUiPrefs();
            await updateViewer();
        };

        $('#gcl-pres-export').onclick = () => exportPresence();

        $('#gcl-pres-clear').onclick = async () => {
            await clearPresence();
            await updateViewer();
        };

        let searchTimer = null;

        $('#gcl-search').addEventListener('input', () => {
            clearTimeout(searchTimer);
            renderLimit = VIEWER_PAGE_SIZE;
            searchTimer = setTimeout(updateViewer, 250);
        });

        let presenceSearchTimer = null;

        $('#gcl-pres-search').addEventListener('input', () => {
            clearTimeout(presenceSearchTimer);
            presenceSearchTimer = setTimeout(updateViewer, 200);
        });

        $('#gcl-pres-sort').onchange = event => {
            ui.psort = event.target.value;
            saveUiPrefs();
            updateViewer();
        };

        $('#gcl-pres-filter').onchange = event => {
            ui.pfilter = event.target.value;
            saveUiPrefs();
            updateViewer();
        };

        $('#gcl-chat-filter').addEventListener('input', () => {
            updateViewer();
        });

        $('#gcl-sort').onchange = event => {
            ui.sort = event.target.value;
            saveUiPrefs();
            renderLimit = VIEWER_PAGE_SIZE;
            updateViewer();
        };

        $('#gcl-status-filter').onchange = event => {
            ui.status = event.target.value;
            saveUiPrefs();
            renderLimit = VIEWER_PAGE_SIZE;
            updateViewer();
        };

        escHandler = event => {
            if (event.key === 'Escape' && document.getElementById('gchat-logger-panel')) {
                event.stopPropagation();
                closeViewer();
            }
        };

        document.addEventListener('keydown', escHandler, true);

        renderLimit = VIEWER_PAGE_SIZE;
        applyTab();
        updateViewer();
        scanMessages();
        scanPresence();
        refreshStorageInfo();
    }

    function selectedExportChat() {
        const box = document.getElementById('gcl-export-selected');

        return box && box.checked && ui.chat !== 'all' ? ui.chat : null;
    }

    // Browser-wide estimate for chat.google.com (includes Google Chat's own data).
    function refreshStorageInfo() {
        if (
            !navigator.storage ||
            !navigator.storage.estimate ||
            Date.now() - storageInfoAt < 5000
        ) {
            return;
        }

        storageInfoAt = Date.now();

        navigator.storage
            .estimate()
            .then(estimate => {
                storageInfo =
                    formatBytes(estimate.usage || 0) +
                    (estimate.quota ? ' of ' + formatBytes(estimate.quota) : '');
                updateViewerStatus();
            })
            .catch(() => {});
    }

    function updateViewerStatus(total, shown, chatCount) {
        const status = document.getElementById('gcl-status');

        if (!status) {
            return;
        }

        if (ui.tab === 'presence') {
            status.textContent = presenceStatusText();
            status.classList.remove('gcl-new');
            document.getElementById('gcl-refresh')?.classList.remove('gcl-pulse');

            return;
        }

        if (typeof total === 'number') {
            status.dataset.total = String(total);
            status.dataset.shown = String(shown);
            status.dataset.chats = String(chatCount ?? status.dataset.chats ?? 0);
        }

        const totalText = status.dataset.total || '0';
        const shownText = status.dataset.shown || '0';

        status.textContent =
            totalText + ' messages in ' + (status.dataset.chats || '0') + ' chats' +
            (shownText !== totalText ? ' | showing ' + shownText : '') +
            (newDataAvailable ? ' | New data - click Refresh' : ' | Up to date') +
            (lastScanMs ? ' | last scan ' + Math.round(lastScanMs) + ' ms' : '') +
            (storageInfo ? ' | site storage ' + storageInfo : '');

        status.classList.toggle('gcl-new', newDataAvailable);

        document
            .getElementById('gcl-refresh')
            ?.classList.toggle('gcl-pulse', newDataAvailable);
    }

    // ---- chat index / filtering -----------------------

    function buildChatIndex(logs) {
        const map = new Map();

        for (const log of logs) {
            const key = chatKeyOf(log);
            let chat = map.get(key);

            if (!chat) {
                chat = {
                    key: key,
                    name: '',
                    nameTime: -1,
                    count: 0,
                    flagged: 0,
                    last: 0
                };
                map.set(key, chat);
            }

            const time = logTime(log);

            chat.count++;

            if (log.status === 'possibly-missing' || log.status === 'deleted') {
                chat.flagged++;
            }

            if (time > chat.last) {
                chat.last = time;
            }

            if (
                log.conversation &&
                log.conversation !== UNKNOWN_CONVERSATION &&
                time >= chat.nameTime
            ) {
                chat.name = log.conversation;
                chat.nameTime = time;
            }
        }

        for (const chat of map.values()) {
            if (!chat.name) {
                chat.name = chat.key;
            }
        }

        return map;
    }

    function matchesStatus(log, status) {
        switch (status) {
            case 'edited':
                return log.edits.length > 0;
            case 'reactions':
                return (log.reactionEvents || []).length > 0 ||
                    (log.reactions || []).length > 0;
            case 'missing':
                return log.status === 'possibly-missing' || log.status === 'deleted';
            case 'attachments':
                return log.attachments.length > 0;
            case 'unsaved':
                return log.attachments.some(a => !a.blobSaved);
            default:
                return true;
        }
    }

    function avatarColor(name) {
        return 'hsl(' + (parseInt(hashText(name || '?'), 16) % 360) + ' 42% 40%)';
    }

    function renderSidebar(panel, chats, totalCount) {
        const list = panel.querySelector('#gcl-chatlist');
        const filter = panel
            .querySelector('#gcl-chat-filter')
            .value.trim()
            .toLowerCase();

        const items = [];

        function addItem(key, name, count, meta, flagged) {
            const button = document.createElement('button');
            button.className = 'gcl-chat' + (ui.chat === key ? ' gcl-active' : '');

            const title = document.createElement('div');
            title.className = 'gcl-chat-name';
            title.textContent = name;
            title.title = name;

            const info = document.createElement('div');
            info.className = 'gcl-chat-meta';

            const left = document.createElement('span');
            left.textContent = count + (count === 1 ? ' message' : ' messages');

            const right = document.createElement('span');

            if (flagged) {
                const flag = document.createElement('span');
                flag.className = 'gcl-chat-flag';
                flag.textContent = flagged + ' deleted/missing  ';
                right.appendChild(flag);
            }

            right.appendChild(document.createTextNode(meta));
            info.append(left, right);
            button.append(title, info);

            button.onclick = () => {
                ui.chat = key;
                saveUiPrefs();
                renderLimit = VIEWER_PAGE_SIZE;
                updateViewer();
            };

            items.push(button);
        }

        addItem('all', 'All chats', totalCount, chats.size + ' chats', 0);

        [...chats.values()]
            .filter(chat => !filter || chat.name.toLowerCase().includes(filter))
            .sort((a, b) => b.last - a.last)
            .forEach(chat => {
                addItem(
                    chat.key,
                    chat.name,
                    chat.count,
                    chat.last ? formatDay(chat.last) : '',
                    chat.flagged
                );
            });

        list.replaceChildren(...items);

        panel.querySelector('#gcl-delete-chat').hidden = ui.chat === 'all';
    }

    async function updateViewer() {
        const panel = document.getElementById('gchat-logger-panel');

        if (!panel) {
            return;
        }

        if (ui.tab === 'presence') {
            await renderPresence(panel);
            return;
        }

        const token = ++renderToken;
        const entries = panel.querySelector('#gcl-entries');
        const query = panel
            .querySelector('#gcl-search')
            .value.trim()
            .toLowerCase();

        const all = getLogs();
        const chats = buildChatIndex(all);

        if (ui.chat !== 'all' && !chats.has(ui.chat)) {
            ui.chat = 'all';
            saveUiPrefs();
        }

        renderSidebar(panel, chats, all.length);

        let rows = all.filter(log => {
            if (ui.chat !== 'all' && chatKeyOf(log) !== ui.chat) {
                return false;
            }

            if (!matchesStatus(log, ui.status)) {
                return false;
            }

            if (!query) {
                return true;
            }

            return [
                log.message,
                log.sender,
                log.conversation,
                ...log.edits.map(edit => edit.message),
                ...log.attachments.map(item => item.name)
            ]
                .join('\n')
                .toLowerCase()
                .includes(query);
        });

        if (ui.sort === 'oldest') {
            rows.sort((a, b) => logTime(a) - logTime(b));
        } else if (ui.sort === 'chat') {
            rows.sort((a, b) => {
                const nameA = chats.get(chatKeyOf(a)).name.toLowerCase();
                const nameB = chats.get(chatKeyOf(b)).name.toLowerCase();

                if (nameA !== nameB) {
                    return nameA < nameB ? -1 : 1;
                }

                return logTime(b) - logTime(a);
            });
        } else {
            rows.sort((a, b) => logTime(b) - logTime(a));
        }

        newDataAvailable = false;
        updateViewerStatus(all.length, rows.length, chats.size);

        if (!rows.length) {
            entries.textContent = all.length
                ? 'No messages match the current filters.'
                : 'No messages have been logged yet.';
            entries.className = 'gcl-entries gcl-empty';
            return;
        }

        entries.className = 'gcl-entries';

        const visible = rows.slice(0, renderLimit);
        const built = [];
        const grouping = ui.sort === 'chat' && ui.chat === 'all';
        let lastGroup = null;
        let lastDay = null;

        for (const log of visible) {
            const chat = chats.get(chatKeyOf(log));

            if (grouping) {
                if (chat.key !== lastGroup) {
                    lastGroup = chat.key;

                    const heading = document.createElement('div');
                    heading.className = 'gcl-chat-heading';
                    heading.textContent = chat.name + ' (' + chat.count + ')';
                    built.push(heading);
                }
            } else {
                const day = formatDay(logTime(log));

                if (day !== lastDay) {
                    lastDay = day;

                    const divider = document.createElement('div');
                    divider.className = 'gcl-day';
                    divider.textContent = day;
                    built.push(divider);
                }
            }

            built.push(await buildEntry(log, chat, ui.chat === 'all' && !grouping));

            if (token !== renderToken) {
                return;
            }
        }

        if (rows.length > visible.length) {
            const more = document.createElement('button');
            more.className = 'gcl-btn gcl-more';
            more.textContent =
                'Show ' + Math.min(VIEWER_PAGE_SIZE, rows.length - visible.length) +
                ' more (' + visible.length + ' of ' + rows.length + ' shown)';

            more.onclick = () => {
                renderLimit += VIEWER_PAGE_SIZE;
                updateViewer();
            };

            built.push(more);
        }

        entries.replaceChildren(...built);
    }

    async function buildEntry(log, chat, showChatChip) {
        const flagged =
            log.status === 'possibly-missing' || log.status === 'deleted';

        const entry = document.createElement('div');
        entry.className = 'gcl-entry' + (flagged ? ' gcl-flagged' : '');

        const sender = log.sender || 'Unknown';

        const avatar = await buildAvatarElement(sender);

        const content = document.createElement('div');
        content.className = 'gcl-content';

        const meta = document.createElement('div');
        meta.className = 'gcl-meta';

        const senderEl = document.createElement('span');
        senderEl.className = 'gcl-sender';
        senderEl.textContent = sender;

        const timeEl = document.createElement('span');
        timeEl.className = 'gcl-time';
        timeEl.textContent = formatTime(log.timestamp ?? log.loggedAt);

        meta.append(senderEl, timeEl);

        if (showChatChip) {
            const chip = document.createElement('button');
            chip.className = 'gcl-chip';
            chip.textContent = chat.name;
            chip.title = 'Show only this chat';
            chip.onclick = () => {
                ui.chat = chat.key;
                saveUiPrefs();
                renderLimit = VIEWER_PAGE_SIZE;
                updateViewer();
            };
            meta.appendChild(chip);
        }

        function badge(text, className) {
            const element = document.createElement('span');
            element.className = 'gcl-badge ' + className;
            element.textContent = text;
            meta.appendChild(element);
        }

        if (log.status === 'deleted') {
            badge('Deleted', 'gcl-deleted');
        } else if (log.status === 'possibly-missing') {
            badge('Possibly deleted', 'gcl-deleted');

            const dismiss = document.createElement('button');
            dismiss.className = 'gcl-chip';
            dismiss.textContent = 'Not deleted';
            dismiss.title = 'Clear this flag';
            dismiss.onclick = async () => {
                await dismissFlag(log.id);
                await updateViewer();
            };
            meta.appendChild(dismiss);
        }

        if (log.edits.length) {
            badge(
                'Edited' + (log.edits.length > 1 ? ' x' + log.edits.length : ''),
                'gcl-edited'
            );
        }

        if (log.attachments.length) {
            badge(
                log.attachments.length + (log.attachments.length === 1 ? ' attachment' : ' attachments'),
                'gcl-attach'
            );
        }

        const reactionEvents = log.reactionEvents || [];
        const currentReactions = (log.reactions || []).filter(r => r.count > 0);

        if (reactionEvents.length) {
            badge(
                'Reactions x' + reactionEvents.length,
                'gcl-react'
            );
        }

        content.appendChild(meta);

        for (const edit of log.edits) {
            const oldLine = document.createElement('div');
            oldLine.className = 'gcl-text gcl-old';
            oldLine.appendChild(formatMessageHTML(edit.message, edit.html));
            oldLine.appendChild(makeTag(
                'edited',
                edit.editedAt ? 'Replaced ' + formatTime(edit.editedAt) : ''
            ));
            content.appendChild(oldLine);
        }

        if (log.message || !log.attachments.length) {
            const message = document.createElement('div');
            message.className = 'gcl-text';
            message.appendChild(
                formatMessageHTML(
                    log.message || '[Empty message]',
                    log.message ? log.html : ''
                )
            );

            if (log.edits.length) {
                message.appendChild(makeTag('edited'));
            }

            content.appendChild(message);
        }

        for (const attachment of log.attachments) {
            const file = document.createElement('div');
            file.className = 'gcl-attachment';

            const kind = attachment.thumbnail
                ? 'preview thumbnail only'
                : attachment.type;

            const heading = document.createElement('div');
            heading.textContent =
                (attachment.name || attachment.type || 'Attachment') +
                ' (' + kind + ')';

            file.appendChild(heading);

            const saveState = document.createElement('div');

            if (attachment.blobSaved) {
                saveState.className = 'gcl-ok';
                saveState.textContent =
                    'Saved locally' +
                    (attachment.size ? ' - ' + formatBytes(attachment.size) : '');
            } else {
                saveState.className = 'gcl-err';
                saveState.textContent =
                    'Not saved locally' +
                    (attachment.saveError ? ': ' + attachment.saveError : '');
            }

            file.appendChild(saveState);

            if (attachment.blobSaved) {
                try {
                    const stored = await getStoredImage(attachment.id);

                    if (stored && stored.blob) {
                        file.appendChild(makeSavedMedia(attachment, stored));
                    } else {
                        saveState.className = 'gcl-err';
                        saveState.textContent =
                            'Saved record is missing from IndexedDB.';
                    }
                } catch (error) {
                    saveState.className = 'gcl-err';
                    saveState.textContent =
                        'Could not read saved attachment: ' + error.message;
                }
            }

            if (!attachment.blobSaved || attachment.type !== 'image') {
                file.appendChild(makeLink(
                    attachment.url,
                    attachment.blobSaved ? 'Open original' : 'Try opening original URL'
                ));
            }

            content.appendChild(file);
        }

        if (currentReactions.length || reactionEvents.length) {
            content.appendChild(buildReactionBlock(currentReactions, reactionEvents));
        }

        content.appendChild(makeLink(log.url || location.href, 'Open conversation'));

        entry.append(avatar, content);

        return entry;
    }

    // Current reactions as small chips, plus a collapsed history list.
    function buildReactionBlock(current, events) {
        const block = document.createElement('div');
        block.className = 'gcl-react-block';

        if (current.length) {
            const chips = document.createElement('div');
            chips.className = 'gcl-react-chips';

            current.forEach(r => {
                const chip = document.createElement('span');
                chip.className = 'gcl-react-chip' + (r.pressed === 'true' ? ' gcl-mine' : '');
                chip.textContent = emojiLabel(r.emoji) + ' ' + r.count;
                chips.appendChild(chip);
            });

            block.appendChild(chips);
        }

        if (events.length) {
            const details = document.createElement('details');
            details.className = 'gcl-react-history';

            const summary = document.createElement('summary');
            summary.textContent =
                'Reaction history (' + events.length + ')';
            details.appendChild(summary);

            [...events].reverse().forEach(event => {
                event.changes.forEach(change => {
                    const info = describeReactionChange(change);
                    const row = document.createElement('div');
                    row.className = 'gcl-react-row';

                    const t = document.createElement('span');
                    t.className = 'gcl-react-time';
                    t.textContent = formatTime(event.timestamp);

                    const text = document.createElement('span');
                    text.className = 'gcl-react-' + info.cls;
                    text.textContent = info.text;

                    row.append(t, text);
                    details.appendChild(row);
                });
            });

            block.appendChild(details);
        }

        return block;
    }

    function makeLink(url, text) {
        const link = document.createElement('a');
        link.className = 'gcl-link';
        link.href = url;
        link.target = '_blank';
        link.rel = 'noopener noreferrer';
        link.textContent = text;
        link.style.marginRight = '12px';
        return link;
    }

    // --------------------------------------------------
    // Export / clear
    // --------------------------------------------------

    function blobToDataUrl(blob) {
        return new Promise((resolve, reject) => {
            const reader = new FileReader();
            reader.onload = () => resolve(reader.result);
            reader.onerror = () => reject(reader.error);
            reader.readAsDataURL(blob);
        });
    }

    async function exportLogs(includeFiles, onlyChat) {
        let logs = JSON.parse(JSON.stringify(getLogs()));
        let fileName = 'google-chat-logs.json';

        if (onlyChat) {
            logs = logs.filter(log => chatKeyOf(log) === onlyChat);

            const chat = buildChatIndex(logs).get(onlyChat);
            const slug = String(chat ? chat.name : onlyChat)
                .toLowerCase()
                .replace(/[^a-z0-9]+/g, '-')
                .replace(/^-+|-+$/g, '')
                .slice(0, 40);

            fileName = 'google-chat-logs-' + (slug || 'chat') + '.json';
        }

        if (includeFiles) {
            for (const log of logs) {
                for (const attachment of log.attachments) {
                    if (!attachment.blobSaved) {
                        continue;
                    }

                    try {
                        const stored = await getStoredImage(attachment.id);

                        if (stored && stored.blob) {
                            attachment.dataUrl = await blobToDataUrl(stored.blob);
                        }
                    } catch (error) {
                        console.warn('[GC Logger] Could not export attachment:', error);
                    }
                }
            }
        }

        const output = {
            exportedAt: new Date().toISOString(),
            scope: onlyChat ? 'single chat' : 'all chats',
            attachmentStorage: includeFiles ? 'embedded as data URLs' : 'IndexedDB',
            note: includeFiles
                ? 'Saved attachments are embedded as base64 data URLs (dataUrl).'
                : 'Attachment blobs remain in this browser and are not embedded ' +
                  'in this JSON export. Use "Export + files" to embed them.',
            messages: logs
        };

        const blob = new Blob(
            [JSON.stringify(output, null, 2)],
            { type: 'application/json' }
        );

        const url = URL.createObjectURL(blob);
        const link = document.createElement('a');

        link.href = url;
        link.download = fileName;
        link.click();

        setTimeout(() => URL.revokeObjectURL(url), 1000);
    }

    function dismissFlag(id) {
        return exclusive(async () => {
            const logs = getLogs();
            const log = logs.find(item => item.id === id);

            if (log && log.status === 'possibly-missing') {
                log.status = 'saved';
                delete log.missingDetectedAt;
                saveLogs(logs, new Set([id]));
            }

            findAnnotation('gc-missing-message-wrapper', id)?.remove();
        });
    }

    function resetPossibleFlags() {
        return exclusive(async () => {
            const logs = getLogs();
            let count = 0;

            for (const log of logs) {
                if (log.status === 'possibly-missing') {
                    log.status = 'saved';
                    delete log.missingDetectedAt;
                    count++;
                }
            }

            if (count) {
                saveLogs(logs);
            }

            missingSince.clear();
            removeAllAnnotations();
            scheduleScan();

            console.log('[GC Logger] Cleared ' + count + ' possibly-deleted flag(s).');
        });
    }

    function deleteChatLogs(chatKey) {
        return exclusive(async () => {
            const logs = getLogs();
            const keep = [];

            for (const log of logs) {
                if (chatKeyOf(log) !== chatKey) {
                    keep.push(log);
                    continue;
                }

                for (const attachment of log.attachments) {
                    revokeImageUrl(attachment.id);
                    await deleteImage(attachment.id);
                }
            }

            saveLogs(keep);
            removeAllAnnotations();
            liveElements.clear();
            missingSince.clear();
            pendingEdits.clear();
            previousVisibleIds = new Set();

            console.log('[GC Logger] Deleted logs for chat:', chatKey);
        });
    }

    function clearAllLogs() {
        return exclusive(async () => {
            localStorage.removeItem(STORAGE_KEY);
            clearTimeout(persistTimer);
            persistTimer = null;
            persistIds.clear();
            persistFull = false;
            persistedSig.clear();
            logCache = [];
            localStorage.removeItem(AVATAR_KEY);
            Object.keys(avatarMap).forEach(key => delete avatarMap[key]);
            revokeAllImageUrls();

            try {
                await clearImageDatabase();
            } catch (error) {
                console.error('[GC Logger] Could not clear stored attachments:', error);
            }

            removeAllAnnotations();
            previousVisibleIds = new Set();
            liveElements.clear();
            pendingMarkers.clear();
            missingSince.clear();
            pendingEdits.clear();
            newDataAvailable = false;
            updateLauncher(0);

            console.log('[GC Logger] Saved logs cleared.');
        });
    }

    // --------------------------------------------------
    // Start
    // --------------------------------------------------

    function redactTokens(text) {
        return String(text).replace(/(attachment_token=)[^&"'\s<>]+/gi, '$1REDACTED');
    }

    // Everything the script can see about attachments in the most recent
    // message that has any, plus the attachment requests the page itself made
    // recently (click Chat's own Download button first to capture the URL
    // type Chat uses for real downloads). Tokens are removed.
    function collectAttachmentDebug() {
        const areas = [...document.querySelectorAll(MESSAGE_SELECTOR)];

        const area =
            [...areas].reverse().find(
                a =>
                    a.innerHTML.includes('get_attachment_url') ||
                    extractAttachments(a).length > 0
            ) || areas[areas.length - 1];

        if (!area) {
            return 'No message on screen.';
        }

        let requests = [];

        try {
            requests = performance
                .getEntriesByType('resource')
                .filter(entry => entry.name.includes('get_attachment_url'))
                .slice(-20)
                .map(entry => ({ initiator: entry.initiatorType, url: entry.name }));
        } catch { /* ignore */ }

        const output = {
            version: '9.0',
            extracted: extractAttachments(area).map(a => ({
                type: a.type,
                name: a.name,
                thumbnail: !!a.thumbnail,
                url: a.url,
                previewUrl: a.previewUrl || ''
            })),
            elements: [...area.querySelectorAll(
                'a[href], img, video, audio, [data-download-url], [data-file-url], [data-url]'
            )].map(el => ({
                tag: el.tagName,
                url:
                    el.getAttribute('href') ||
                    el.currentSrc ||
                    el.getAttribute('data-download-url') ||
                    el.getAttribute('data-file-url') ||
                    el.getAttribute('data-url') ||
                    '',
                html: el.outerHTML.slice(0, 300)
            })),
            recentChatRequests: requests
        };

        return redactTokens(JSON.stringify(output, null, 2));
    }

    async function init() {
        createStyles();

        try {
            await Promise.race([
                openDatabase(),
                new Promise((resolve, reject) =>
                    setTimeout(() => reject(new Error(
                        'Opening IndexedDB timed out. Close or reload your other ' +
                        'Google Chat tabs, then reload this one.'
                    )), 8000)
                )
            ]);

            console.info('[GC Logger] IndexedDB is ready.');
        } catch (error) {
            console.error('[GC Logger] IndexedDB could not be opened.', error);

            alert(
                'The logger could not open IndexedDB (' + (error && error.message) + '). ' +
                'Messages will still be logged, but attachment files cannot be saved.'
            );
        }

        try {
            await loadLogs();
        } catch (error) {
            console.error('[GC Logger] Could not load the log from IndexedDB.', error);

            dbLogs = false;
            logCache = readLogsFromLocalStorage();

            alert(
                'The logger could not move its log to IndexedDB and will keep ' +
                'using the old localStorage log (about 5 MB limit) this session.'
            );
        }

        addLauncher();
        scanMessages();

        // Presence logging runs alongside message logging.
        await initPresence();

        observer = new MutationObserver(records => {
            if (records.every(isOwnMutation)) {
                return;
            }

            addLauncher();

            // Presence dots live in the chat list too, so any page change counts.
            schedulePresenceScan();

            if (records.some(isRelevantMutation)) {
                scheduleScan();
                scheduleReactionScan();
            }
        });

        observer.observe(document.body, {
            childList: true,
            subtree: true,
            characterData: true,
            attributes: true,
            attributeFilter: [
                'src',
                'href',
                'data-file-name',
                'data-filename',
                'data-mime-type',
                'data-download-url',
                'data-count',
                'aria-pressed'
            ]
        });

        window.addEventListener('scroll', () => {
            lastScrollAt = Date.now();
            scheduleScan();
        }, { capture: true, passive: true });
        window.addEventListener('popstate', () => scheduleScan());

        // Another tab changed the log: re-read it next time.
        window.addEventListener('storage', event => {
            if (!dbLogs && (event.key === STORAGE_KEY || event.key === null)) {
                logCache = null;
            }
        });

        // Write pending changes before the tab is hidden / minimized / closed.
        window.addEventListener('pagehide', () => {
            if (dbLogs) {
                flushLogs();
            }
        });

        document.addEventListener('visibilitychange', () => {
            if (dbLogs && document.visibilityState === 'hidden') {
                flushLogs();
            }
        });

        // Safety net: compare everything against IndexedDB once a minute.
        setInterval(() => {
            if (dbLogs) {
                queuePersist();
            }
        }, 60000);

        // Safety net: SPA navigation and any missed mutation are picked up here.
        let tick = 0;

        setInterval(() => {
            tick++;

            if (location.pathname !== lastSeenPath || tick % 5 === 0) {
                scheduleScan();
            }
        }, 1000);

        // Keep the Presence tab's relative times ("5 min ago") fresh.
        setInterval(() => {
            if (ui.tab === 'presence' && document.getElementById('gchat-logger-panel')) {
                updateViewer();
            }
        }, 15000);

        pageWindow.viewChatLogs = toggleViewer;
        pageWindow.scanChatMessages = scanMessages;

        // Tests whether the script can read who reacted (opens each popup briefly).
        pageWindow.gcReactionProbe = async () => {
            const out = [];

            for (const area of document.querySelectorAll(MESSAGE_SELECTOR)) {
                for (const [emoji, chip] of chipsByEmoji(area)) {
                    const users = await probeChip(chip);

                    out.push({
                        message: (area.querySelector(TEXT_SELECTOR)?.innerText || '').slice(0, 30),
                        emoji: emoji,
                        count: chip.dataset.count,
                        users: users ? users.map(u => u.name).join(', ') : '(could not read)'
                    });
                }
            }

            console.table(out);
        };
        pageWindow.clearChatLogs = clearAllLogs;

        // Presence console helpers
        pageWindow.viewPresence = () => {
            ui.tab = 'presence';
            saveUiPrefs();

            if (document.getElementById('gchat-logger-panel')) {
                closeViewer();
            }

            openViewer();
        };

        pageWindow.presenceSummary = () => {
            console.table(presenceSummaryRows());
        };

        pageWindow.lastSeen = id => {
            const user = presenceUsers.get(String(id));

            console.log(
                user && user.lastActive
                    ? 'last seen Active: ' + new Date(user.lastActive).toLocaleString()
                    : 'never seen Active'
            );
        };

        pageWindow.presenceDump = dumpPresenceDom;
        pageWindow.exportPresence = exportPresence;
        pageWindow.clearPresence = clearPresence;

        // Debug helper: shows what the formatting serializer sees on the
        // last message currently on screen.
        pageWindow.gcDebug = () => console.log(collectAttachmentDebug());

        pageWindow.gcDumpFormat = () => {
            const areas = document.querySelectorAll(
                MESSAGE_SELECTOR + ' ' + TEXT_SELECTOR
            );
            const el = areas[areas.length - 1];

            console.log('HTML:', el?.innerHTML);
            console.log('Serialized:', serializeRich(el));
        };

        // Debug helper: shows every attachment candidate in the last message
        // on screen (what the script extracted and the raw links/images/data
        // attributes it was working from). Use it when a file will not save.
        pageWindow.gcDumpAttachments = () => {
            const areas = document.querySelectorAll(MESSAGE_SELECTOR);
            const area = areas[areas.length - 1];

            if (!area) {
                console.log('No message on screen.');
                return;
            }

            console.log(
                'Extracted:',
                extractAttachments(area).map(a => ({
                    type: a.type,
                    name: a.name,
                    thumbnail: !!a.thumbnail,
                    url: a.url
                }))
            );

            area
                .querySelectorAll('a[href], img, video, audio, [data-download-url], [data-file-url], [data-url]')
                .forEach(el => {
                    console.log(
                        el.tagName,
                        el.getAttribute('href') ||
                            el.currentSrc ||
                            el.getAttribute('data-download-url') ||
                            el.getAttribute('data-file-url') ||
                            el.getAttribute('data-url') ||
                            '',
                        el.outerHTML.slice(0, 250)
                    );
                });
        };

        // Debug helper: lists the images near the last message so the
        // profile-photo detection can be checked.
        pageWindow.gcDumpAvatar = () => {
            const areas = document.querySelectorAll(MESSAGE_SELECTOR);

            console.log('Message bubbles on screen:', areas.length);

            areas.forEach((area, index) => {
                console.log(
                    'Message ' + index + ' avatar:',
                    findAvatarUrl(area) || '(none found)'
                );
            });

            console.log('All img.' + AVATAR_IMG_CLASS + ' on page:');

            document.querySelectorAll('img.' + AVATAR_IMG_CLASS).forEach(img => {
                const rect = img.getBoundingClientRect();

                console.log(
                    Math.round(rect.width) + 'x' + Math.round(rect.height),
                    img.currentSrc || img.src
                );
            });

            console.log('Stored avatars:', JSON.parse(JSON.stringify(avatarMap)));
        };

        console.log('[GC Logger] Initialized (v9.1, messages + presence).');
        console.log('[GC Logger] Commands: viewChatLogs(), viewPresence(), presenceSummary(), lastSeen(id), scanChatMessages(), clearChatLogs(), gcDumpFormat(), gcDumpAttachments(), gcDebug(), gcReactionProbe()');
    }

    if (document.body) {
        init();
    } else {
        window.addEventListener('DOMContentLoaded', init, { once: true });
    }
})();
