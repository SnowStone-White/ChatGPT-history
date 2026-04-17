const owner = "SnowStone-White";
const repo = "ChatGPT-history";
const fallbackBranch = "main";

const MANIFEST_URL = "./manifest.json";
const VERSION_URL = "./version.json";

const CACHE_KEY = `repo-index-manifest-cache::${owner}/${repo}`;
const VERSION_CACHE_KEY = `repo-index-version-cache::${owner}/${repo}`;
const DIR_PATH_KEY = `repo-index-dir-path::${owner}/${repo}`;
const CACHE_TTL = 10 * 60 * 1000;
const VERSION_CHECK_INTERVAL = 30 * 1000;
const AUTO_REFRESH_ON_UPDATE = false;
const AUTO_REFRESH_DELAY = 3000;
const THEME_KEY = "repo-index-theme-mode";

const repoInfoEl = document.getElementById("repoInfo");
const branchInfoEl = document.getElementById("branchInfo");
const countInfoEl = document.getElementById("countInfo");
const cacheInfoEl = document.getElementById("cacheInfo");
const updateInfoEl = document.getElementById("updateInfo");
const versionInfoEl = document.getElementById("versionInfo");

const contentAreaEl = document.getElementById("contentArea");
const directoryAreaEl = document.getElementById("directoryArea");
const breadcrumbBarEl = document.getElementById("breadcrumbBar");
const goRootBtnEl = document.getElementById("goRootBtn");
const goParentBtnEl = document.getElementById("goParentBtn");

const searchInputEl = document.getElementById("searchInput");
const sortSelectEl = document.getElementById("sortSelect");
const typeFilterEl = document.getElementById("typeFilter");
const refreshBtnEl = document.getElementById("refreshBtn");
const themeSelectEl = document.getElementById("themeSelect");

const checkRateBtnEl = document.getElementById("checkRateBtn");
const rateStatusEl = document.getElementById("rateStatus");
const rateLimitEl = document.getElementById("rateLimit");
const rateRemainingEl = document.getElementById("rateRemaining");
const rateUsedEl = document.getElementById("rateUsed");
const rateResetEl = document.getElementById("rateReset");
const rateHintEl = document.getElementById("rateHint");

const updateBannerEl = document.getElementById("updateBanner");
const updateBannerDetailEl = document.getElementById("updateBannerDetail");
const updateNowBtnEl = document.getElementById("updateNowBtn");
const dismissUpdateBtnEl = document.getElementById("dismissUpdateBtn");

let allFiles = [];
let currentVersion = null;
let pendingVersion = null;
let versionCheckTimer = null;
let autoRefreshTimer = null;
let currentDirPath = "";

function escapeHtml(str) {
  return String(str).replace(/[&<>"']/g, (s) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
    "'": "&#39;"
  }[s]));
}

function formatBytes(bytes) {
  const n = Number(bytes || 0);
  if (n < 1024) return `${n} B`;
  if (n < 1024 * 1024) return `${(n / 1024).toFixed(1)} KB`;
  if (n < 1024 * 1024 * 1024) return `${(n / 1024 / 1024).toFixed(1)} MB`;
  return `${(n / 1024 / 1024 / 1024).toFixed(1)} GB`;
}

function formatDate(dateStr) {
  if (!dateStr) return "-";
  const d = new Date(dateStr);
  if (Number.isNaN(d.getTime())) return "-";
  return d.toLocaleString("zh-CN", { hour12: false });
}

function getExtension(path) {
  const name = path.split("/").pop() || "";
  const idx = name.lastIndexOf(".");
  return idx >= 0 ? name.slice(idx + 1).toLowerCase() : "";
}

function getFileType(path) {
  const ext = getExtension(path);
  if (["html", "htm"].includes(ext)) return "html";
  if (["pdf"].includes(ext)) return "pdf";
  if (["png", "jpg", "jpeg", "gif", "webp", "svg", "bmp", "ico", "avif"].includes(ext)) return "image";
  if (["md", "txt", "json", "csv", "xml", "yml", "yaml"].includes(ext)) return "text";
  if (["js", "mjs", "cjs", "ts", "jsx", "tsx", "py", "java", "c", "cpp", "h", "hpp", "cs", "go", "rs", "php", "rb", "sh", "bat", "ps1", "css", "scss", "sql"].includes(ext)) return "code";
  if (["zip", "rar", "7z", "tar", "gz"].includes(ext)) return "archive";
  return "other";
}

function getGroupLabel(type) {
  const map = {
    html: "🌐 HTML 页面",
    pdf: "📕 PDF 文档",
    image: "🖼️ 图片文件",
    text: "📄 文本 / Markdown / JSON",
    code: "💻 代码 / 脚本",
    archive: "🗜️ 压缩包",
    other: "📦 其他文件"
  };
  return map[type] || "📦 其他文件";
}

function getIcon(path) {
  const type = getFileType(path);
  const map = {
    html: "🌐",
    pdf: "📕",
    image: "🖼️",
    text: "📄",
    code: "💻",
    archive: "🗜️",
    other: "📦"
  };
  return map[type] || "📦";
}

function toPagesUrl(path) {
  const base = location.pathname.endsWith("/")
    ? location.pathname
    : location.pathname.replace(/\/[^/]*$/, "/");
  return base + path.split("/").map(encodeURIComponent).join("/");
}

function getAutoThemeByTime() {
  const hour = new Date().getHours();
  return (hour >= 19 || hour < 7) ? "dark" : "light";
}

function applyTheme(mode) {
  const actualTheme = mode === "auto" ? getAutoThemeByTime() : mode;
  document.documentElement.setAttribute("data-theme", actualTheme);
}

function initTheme() {
  const savedMode = localStorage.getItem(THEME_KEY) || "auto";
  themeSelectEl.value = savedMode;
  applyTheme(savedMode);
}

function bindThemeEvents() {
  themeSelectEl.addEventListener("change", () => {
    const mode = themeSelectEl.value;
    localStorage.setItem(THEME_KEY, mode);
    applyTheme(mode);
  });
}

function saveDirPath(path) {
  currentDirPath = path;
  try {
    localStorage.setItem(DIR_PATH_KEY, path);
  } catch {}
}

function loadDirPath() {
  try {
    return localStorage.getItem(DIR_PATH_KEY) || "";
  } catch {
    return "";
  }
}

function loadCache() {
  try {
    const raw = localStorage.getItem(CACHE_KEY);
    if (!raw) return null;
    const parsed = JSON.parse(raw);
    if (!parsed || !parsed.time || !Array.isArray(parsed.files)) return null;
    if (Date.now() - parsed.time > CACHE_TTL) return null;
    return parsed;
  } catch {
    return null;
  }
}

function loadAnyCache() {
  try {
    const raw = localStorage.getItem(CACHE_KEY);
    if (!raw) return null;
    const parsed = JSON.parse(raw);
    return parsed && Array.isArray(parsed.files) ? parsed : null;
  } catch {
    return null;
  }
}

function saveCache(data) {
  try {
    localStorage.setItem(CACHE_KEY, JSON.stringify({ time: Date.now(), ...data }));
  } catch {}
}

function clearCache() {
  try {
    localStorage.removeItem(CACHE_KEY);
  } catch {}
}

function saveVersionCache(data) {
  try {
    localStorage.setItem(VERSION_CACHE_KEY, JSON.stringify(data));
  } catch {}
}

function loadVersionCache() {
  try {
    const raw = localStorage.getItem(VERSION_CACHE_KEY);
    if (!raw) return null;
    return JSON.parse(raw);
  } catch {
    return null;
  }
}

function setManifestStatus(status, hint, detail = {}) {
  rateStatusEl.textContent = status;
  rateStatusEl.className = "";
  if (detail.className) rateStatusEl.classList.add(detail.className);
  rateLimitEl.textContent = detail.source || "manifest.json";
  rateRemainingEl.textContent = detail.generatedAt ? formatDate(detail.generatedAt) : "-";
  rateUsedEl.textContent = detail.filesCount != null ? String(detail.filesCount) : "-";
  rateResetEl.textContent = detail.cacheAge || "-";
  rateHintEl.textContent = hint;
}

function normalizeVersion(version) {
  if (!version || typeof version !== "object") {
    throw new Error("version.json 格式不正确");
  }
  return {
    owner: version.owner || owner,
    repo: version.repo || repo,
    branch: version.branch || fallbackBranch,
    generatedAt: version.generatedAt || null,
    filesCount: Number(version.filesCount || 0),
    latestCommit: version.latestCommit || "",
    source: version.source || "version.json"
  };
}

function normalizeManifest(manifest) {
  if (!manifest || !Array.isArray(manifest.files)) {
    throw new Error("manifest.json 格式不正确：缺少 files 数组");
  }
  return {
    owner: manifest.owner || owner,
    repo: manifest.repo || repo,
    branch: manifest.branch || fallbackBranch,
    generatedAt: manifest.generatedAt || null,
    files: manifest.files.map((file) => ({
      path: file.path,
      name: file.name || (file.path.split("/").pop() || file.path),
      size: Number(file.size || 0),
      type: file.type || getFileType(file.path),
      lastModified: file.lastModified || null,
      sha: file.sha || ""
    }))
  };
}

async function fetchVersion(forceRefresh = false) {
  const url = forceRefresh ? `${VERSION_URL}?t=${Date.now()}` : VERSION_URL;
  const res = await fetch(url, { cache: forceRefresh ? "no-store" : "default" });
  if (!res.ok) throw new Error(`读取 version.json 失败：${res.status}`);
  return normalizeVersion(await res.json());
}

async function fetchManifest(forceRefresh = false) {
  const url = forceRefresh ? `${MANIFEST_URL}?t=${Date.now()}` : MANIFEST_URL;
  const res = await fetch(url, { cache: forceRefresh ? "no-store" : "default" });
  if (!res.ok) throw new Error(`读取 manifest.json 失败：${res.status}`);
  return normalizeManifest(await res.json());
}

function filterFiles(files) {
  const keyword = searchInputEl.value.trim().toLowerCase();
  const type = typeFilterEl.value;

  return files.filter((file) => {
    const matchedKeyword = !keyword || [
      file.path,
      file.name,
      getExtension(file.path),
      getGroupLabel(file.type)
    ].join(" ").toLowerCase().includes(keyword);

    const matchedType = type === "all" || file.type === type;
    return matchedKeyword && matchedType;
  });
}

function sortFiles(files) {
  const mode = sortSelectEl.value;
  const list = [...files];

  if (mode === "name-asc") {
    list.sort((a, b) => a.path.localeCompare(b.path, "zh-CN"));
  } else if (mode === "time-asc") {
    list.sort((a, b) => {
      const ta = a.lastModified ? new Date(a.lastModified).getTime() : Number.MAX_SAFE_INTEGER;
      const tb = b.lastModified ? new Date(b.lastModified).getTime() : Number.MAX_SAFE_INTEGER;
      if (ta !== tb) return ta - tb;
      return a.path.localeCompare(b.path, "zh-CN");
    });
  } else {
    list.sort((a, b) => {
      const ta = a.lastModified ? new Date(a.lastModified).getTime() : -1;
      const tb = b.lastModified ? new Date(b.lastModified).getTime() : -1;
      if (ta !== tb) return tb - ta;
      return a.path.localeCompare(b.path, "zh-CN");
    });
  }

  return list;
}

function groupFilesByType(files) {
  const groups = new Map();
  for (const file of files) {
    if (!groups.has(file.type)) groups.set(file.type, []);
    groups.get(file.type).push(file);
  }
  const preferredOrder = ["html", "pdf", "image", "text", "code", "archive", "other"];
  return [...groups.entries()].sort((a, b) => preferredOrder.indexOf(a[0]) - preferredOrder.indexOf(b[0]));
}

function renderTypeGroups(files) {
  const filtered = filterFiles(files);
  const sorted = sortFiles(filtered);
  const grouped = groupFilesByType(sorted);

  countInfoEl.textContent = String(filtered.length);

  if (filtered.length === 0) {
    contentAreaEl.innerHTML = `<div class="empty">没有匹配到文件。</div>`;
    return;
  }

  let html = "";
  for (const [type, items] of grouped) {
    html += `
      <section class="group">
        <div class="group-header">
          <h2 class="group-title">${getGroupLabel(type)}</h2>
          <div class="group-count">${items.length} 个文件</div>
        </div>
        <ul class="file-list">
          ${items.map((file) => `
            <li class="file-item">
              <div class="file-icon">${getIcon(file.path)}</div>
              <div class="file-main">
                <a class="file-link" href="${toPagesUrl(file.path)}" target="_blank" rel="noopener noreferrer">
                  ${escapeHtml(file.name)}
                </a>
                <div class="file-path">${escapeHtml(file.path)}</div>
              </div>
              <div class="file-meta">
                <div class="meta-line">${formatBytes(file.size)}</div>
                <div class="meta-line">${formatDate(file.lastModified)}</div>
              </div>
            </li>
          `).join("")}
        </ul>
      </section>
    `;
  }

  contentAreaEl.innerHTML = html;
}

function buildDirectoryView(files, dirPath) {
  const filtered = filterFiles(files);

  const dirs = new Map();
  const directFiles = [];

  for (const file of filtered) {
    const rawPath = file.path || "";
    const parts = rawPath.split("/");

    if (!dirPath) {
      if (parts.length === 1) {
        directFiles.push(file);
      } else {
        const first = parts[0];
        if (!dirs.has(first)) dirs.set(first, { name: first, count: 0 });
        dirs.get(first).count += 1;
      }
    } else {
      const prefix = `${dirPath}/`;
      if (!rawPath.startsWith(prefix)) continue;

      const remain = rawPath.slice(prefix.length);
      if (!remain) continue;

      const remainParts = remain.split("/");
      if (remainParts.length === 1) {
        directFiles.push(file);
      } else {
        const first = remainParts[0];
        const full = `${dirPath}/${first}`;
        if (!dirs.has(full)) dirs.set(full, { name: first, fullPath: full, count: 0 });
        dirs.get(full).count += 1;
      }
    }
  }

  const dirList = [...dirs.values()].sort((a, b) => a.name.localeCompare(b.name, "zh-CN"));
  const fileList = sortFiles(directFiles);

  return { dirList, fileList };
}

function renderBreadcrumb(path) {
  const parts = path ? path.split("/") : [];
  let html = `
    <span class="breadcrumb-item">
      ${parts.length === 0
        ? `<span class="breadcrumb-current">根目录</span>`
        : `<button class="breadcrumb-link" data-dir-nav="">根目录</button>`}
    </span>
  `;

  let acc = "";
  for (let i = 0; i < parts.length; i++) {
    acc = acc ? `${acc}/${parts[i]}` : parts[i];
    const isLast = i === parts.length - 1;
    html += `
      <span class="breadcrumb-sep">/</span>
      <span class="breadcrumb-item">
        ${isLast
          ? `<span class="breadcrumb-current">${escapeHtml(parts[i])}</span>`
          : `<button class="breadcrumb-link" data-dir-nav="${escapeHtml(acc)}">${escapeHtml(parts[i])}</button>`}
      </span>
    `;
  }

  breadcrumbBarEl.innerHTML = html;

  breadcrumbBarEl.querySelectorAll("[data-dir-nav]").forEach((el) => {
    el.addEventListener("click", () => {
      const path = el.getAttribute("data-dir-nav") || "";
      saveDirPath(path);
      renderDirectoryModule(allFiles);
    });
  });
}

function renderDirectoryModule(files) {
  renderBreadcrumb(currentDirPath);

  const { dirList, fileList } = buildDirectoryView(files, currentDirPath);

  if (dirList.length === 0 && fileList.length === 0) {
    directoryAreaEl.innerHTML = `<div class="empty">当前目录下没有匹配内容。</div>`;
    return;
  }

  let html = "";

  if (dirList.length > 0) {
    html += `<div class="dir-grid">`;
    html += dirList.map((dir) => `
      <div class="dir-item">
        <button class="dir-item-button" data-open-dir="${escapeHtml(dir.fullPath || dir.name)}">
          <div class="dir-item-head">
            <span class="file-icon">📁</span>
            <span class="dir-item-title">${escapeHtml(dir.name)}</span>
          </div>
          <div class="dir-item-sub">${dir.count} 个下级文件</div>
        </button>
      </div>
    `).join("");
    html += `</div>`;
  }

  if (fileList.length > 0) {
    html += `
      <section class="group" style="margin-top:${dirList.length > 0 ? "16px" : "0"};">
        <div class="group-header">
          <h2 class="group-title">📄 当前目录文件</h2>
          <div class="group-count">${fileList.length} 个文件</div>
        </div>
        <ul class="file-list">
          ${fileList.map((file) => `
            <li class="file-item">
              <div class="file-icon">${getIcon(file.path)}</div>
              <div class="file-main">
                <a class="file-link" href="${toPagesUrl(file.path)}" target="_blank" rel="noopener noreferrer">
                  ${escapeHtml(file.name)}
                </a>
                <div class="file-path">${escapeHtml(file.path)}</div>
              </div>
              <div class="file-meta">
                <div class="meta-line">${formatBytes(file.size)}</div>
                <div class="meta-line">${formatDate(file.lastModified)}</div>
              </div>
            </li>
          `).join("")}
        </ul>
      </section>
    `;
  }

  directoryAreaEl.innerHTML = html;

  directoryAreaEl.querySelectorAll("[data-open-dir]").forEach((el) => {
    el.addEventListener("click", () => {
      const path = el.getAttribute("data-open-dir") || "";
      saveDirPath(path);
      renderDirectoryModule(allFiles);
    });
  });
}

function showUpdateBanner(latestVersion) {
  pendingVersion = latestVersion;
  updateBannerDetailEl.textContent = `当前版本：${formatDate(currentVersion)}，新版本：${formatDate(latestVersion)}`;
  updateBannerEl.classList.remove("hidden");

  if (AUTO_REFRESH_ON_UPDATE) {
    if (autoRefreshTimer) clearTimeout(autoRefreshTimer);
    autoRefreshTimer = setTimeout(() => applyUpdateNow(), AUTO_REFRESH_DELAY);
  }
}

function hideUpdateBanner() {
  pendingVersion = null;
  updateBannerEl.classList.add("hidden");
  if (autoRefreshTimer) {
    clearTimeout(autoRefreshTimer);
    autoRefreshTimer = null;
  }
}

async function applyUpdateNow() {
  hideUpdateBanner();
  clearCache();
  await loadData(true);
}

async function checkForUpdates(silent = true) {
  try {
    const latest = await fetchVersion(true);
    saveVersionCache(latest);

    const latestVersion = latest.generatedAt || null;
    if (!latestVersion) return;

    if (!currentVersion) {
      currentVersion = latestVersion;
      versionInfoEl.textContent = formatDate(currentVersion);
      return;
    }

    if (latestVersion !== currentVersion && latestVersion !== pendingVersion) {
      showUpdateBanner(latestVersion);
      setManifestStatus("发现新版本", "后台检测到新的文件索引，可点击“立即更新”同步。", {
        className: "rate-warn",
        source: VERSION_URL,
        generatedAt: latest.generatedAt,
        filesCount: latest.filesCount,
        cacheAge: "检测到更新"
      });
    } else if (!pendingVersion && !silent) {
      setManifestStatus("已是最新", "当前页面已经是最新文件索引。", {
        className: "rate-ok",
        source: VERSION_URL,
        generatedAt: latest.generatedAt,
        filesCount: latest.filesCount,
        cacheAge: "已检查"
      });
    }
  } catch (err) {
    if (!silent) {
      setManifestStatus("检查失败", `version.json 检查失败：${err.message}`, {
        className: "rate-danger",
        source: VERSION_URL,
        generatedAt: null,
        filesCount: null,
        cacheAge: "检查失败"
      });
    }
  }
}

function hydratePage(manifest, cacheLabel) {
  currentVersion = manifest.generatedAt || null;
  versionInfoEl.textContent = formatDate(currentVersion);

  repoInfoEl.textContent = `${manifest.owner || owner} / ${manifest.repo || repo}`;
  branchInfoEl.textContent = manifest.branch || fallbackBranch;
  cacheInfoEl.textContent = cacheLabel;
  updateInfoEl.textContent = formatDate(manifest.generatedAt);

  allFiles = manifest.files || [];
  renderDirectoryModule(allFiles);
  renderTypeGroups(allFiles);
}

async function loadData(forceRefresh = false) {
  directoryAreaEl.innerHTML = `<div class="empty">正在读取目录…</div>`;
  contentAreaEl.innerHTML = `<div class="empty">正在读取文件索引…</div>`;

  if (!forceRefresh) {
    const cached = loadCache();
    if (cached) {
      hydratePage(cached, "命中");
      setManifestStatus("使用缓存", "当前页面优先读取本地缓存的 manifest.json，然后后台静默检查是否有新版本。", {
        className: "rate-ok",
        source: "manifest.json",
        generatedAt: cached.generatedAt,
        filesCount: cached.files.length,
        cacheAge: "本地缓存有效"
      });
      checkForUpdates(true);
      return;
    }
  }

  try {
    const manifest = await fetchManifest(forceRefresh);
    hydratePage(manifest, forceRefresh ? "已刷新" : "新加载");
    saveCache(manifest);

    const versionMeta = {
      owner: manifest.owner || owner,
      repo: manifest.repo || repo,
      branch: manifest.branch || fallbackBranch,
      generatedAt: manifest.generatedAt || null,
      filesCount: manifest.files.length,
      latestCommit: manifest.latestCommit || "",
      source: "manifest.json"
    };
    saveVersionCache(versionMeta);

    setManifestStatus("静态清单", "页面已读取仓库内的 manifest.json，并将继续后台检查 version.json。", {
      className: "rate-ok",
      source: MANIFEST_URL,
      generatedAt: manifest.generatedAt,
      filesCount: manifest.files.length,
      cacheAge: forceRefresh ? "刚刚刷新" : "已同步"
    });

    hideUpdateBanner();
  } catch (err) {
    const stale = loadAnyCache();
    if (stale) {
      hydratePage(stale, "过期缓存");
      setManifestStatus("离线回退", `manifest.json 读取失败，已回退到旧缓存：${err.message}`, {
        className: "rate-warn",
        source: MANIFEST_URL,
        generatedAt: stale.generatedAt,
        filesCount: stale.files.length,
        cacheAge: "旧缓存"
      });
      return;
    }

    const msg = `<div class="error">加载失败：${escapeHtml(err.message)}</div>`;
    directoryAreaEl.innerHTML = msg;
    contentAreaEl.innerHTML = msg;
  }
}

function startVersionPolling() {
  if (versionCheckTimer) clearInterval(versionCheckTimer);
  versionCheckTimer = setInterval(() => checkForUpdates(true), VERSION_CHECK_INTERVAL);
}

function initVersionInfo() {
  const cachedVersion = loadVersionCache();
  if (cachedVersion?.generatedAt) {
    versionInfoEl.textContent = formatDate(cachedVersion.generatedAt);
  }
}

searchInputEl.addEventListener("input", () => {
  renderDirectoryModule(allFiles);
  renderTypeGroups(allFiles);
});

typeFilterEl.addEventListener("change", () => {
  renderDirectoryModule(allFiles);
  renderTypeGroups(allFiles);
});

sortSelectEl.addEventListener("change", () => {
  renderDirectoryModule(allFiles);
  renderTypeGroups(allFiles);
});

refreshBtnEl.addEventListener("click", async () => {
  clearCache();
  hideUpdateBanner();
  await loadData(true);
});

checkRateBtnEl.addEventListener("click", async () => {
  await checkForUpdates(false);
});

updateNowBtnEl.addEventListener("click", async () => {
  await applyUpdateNow();
});

dismissUpdateBtnEl.addEventListener("click", () => {
  hideUpdateBanner();
});

goRootBtnEl.addEventListener("click", () => {
  saveDirPath("");
  renderDirectoryModule(allFiles);
});

goParentBtnEl.addEventListener("click", () => {
  if (!currentDirPath) return;
  const parts = currentDirPath.split("/");
  parts.pop();
  saveDirPath(parts.join("/"));
  renderDirectoryModule(allFiles);
});

document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "visible") checkForUpdates(true);
});

window.addEventListener("focus", () => {
  checkForUpdates(true);
});

initTheme();
bindThemeEvents();
initVersionInfo();
saveDirPath(loadDirPath());
loadData();
startVersionPolling();