const owner = "SnowStone-White";
const repo = "ChatGPT-history";
const fallbackBranch = "main";

const MANIFEST_URL = "./manifest.json";
const VERSION_URL = "./version.json";

const CACHE_KEY = `repo-index-manifest-cache::${owner}/${repo}`;
const VERSION_CACHE_KEY = `repo-index-version-cache::${owner}/${repo}`;
const GROUP_MODE_KEY = `repo-index-group-mode::${owner}/${repo}`;
const TREE_EXPANDED_KEY = `repo-index-tree-expanded::${owner}/${repo}`;

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
const groupModeInfoEl = document.getElementById("groupModeInfo");

const contentAreaEl = document.getElementById("contentArea");
const searchInputEl = document.getElementById("searchInput");
const sortSelectEl = document.getElementById("sortSelect");
const typeFilterEl = document.getElementById("typeFilter");
const groupModeSelectEl = document.getElementById("groupModeSelect");
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

let repoMeta = { branch: fallbackBranch, generatedAt: null, source: MANIFEST_URL };
let allFiles = [];
let currentVersion = null;
let pendingVersion = null;
let versionCheckTimer = null;
let autoRefreshTimer = null;
let expandedTreePaths = new Set(["root"]);

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
  if (["js", "ts", "jsx", "tsx", "py", "java", "c", "cpp", "h", "hpp", "cs", "go", "rs", "php", "rb", "sh", "bat", "ps1", "css", "scss", "sql"].includes(ext)) return "code";
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

function getTopFolder(path) {
  const normalized = String(path || "").replace(/^\/+|\/+$/g, "");
  if (!normalized) return "root";
  const parts = normalized.split("/");
  return parts.length > 1 ? parts[0] : "root";
}

function getGroupMode() {
  return groupModeSelectEl.value || "type";
}

function getGroupModeText(mode) {
  if (mode === "folder") return "按一级文件夹分组";
  if (mode === "tree") return "按目录树浏览";
  return "按类型分组";
}

function updateGroupModeInfo() {
  groupModeInfoEl.textContent = getGroupModeText(getGroupMode());
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

  setInterval(() => {
    const currentMode = localStorage.getItem(THEME_KEY) || "auto";
    if (currentMode === "auto") applyTheme("auto");
  }, 60 * 1000);
}

function initGroupMode() {
  const savedMode = localStorage.getItem(GROUP_MODE_KEY) || "type";
  groupModeSelectEl.value = savedMode;
  updateGroupModeInfo();
}

function saveGroupMode() {
  try {
    localStorage.setItem(GROUP_MODE_KEY, getGroupMode());
  } catch {}
}

function initTreeExpandedState() {
  try {
    const raw = localStorage.getItem(TREE_EXPANDED_KEY);
    if (!raw) {
      expandedTreePaths = new Set(["root"]);
      return;
    }
    const parsed = JSON.parse(raw);
    expandedTreePaths = new Set(Array.isArray(parsed) ? parsed : ["root"]);
    expandedTreePaths.add("root");
  } catch {
    expandedTreePaths = new Set(["root"]);
  }
}

function saveTreeExpandedState() {
  try {
    localStorage.setItem(TREE_EXPANDED_KEY, JSON.stringify([...expandedTreePaths]));
  } catch {}
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
      sha: file.sha || "",
      folder: getTopFolder(file.path)
    }))
  };
}

async function fetchVersion(forceRefresh = false) {
  const url = forceRefresh ? `${VERSION_URL}?t=${Date.now()}` : VERSION_URL;
  const res = await fetch(url, { cache: forceRefresh ? "no-store" : "default" });
  if (!res.ok) {
    throw new Error(`读取 version.json 失败：${res.status}`);
  }
  return normalizeVersion(await res.json());
}

async function fetchManifest(forceRefresh = false) {
  const url = forceRefresh ? `${MANIFEST_URL}?t=${Date.now()}` : MANIFEST_URL;
  const res = await fetch(url, { cache: forceRefresh ? "no-store" : "default" });
  if (!res.ok) {
    throw new Error(`读取 manifest.json 失败：${res.status}`);
  }
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
      getGroupLabel(file.type),
      file.folder
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
  } else if (mode === "time-desc") {
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

function groupFilesByFolder(files) {
  const groups = new Map();
  for (const file of files) {
    const folder = file.folder || "root";
    if (!groups.has(folder)) groups.set(folder, []);
    groups.get(folder).push(file);
  }

  return [...groups.entries()].sort((a, b) => {
    if (a[0] === "root" && b[0] !== "root") return -1;
    if (a[0] !== "root" && b[0] === "root") return 1;
    return a[0].localeCompare(b[0], "zh-CN");
  });
}

function buildGroupHeader(key, items, mode) {
  if (mode === "folder") {
    return `
      <div class="group-header">
        <h2 class="group-title">
          <span>📁</span>
          <span class="group-title-text">${escapeHtml(key)}</span>
          <span class="folder-badge">一级目录</span>
        </h2>
        <div class="group-count">${items.length} 个文件</div>
      </div>
    `;
  }

  return `
    <div class="group-header">
      <h2 class="group-title">
        <span class="group-title-text">${getGroupLabel(key)}</span>
      </h2>
      <div class="group-count">${items.length} 个文件</div>
    </div>
  `;
}

/* tree start */
function createTreeNode(name, fullPath = "root") {
  return {
    name,
    fullPath,
    folders: new Map(),
    files: []
  };
}

function buildFileTree(files) {
  const root = createTreeNode("root", "root");

  for (const file of files) {
    const normalized = String(file.path || "").replace(/^\/+|\/+$/g, "");
    const parts = normalized ? normalized.split("/") : [];
    if (parts.length <= 1) {
      root.files.push(file);
      continue;
    }

    let current = root;
    let currentPath = "";
    for (let i = 0; i < parts.length - 1; i++) {
      const segment = parts[i];
      currentPath = currentPath ? `${currentPath}/${segment}` : segment;
      if (!current.folders.has(segment)) {
        current.folders.set(segment, createTreeNode(segment, currentPath));
      }
      current = current.folders.get(segment);
    }
    current.files.push(file);
  }

  return root;
}

function countTree(node) {
  let folderCount = node.fullPath === "root" ? 0 : 1;
  let fileCount = node.files.length;

  for (const child of node.folders.values()) {
    const stats = countTree(child);
    folderCount += stats.folderCount;
    fileCount += stats.fileCount;
  }

  return { folderCount, fileCount };
}

function sortFoldersMap(map) {
  return [...map.entries()].sort((a, b) => a[0].localeCompare(b[0], "zh-CN"));
}

function isExpanded(path) {
  return expandedTreePaths.has(path);
}

function setExpanded(path, expanded) {
  if (path === "root") {
    expandedTreePaths.add("root");
    saveTreeExpandedState();
    return;
  }
  if (expanded) expandedTreePaths.add(path);
  else expandedTreePaths.delete(path);
  saveTreeExpandedState();
}

function expandAllTree(node) {
  if (node.fullPath) expandedTreePaths.add(node.fullPath);
  for (const child of node.folders.values()) {
    expandAllTree(child);
  }
}

function collapseAllTree(node) {
  expandedTreePaths = new Set(["root"]);
  saveTreeExpandedState();
}

function renderTreeFileRow(file) {
  return `
    <div class="tree-file-row">
      <div class="file-icon">${getIcon(file.path)}</div>
      <div class="file-main">
        <a class="file-link" href="${toPagesUrl(file.path)}" target="_blank" rel="noopener noreferrer">
          ${escapeHtml(file.name)}
        </a>
        <div class="file-path">${escapeHtml(file.path)}</div>
      </div>
      <div class="file-meta">
        <div class="meta-line">${formatBytes(file.size)}</div>
        <div class="meta-line file-time">${formatDate(file.lastModified)}</div>
      </div>
    </div>
  `;
}

function renderTreeNode(node, depth = 0) {
  const stats = countTree(node);
  const expanded = isExpanded(node.fullPath);
  const folders = sortFoldersMap(node.folders);
  const sortedFiles = sortFiles(node.files);

  const folderRow = node.fullPath === "root"
    ? ""
    : `
      <div class="tree-folder-row">
        <button
          class="folder-header-btn"
          type="button"
          data-tree-toggle="${escapeHtml(node.fullPath)}"
          aria-expanded="${expanded ? "true" : "false"}"
        >
          <span class="folder-arrow">${expanded ? "▾" : "▸"}</span>
          <span class="folder-icon">📁</span>
          <span class="folder-name">${escapeHtml(node.name)}</span>
          <span class="folder-meta">
            <span>${stats.folderCount - 1} 个子目录</span>
            <span>${stats.fileCount} 个文件</span>
          </span>
        </button>
      </div>
    `;

  const childrenHtml = expanded || node.fullPath === "root"
    ? `
      <div class="tree-node-children">
        ${folders.map(([, child]) => renderTreeNode(child, depth + 1)).join("")}
        ${sortedFiles.map((file) => renderTreeFileRow(file)).join("")}
      </div>
    `
    : "";

  return `
    <div class="tree-node" data-tree-node="${escapeHtml(node.fullPath)}">
      ${folderRow}
      ${childrenHtml}
    </div>
  `;
}

function renderTree(files) {
  const tree = buildFileTree(files);
  expandRootAncestorsForSearch(tree);

  const stats = countTree(tree);
  contentAreaEl.innerHTML = `
    <section class="tree-root">
      <div class="tree-toolbar">
        <div class="group-title">
          <span>🗂️</span>
          <span class="group-title-text">目录树浏览</span>
          <span class="folder-badge">${stats.folderCount} 个目录 / ${stats.fileCount} 个文件</span>
        </div>
        <div class="tree-actions">
          <button id="expandAllBtn" type="button" class="tree-toggle-btn">全部展开</button>
          <button id="collapseAllBtn" type="button" class="tree-toggle-btn">全部收起</button>
        </div>
      </div>
      <div class="tree-body">
        ${renderTreeNode(tree)}
      </div>
    </section>
  `;

  bindTreeEvents(tree);
}

function expandRootAncestorsForSearch(tree) {
  const keyword = searchInputEl.value.trim();
  if (!keyword) return;

  function walk(node) {
    for (const child of node.folders.values()) {
      expandedTreePaths.add(child.fullPath);
      walk(child);
    }
  }

  // 搜索时默认全部展开，便于看到结果
  walk(tree);
  saveTreeExpandedState();
}

function bindTreeEvents(tree) {
  const toggles = contentAreaEl.querySelectorAll("[data-tree-toggle]");
  toggles.forEach((btn) => {
    btn.addEventListener("click", () => {
      const path = btn.getAttribute("data-tree-toggle");
      const expanded = isExpanded(path);
      setExpanded(path, !expanded);
      render(allFiles);
    });
  });

  const expandAllBtn = document.getElementById("expandAllBtn");
  const collapseAllBtn = document.getElementById("collapseAllBtn");

  if (expandAllBtn) {
    expandAllBtn.addEventListener("click", () => {
      expandAllTree(tree);
      saveTreeExpandedState();
      render(allFiles);
    });
  }

  if (collapseAllBtn) {
    collapseAllBtn.addEventListener("click", () => {
      collapseAllTree(tree);
      render(allFiles);
    });
  }
}
/* tree end */

function render(files) {
  const filtered = filterFiles(files);
  const sorted = sortFiles(filtered);
  const mode = getGroupMode();

  countInfoEl.textContent = String(filtered.length);
  updateGroupModeInfo();

  if (filtered.length === 0) {
    contentAreaEl.innerHTML = `<div class="empty">没有匹配到文件。</div>`;
    return;
  }

  if (mode === "tree") {
    renderTree(sorted);
    return;
  }

  const grouped = mode === "folder"
    ? groupFilesByFolder(sorted)
    : groupFilesByType(sorted);

  let html = "";

  for (const [groupKey, items] of grouped) {
    html += `
      <section class="group">
        ${buildGroupHeader(groupKey, items, mode)}
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
                <div class="meta-line file-time">${formatDate(file.lastModified)}</div>
              </div>
            </li>
          `).join("")}
        </ul>
      </section>
    `;
  }

  contentAreaEl.innerHTML = html;
}

function hydratePage(manifest, cacheLabel) {
  repoMeta.branch = manifest.branch || fallbackBranch;
  repoMeta.generatedAt = manifest.generatedAt || null;

  currentVersion = manifest.generatedAt || null;
  versionInfoEl.textContent = formatDate(currentVersion);

  repoInfoEl.textContent = `${manifest.owner || owner} / ${manifest.repo || repo}`;
  branchInfoEl.textContent = repoMeta.branch;
  cacheInfoEl.textContent = cacheLabel;
  updateInfoEl.textContent = formatDate(manifest.generatedAt);

  allFiles = manifest.files || [];
  render(allFiles);
}

function showUpdateBanner(latestVersion) {
  pendingVersion = latestVersion;
  updateBannerDetailEl.textContent =
    `当前版本：${formatDate(currentVersion)}，新版本：${formatDate(latestVersion)}`;
  updateBannerEl.classList.remove("hidden");

  if (AUTO_REFRESH_ON_UPDATE) {
    if (autoRefreshTimer) clearTimeout(autoRefreshTimer);
    autoRefreshTimer = setTimeout(() => {
      applyUpdateNow();
    }, AUTO_REFRESH_DELAY);
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
      setManifestStatus(
        "发现新版本",
        "后台检测到新的文件索引，可点击“立即更新”同步。",
        {
          className: "rate-warn",
          source: VERSION_URL,
          generatedAt: latest.generatedAt,
          filesCount: latest.filesCount,
          cacheAge: "检测到更新"
        }
      );
    } else if (!pendingVersion && !silent) {
      setManifestStatus(
        "已是最新",
        "当前页面已经是最新文件索引。",
        {
          className: "rate-ok",
          source: VERSION_URL,
          generatedAt: latest.generatedAt,
          filesCount: latest.filesCount,
          cacheAge: "已检查"
        }
      );
    }
  } catch (err) {
    if (!silent) {
      setManifestStatus(
        "检查失败",
        `version.json 检查失败：${err.message}`,
        {
          className: "rate-danger",
          source: VERSION_URL,
          generatedAt: null,
          filesCount: null,
          cacheAge: "检查失败"
        }
      );
    }
  }
}

async function loadData(forceRefresh = false) {
  contentAreaEl.innerHTML = `<div class="empty">正在读取文件索引…</div>`;

  if (!forceRefresh) {
    const cached = loadCache();
    if (cached) {
      hydratePage(cached, "命中");
      setManifestStatus(
        "使用缓存",
        "当前页面优先读取本地缓存的 manifest.json，然后后台静默检查是否有新版本。",
        {
          className: "rate-ok",
          source: "manifest.json",
          generatedAt: cached.generatedAt,
          filesCount: cached.files.length,
          cacheAge: "本地缓存有效"
        }
      );
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

    setManifestStatus(
      "静态清单",
      "页面已读取仓库内的 manifest.json，并将继续后台检查 version.json。",
      {
        className: "rate-ok",
        source: MANIFEST_URL,
        generatedAt: manifest.generatedAt,
        filesCount: manifest.files.length,
        cacheAge: forceRefresh ? "刚刚刷新" : "已同步"
      }
    );

    hideUpdateBanner();
  } catch (err) {
    const stale = loadAnyCache();
    if (stale) {
      hydratePage(stale, "过期缓存");
      setManifestStatus(
        "离线回退",
        `manifest.json 读取失败，已回退到旧缓存：${err.message}`,
        {
          className: "rate-warn",
          source: MANIFEST_URL,
          generatedAt: stale.generatedAt,
          filesCount: stale.files.length,
          cacheAge: "旧缓存"
        }
      );
      return;
    }

    contentAreaEl.innerHTML = `<div class="error">加载失败：${escapeHtml(err.message)}

请检查：
1. manifest.json / version.json 是否已生成并提交到仓库根目录
2. GitHub Pages 是否部署的是当前分支
3. 页面与 manifest.json / version.json 是否在同一站点目录</div>`;

    setManifestStatus(
      "读取失败",
      "当前方案依赖静态 manifest.json 和 version.json。",
      {
        className: "rate-danger",
        source: MANIFEST_URL,
        generatedAt: null,
        filesCount: null,
        cacheAge: "无缓存"
      }
    );
  }
}

function startVersionPolling() {
  if (versionCheckTimer) clearInterval(versionCheckTimer);
  versionCheckTimer = setInterval(() => {
    checkForUpdates(true);
  }, VERSION_CHECK_INTERVAL);
}

function initVersionInfo() {
  const cachedVersion = loadVersionCache();
  if (cachedVersion?.generatedAt) {
    versionInfoEl.textContent = formatDate(cachedVersion.generatedAt);
  }
}

searchInputEl.addEventListener("input", () => render(allFiles));
typeFilterEl.addEventListener("change", () => render(allFiles));
sortSelectEl.addEventListener("change", () => render(allFiles));

groupModeSelectEl.addEventListener("change", () => {
  saveGroupMode();
  updateGroupModeInfo();
  render(allFiles);
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

document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "visible") {
    checkForUpdates(true);
  }
});

window.addEventListener("focus", () => {
  checkForUpdates(true);
});

initTheme();
bindThemeEvents();
initGroupMode();
initTreeExpandedState();
initVersionInfo();
loadData();
startVersionPolling();