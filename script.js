const owner = "SnowStone-White";
const repo = "ChatGPT-history";
const fallbackBranch = "main";

const MANIFEST_URL = "./manifest.json";
const CACHE_KEY = `repo-index-manifest-cache::${owner}/${repo}`;
const CACHE_TTL = 10 * 60 * 1000;
const THEME_KEY = "repo-index-theme-mode";

const repoInfoEl = document.getElementById("repoInfo");
const branchInfoEl = document.getElementById("branchInfo");
const countInfoEl = document.getElementById("countInfo");
const cacheInfoEl = document.getElementById("cacheInfo");
const updateInfoEl = document.getElementById("updateInfo");

const contentAreaEl = document.getElementById("contentArea");
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

let repoMeta = { branch: fallbackBranch, generatedAt: null, source: MANIFEST_URL };
let allFiles = [];

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

function groupFiles(files) {
  const groups = new Map();
  for (const file of files) {
    if (!groups.has(file.type)) groups.set(file.type, []);
    groups.get(file.type).push(file);
  }
  const preferredOrder = ["html", "pdf", "image", "text", "code", "archive", "other"];
  return [...groups.entries()].sort((a, b) => preferredOrder.indexOf(a[0]) - preferredOrder.indexOf(b[0]));
}

function render(files) {
  const filtered = filterFiles(files);
  const sorted = sortFiles(filtered);
  const grouped = groupFiles(sorted);

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

  repoInfoEl.textContent = `${manifest.owner || owner} / ${manifest.repo || repo}`;
  branchInfoEl.textContent = repoMeta.branch;
  cacheInfoEl.textContent = cacheLabel;
  updateInfoEl.textContent = formatDate(manifest.generatedAt);

  allFiles = manifest.files || [];
  render(allFiles);
}

async function loadData(forceRefresh = false) {
  contentAreaEl.innerHTML = `<div class="empty">正在读取文件索引…</div>`;

  if (!forceRefresh) {
    const cached = loadCache();
    if (cached) {
      hydratePage(cached, "命中");
      setManifestStatus(
        "使用缓存",
        "当前页面优先读取本地缓存的 manifest.json，不直接请求 GitHub 文件树 API。",
        {
          className: "rate-ok",
          source: "manifest.json",
          generatedAt: cached.generatedAt,
          filesCount: cached.files.length,
          cacheAge: "本地缓存有效",
        }
      );
      return;
    }
  }

  try {
    const manifest = await fetchManifest(forceRefresh);
    hydratePage(manifest, forceRefresh ? "已刷新" : "新加载");
    saveCache(manifest);
    setManifestStatus(
      "静态清单",
      "页面已改为读取仓库内的 manifest.json，正常浏览时不占用 GitHub REST API 匿名额度。",
      {
        className: "rate-ok",
        source: MANIFEST_URL,
        generatedAt: manifest.generatedAt,
        filesCount: manifest.files.length,
        cacheAge: forceRefresh ? "刚刚刷新" : "已同步",
      }
    );
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
          cacheAge: "旧缓存",
        }
      );
      return;
    }

    contentAreaEl.innerHTML = `<div class="error">加载失败：${escapeHtml(err.message)}

请检查：
1. manifest.json 是否已生成并提交到仓库根目录
2. GitHub Pages 是否部署的是当前分支
3. 页面与 manifest.json 是否在同一站点目录</div>`;

    setManifestStatus(
      "读取失败",
      "当前方案依赖静态 manifest.json，而不是 GitHub API。",
      {
        className: "rate-danger",
        source: MANIFEST_URL,
        generatedAt: null,
        filesCount: null,
        cacheAge: "无缓存",
      }
    );
  }
}

searchInputEl.addEventListener("input", () => render(allFiles));
typeFilterEl.addEventListener("change", () => render(allFiles));
sortSelectEl.addEventListener("change", () => render(allFiles));

refreshBtnEl.addEventListener("click", async () => {
  clearCache();
  await loadData(true);
});

checkRateBtnEl.addEventListener("click", async () => {
  await loadData(true);
});

initTheme();
bindThemeEvents();
loadData();
