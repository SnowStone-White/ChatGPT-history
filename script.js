const owner = "SnowStone-White";
const repo = "ChatGPT-history";
const fallbackBranch = "main";

const CACHE_KEY = `repo-index-cache::${owner}/${repo}`;
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

let repoMeta = { branch: fallbackBranch };
let allFiles = [];
let timeFillVersion = 0;

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
  if (!dateStr) return "加载中…";
  const d = new Date(dateStr);
  if (Number.isNaN(d.getTime())) return "-";
  return d.toLocaleString("zh-CN", { hour12: false });
}

function formatUnixTime(seconds) {
  if (!seconds) return "-";
  const d = new Date(seconds * 1000);
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

function fileId(path) {
  return "f_" + btoa(unescape(encodeURIComponent(path)))
    .replace(/=+/g, "")
    .replace(/\+/g, "_")
    .replace(/\//g, "-");
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
    if (currentMode === "auto") {
      applyTheme("auto");
    }
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

function saveCache(data) {
  try {
    localStorage.setItem(CACHE_KEY, JSON.stringify({
      time: Date.now(),
      ...data
    }));
  } catch {}
}

function clearCache() {
  try {
    localStorage.removeItem(CACHE_KEY);
  } catch {}
}

function setRateStatus(text, className = "") {
  rateStatusEl.textContent = text;
  rateStatusEl.className = "";
  if (className) {
    rateStatusEl.classList.add(className);
  }
}

async function checkRateLimit() {
  try {
    setRateStatus("检测中...");
    rateLimitEl.textContent = "-";
    rateRemainingEl.textContent = "-";
    rateUsedEl.textContent = "-";
    rateResetEl.textContent = "-";
    rateHintEl.textContent = "-";

    const res = await fetch("https://api.github.com/rate_limit", {
      headers: { "Accept": "application/vnd.github+json" }
    });

    if (!res.ok) {
      setRateStatus(`检测失败 (${res.status})`, "rate-danger");
      rateHintEl.textContent = "无法读取限流信息";
      return;
    }

    const data = await res.json();
    const core = data?.resources?.core || data?.rate || {};

    const limit = core.limit ?? "-";
    const remaining = core.remaining ?? "-";
    const used = core.used ?? "-";
    const reset = core.reset ?? null;

    rateLimitEl.textContent = String(limit);
    rateRemainingEl.textContent = String(remaining);
    rateUsedEl.textContent = String(used);
    rateResetEl.textContent = formatUnixTime(reset);

    if (typeof remaining === "number" && typeof limit === "number") {
      const ratio = limit > 0 ? remaining / limit : 0;

      if (remaining <= 0) {
        setRateStatus("已限流", "rate-danger");
        rateHintEl.textContent = "remaining 为 0，基本可以确定当前请求被限流";
      } else if (ratio <= 0.2 || remaining <= 10) {
        setRateStatus("接近限流", "rate-warn");
        rateHintEl.textContent = "剩余额度较低，继续频繁刷新可能触发 403";
      } else {
        setRateStatus("正常", "rate-ok");
        rateHintEl.textContent = "当前 REST API 配额仍可用";
      }
    } else {
      setRateStatus("未知", "rate-warn");
      rateHintEl.textContent = "返回结构异常，无法准确判断";
    }
  } catch (err) {
    setRateStatus("检测失败", "rate-danger");
    rateHintEl.textContent = err?.message || "请求失败";
  }
}

async function fetchRepoInfo() {
  const url = `https://api.github.com/repos/${owner}/${repo}`;
  const res = await fetch(url, {
    headers: { "Accept": "application/vnd.github+json" }
  });
  if (!res.ok) {
    throw new Error(`读取仓库信息失败：${res.status}`);
  }
  return await res.json();
}

async function fetchTree(currentBranch) {
  const url = `https://api.github.com/repos/${owner}/${repo}/git/trees/${currentBranch}?recursive=1`;
  const res = await fetch(url, {
    headers: { "Accept": "application/vnd.github+json" }
  });
  if (!res.ok) {
    throw new Error(`读取文件树失败：${res.status}`);
  }
  const data = await res.json();
  if (!data.tree || !Array.isArray(data.tree)) {
    throw new Error("返回的数据中没有 tree 字段。");
  }
  return data.tree;
}

async function fetchCommitTimeForPath(path) {
  const url = `https://api.github.com/repos/${owner}/${repo}/commits?path=${encodeURIComponent(path)}&per_page=1`;
  const res = await fetch(url, {
    headers: { "Accept": "application/vnd.github+json" }
  });
  if (!res.ok) return null;
  const data = await res.json();
  if (!Array.isArray(data) || data.length === 0) return null;
  return data[0]?.commit?.committer?.date || data[0]?.commit?.author?.date || null;
}

function normalizeFiles(treeItems) {
  return treeItems
    .filter((item) => item.type === "blob")
    .filter((item) => !["index.html", "style.css", "script.js"].includes(item.path))
    .map((item) => ({
      path: item.path,
      name: item.path.split("/").pop() || item.path,
      size: item.size || 0,
      sha: item.sha || "",
      type: getFileType(item.path),
      lastModified: null
    }));
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
            <li class="file-item" id="${fileId(file.path)}">
              <div class="file-icon">${getIcon(file.path)}</div>
              <div class="file-main">
                <a class="file-link" href="${toPagesUrl(file.path)}" target="_blank" rel="noopener noreferrer">
                  ${escapeHtml(file.name)}
                </a>
                <div class="file-path">${escapeHtml(file.path)}</div>
              </div>
              <div class="file-meta">
                <div class="meta-line">${formatBytes(file.size)}</div>
                <div class="meta-line file-time">${file.lastModified ? formatDate(file.lastModified) : "加载中…"}</div>
              </div>
            </li>
          `).join("")}
        </ul>
      </section>
    `;
  }

  contentAreaEl.innerHTML = html;
}

function updateFileTimeInDom(path, time) {
  const row = document.getElementById(fileId(path));
  if (!row) return;
  const timeEl = row.querySelector(".file-time");
  if (timeEl) {
    timeEl.textContent = time ? formatDate(time) : "-";
  }
}

function getVisibleFiles(files) {
  const filtered = filterFiles(files);
  const sorted = sortFiles(filtered);
  return sorted.slice(0, 20);
}

async function fillTimesAsync(files, version) {
  const visibleFiles = getVisibleFiles(files);
  const concurrency = 2;
  let index = 0;
  let updated = false;

  async function worker() {
    while (index < visibleFiles.length) {
      if (version !== timeFillVersion) return;

      const current = visibleFiles[index++];
      if (current.lastModified) {
        updateFileTimeInDom(current.path, current.lastModified);
        continue;
      }

      const time = await fetchCommitTimeForPath(current.path);

      if (version !== timeFillVersion) return;

      current.lastModified = time;
      updateFileTimeInDom(current.path, time);
      updated = true;
    }
  }

  const workers = Array.from({ length: Math.min(concurrency, visibleFiles.length) }, worker);
  await Promise.all(workers);

  if (version === timeFillVersion && updated) {
    saveCache({
      branch: repoMeta.branch,
      files: allFiles
    });

    if (sortSelectEl.value !== "name-asc") {
      render(allFiles);
    }

    updateInfoEl.textContent = new Date().toLocaleString("zh-CN", { hour12: false });
    checkRateLimit();
  }
}

async function loadData(forceRefresh = false) {
  timeFillVersion++;
  const currentVersion = timeFillVersion;

  repoInfoEl.textContent = `${owner} / ${repo}`;
  contentAreaEl.innerHTML = `<div class="empty">正在读取仓库文件…</div>`;

  if (!forceRefresh) {
    const cached = loadCache();
    if (cached) {
      repoMeta.branch = cached.branch || fallbackBranch;
      branchInfoEl.textContent = repoMeta.branch;
      cacheInfoEl.textContent = "命中";
      updateInfoEl.textContent = new Date(cached.time).toLocaleString("zh-CN", { hour12: false });
      allFiles = cached.files || [];
      render(allFiles);
      fillTimesAsync(allFiles, currentVersion);
      return;
    }
  }

  cacheInfoEl.textContent = "未命中";
  updateInfoEl.textContent = "-";

  try {
    const repoInfo = await fetchRepoInfo();
    repoMeta.branch = repoInfo.default_branch || fallbackBranch;
    branchInfoEl.textContent = repoMeta.branch;

    const tree = await fetchTree(repoMeta.branch);
    allFiles = normalizeFiles(tree);

    render(allFiles);
    cacheInfoEl.textContent = forceRefresh ? "已刷新" : "新列表";

    saveCache({
      branch: repoMeta.branch,
      files: allFiles
    });

    fillTimesAsync(allFiles, currentVersion);
  } catch (err) {
    contentAreaEl.innerHTML = `
      <div class="error">加载失败：${escapeHtml(err.message)}

请检查：
1. owner 和 repo 是否填写正确
2. 仓库是否公开
3. GitHub Pages 是否已开启
4. GitHub API 是否暂时限流</div>
    `;
    checkRateLimit();
  }
}

searchInputEl.addEventListener("input", () => {
  render(allFiles);
  timeFillVersion++;
  fillTimesAsync(allFiles, timeFillVersion);
});

typeFilterEl.addEventListener("change", () => {
  render(allFiles);
  timeFillVersion++;
  fillTimesAsync(allFiles, timeFillVersion);
});

sortSelectEl.addEventListener("change", () => {
  render(allFiles);
  timeFillVersion++;
  fillTimesAsync(allFiles, timeFillVersion);
});

refreshBtnEl.addEventListener("click", async () => {
  clearCache();
  await loadData(true);
});

checkRateBtnEl.addEventListener("click", async () => {
  await checkRateLimit();
});

initTheme();
bindThemeEvents();
checkRateLimit();
loadData();