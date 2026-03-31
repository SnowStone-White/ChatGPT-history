import fs from "node:fs";
import path from "node:path";
import { execSync } from "node:child_process";

const repoRoot = process.cwd();
const outputFile = path.join(repoRoot, "manifest.json");

const EXCLUDE_PATHS = new Set([
  "manifest.json",
]);

const EXCLUDE_PREFIXES = [
  ".git/",
  "node_modules/",
  ".github/",   // 不想展示工作流的话保留；想展示就删掉这一行
];

const SITE_SELF_FILES = new Set([
  "index.html",
  "style.css",
  "script.js",
  "index.manifest.html",
  "script.old.js",
]);

function normalizeToPosix(p) {
  return p.split(path.sep).join("/");
}

function shouldExclude(relPath) {
  const p = normalizeToPosix(relPath);

  if (!p) return true;
  if (EXCLUDE_PATHS.has(p)) return true;
  if (SITE_SELF_FILES.has(p)) return true;
  if (EXCLUDE_PREFIXES.some(prefix => p.startsWith(prefix))) return true;

  return false;
}

function getTrackedFiles() {
  const raw = execSync("git ls-files -z", {
    cwd: repoRoot,
    encoding: "utf8",
    stdio: ["ignore", "pipe", "pipe"],
  });

  return raw
    .split("\0")
    .map(s => s.trim())
    .filter(Boolean)
    .map(p => p.replace(/^"(.*)"$/, "$1")); // 防御性去掉整串外层引号
}

function getFileType(relPath) {
  const ext = path.extname(relPath).toLowerCase();

  if ([".html", ".htm"].includes(ext)) return "html";
  if ([".pdf"].includes(ext)) return "pdf";
  if ([".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".bmp", ".ico", ".avif"].includes(ext)) return "image";
  if ([".md", ".txt", ".json", ".csv", ".xml", ".yml", ".yaml"].includes(ext)) return "text";
  if ([".js", ".mjs", ".ts", ".jsx", ".tsx", ".py", ".java", ".c", ".cpp", ".h", ".hpp", ".cs", ".go", ".rs", ".php", ".rb", ".sh", ".bat", ".ps1", ".css", ".scss", ".sql"].includes(ext)) return "code";
  if ([".zip", ".rar", ".7z", ".tar", ".gz"].includes(ext)) return "archive";

  return "other";
}

function getLastCommitTime(relPath) {
  try {
    const safePath = relPath.replace(/"/g, '\\"');
    const raw = execSync(`git log -1 --format=%cI -- "${safePath}"`, {
      cwd: repoRoot,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();

    return raw || null;
  } catch {
    return null;
  }
}

function generateManifest() {
  const files = getTrackedFiles()
    .filter(relPath => !shouldExclude(relPath))
    .map(relPath => {
      const fullPath = path.join(repoRoot, relPath);
      const stats = fs.statSync(fullPath);

      return {
        path: normalizeToPosix(relPath),
        name: path.basename(relPath),
        size: stats.size,
        type: getFileType(relPath),
        lastModified: getLastCommitTime(relPath),
      };
    })
    .sort((a, b) => a.path.localeCompare(b.path, "zh-CN"));

  const manifest = {
    generatedAt: new Date().toISOString(),
    files,
  };

  fs.writeFileSync(outputFile, JSON.stringify(manifest, null, 2), "utf8");
  console.log(`manifest.json generated: ${files.length} files`);
}

generateManifest();
