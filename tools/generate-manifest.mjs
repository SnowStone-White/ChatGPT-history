import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const repoRoot = process.cwd();
const repoSlug = process.env.GITHUB_REPOSITORY || "";
const [owner = "", repo = path.basename(repoRoot)] = repoSlug.split("/");
const branch =
  process.env.GITHUB_REF_NAME ||
  safeGit(["rev-parse", "--abbrev-ref", "HEAD"]) ||
  "main";

const manifestFile = path.join(repoRoot, "manifest.json");
const versionFile = path.join(repoRoot, "version.json");

const EXCLUDE_PATHS = new Set([
  "manifest.json",
  "version.json",
]);

const EXCLUDE_PREFIXES = [
  ".git/",
  "node_modules/",
];

const SITE_SELF_FILES = new Set([
  "index.html",
  "style.css",
  "script.js",
]);

function safeGit(args) {
  try {
    return execFileSync("git", args, {
      cwd: repoRoot,
      encoding: "utf8",
    }).trim();
  } catch {
    return "";
  }
}

function getTrackedFiles() {
  const output = safeGit(["ls-files"]);
  if (!output) return [];
  return output
    .split(/\r?\n/)
    .map((s) => s.trim())
    .filter(Boolean);
}

function shouldExclude(relPath) {
  if (EXCLUDE_PATHS.has(relPath)) return true;
  if (SITE_SELF_FILES.has(relPath)) return true;
  return EXCLUDE_PREFIXES.some((prefix) => relPath.startsWith(prefix));
}

function getExtension(relPath) {
  const ext = path.extname(relPath || "").toLowerCase();
  return ext.startsWith(".") ? ext.slice(1) : ext;
}

function getFileType(relPath) {
  const ext = getExtension(relPath);
  if (["html", "htm"].includes(ext)) return "html";
  if (["pdf"].includes(ext)) return "pdf";
  if (["png", "jpg", "jpeg", "gif", "webp", "svg", "bmp", "ico", "avif"].includes(ext)) return "image";
  if (["md", "txt", "json", "csv", "xml", "yml", "yaml"].includes(ext)) return "text";
  if (["js", "ts", "jsx", "tsx", "py", "java", "c", "cpp", "h", "hpp", "cs", "go", "rs", "php", "rb", "sh", "bat", "ps1", "css", "scss", "sql"].includes(ext)) return "code";
  if (["zip", "rar", "7z", "tar", "gz"].includes(ext)) return "archive";
  return "other";
}

function getLastModified(relPath) {
  const value = safeGit(["log", "-1", "--format=%cI", "--", relPath]);
  return value || null;
}

function getSha(relPath) {
  const value = safeGit(["rev-list", "-1", "HEAD", "--", relPath]);
  return value || "";
}

function getLatestCommit() {
  return safeGit(["rev-parse", "HEAD"]) || "";
}

function generateManifestData() {
  const files = getTrackedFiles()
    .filter((relPath) => !shouldExclude(relPath))
    .map((relPath) => {
      const absPath = path.join(repoRoot, relPath);
      const stat = fs.statSync(absPath);

      return {
        path: relPath.replace(/\\/g, "/"),
        name: path.basename(relPath),
        size: stat.size,
        type: getFileType(relPath),
        lastModified: getLastModified(relPath),
        sha: getSha(relPath),
      };
    })
    .sort((a, b) => a.path.localeCompare(b.path, "zh-CN"));

  const generatedAt = new Date().toISOString();
  const latestCommit = getLatestCommit();

  const manifest = {
    owner,
    repo,
    branch,
    generatedAt,
    latestCommit,
    files,
  };

  const version = {
    owner,
    repo,
    branch,
    generatedAt,
    latestCommit,
    filesCount: files.length,
    source: "github-actions",
  };

  return { manifest, version };
}

function writeJson(filePath, data) {
  fs.writeFileSync(filePath, JSON.stringify(data, null, 2) + "\n", "utf8");
}

const { manifest, version } = generateManifestData();

writeJson(manifestFile, manifest);
writeJson(versionFile, version);

console.log(`manifest.json generated with ${manifest.files.length} files.`);
console.log(`version.json generated at ${version.generatedAt}.`);