"""Fast repository checks that need no Lean toolchain (run by CI; takes a few seconds).

1. Every import of a local module resolves: the module belongs to a `lean_lib` of `lakefile.lean`
   (by its `globs`, or by its root name when `globs` is not set) and its file exists.
2. Nothing in the import closure of `TernaryGoldbach.MainTheorems` and `Solution` contains `sorry`,
   `admit`, `native_decide` or an `axiom` declaration (comments stripped). This is a source-level
   check; `#print axioms` after a build is the authoritative one.
3. Every file under `TernaryGoldbach/` is imported (directly or not) by `TernaryGoldbach.lean`, so
   the default `lake build` checks it.
4. `Challenge.lean` matches the code: its definitions are those of `TernaryGoldbach/Statement.lean`,
   its theorem statements those of `TernaryGoldbach/MainTheorems.lean`, and `comparator/config.json`
   names exactly its theorems.
5. The vendored RSBounds sources match `vendor/rsbounds/source-provenance.json`.
6. Every file path written in backticks in the Markdown docs exists.

Usage: python3 scripts/ci_checks.py   (from the repository root)"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
EXTERNAL = {"Init", "Lean", "Std", "Lake", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets",
            "Plausible", "ImportGraph", "LeanSearchClient"}
problems = []


def fail(check, msg):
    problems.append(f"[{check}] {msg}")


def strip_comments(t):
    """Remove Lean comments (nested `/- -/` and `--`) and string literals."""
    out, i, depth, n = [], 0, 0, len(t)
    while i < n:
        if t.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and t.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if t.startswith("--", i):
            j = t.find("\n", i); i = n if j < 0 else j; continue
        if t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(t[i]); i += 1
    return "".join(out)


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


# --- the libraries of lakefile.lean -------------------------------------------------------------
lakefile = open("lakefile.lean", encoding="utf8").read()
libs = []
for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?lean_lib\s+(\w+)(.*?)(?=^\S|\Z)", lakefile, re.M | re.S):
    name, body = m.group(1), m.group(2)
    src = re.search(r'srcDir\s*:=\s*"([^"]*)"', body)
    globs = re.search(r"globs\s*:=\s*#\[(.*?)\]", body, re.S)
    roots = re.search(r"roots\s*:=\s*#\[(.*?)\]", body, re.S)
    lib = {"name": name, "src": src.group(1) if src else ".",
           "roots": re.findall(r"`([\w.]+)", roots.group(1)) if roots else [name], "globs": None}
    if globs:
        lib["globs"] = [(kind or "one", mod) for kind, mod in
                        re.findall(r"(?:\.(one|submodules|andSubmodules)\s+)?`([\w.]+)", globs.group(1))]
    libs.append(lib)


def owner(mod):
    for lib in libs:
        if lib["globs"] is None:
            if any(mod == r or mod.startswith(r + ".") for r in lib["roots"]):
                return lib
        else:
            for kind, g in lib["globs"]:
                if ((kind in ("one", "andSubmodules") and mod == g)
                        or (kind in ("submodules", "andSubmodules") and mod.startswith(g + "."))):
                    return lib
    return None


def path_of(mod):
    lib = owner(mod)
    if lib is None:
        return None
    return os.path.normpath(os.path.join(lib["src"], *mod.split("."))) + ".lean"


# --- 1. imports resolve; build the import graph ---------------------------------------------------
files = subprocess.run(["git", "ls-files", "*.lean"], capture_output=True, text=True,
                       check=True).stdout.split()
local_roots = {r for lib in libs for r in lib["roots"]} | {g.split(".")[0] for lib in libs
                                                           for _, g in (lib["globs"] or [])}
imports = {}
for f in files:
    if f == "lakefile.lean":
        continue
    header = re.match(r"(?:\s*(?:prelude|module|(?:public\s+|meta\s+)*import\s+[\w.]+))*",
                      strip_comments(open(f, encoding="utf8").read())).group(0)
    imports[f] = re.findall(r"import\s+([\w.]+)", header)
    for mod in imports[f]:
        root = mod.split(".")[0]
        if root in EXTERNAL:
            continue
        if root not in local_roots:
            fail("imports", f"{f}: `import {mod}`: no library or dependency provides `{root}`")
            continue
        p = path_of(mod)
        if p is None:
            fail("imports", f"{f}: `import {mod}`: no `lean_lib` in lakefile.lean contains this module "
                            "(check its `globs`)")
        elif not os.path.exists(p):
            fail("imports", f"{f}: `import {mod}`: {p} does not exist")


def closure(start_files):
    seen, stack = set(), list(start_files)
    while stack:
        f = stack.pop()
        if f in seen or not os.path.exists(f):
            continue
        seen.add(f)
        for mod in imports.get(f, []):
            if mod.split(".")[0] not in EXTERNAL:
                p = path_of(mod)
                if p:
                    stack.append(p)
    return seen


# --- 2. no sorry / admit / native_decide / axiom in what the main theorems use -------------------
for f in sorted(closure(["TernaryGoldbach/MainTheorems.lean", "Solution.lean"])):
    t = strip_comments(open(f, encoding="utf8").read())
    for word in ("sorry", "admit", "native_decide"):
        if re.search(r"(?<![\w.'])" + word + r"(?![\w'])", t):
            fail("trust", f"{f} contains `{word}`")
    if re.search(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\s", t, re.M):
        fail("trust", f"{f} declares an `axiom`")

# --- 3. the default target covers every project file ---------------------------------------------
reached = closure(["TernaryGoldbach.lean"])
for f in files:
    if f.startswith("TernaryGoldbach/") and f not in reached:
        fail("coverage", f"{f} is not imported by TernaryGoldbach.lean, so `lake build` skips it")

# --- 4. Challenge.lean matches the code ------------------------------------------------------------
def decls(path, kind):
    t = strip_comments(open(path, encoding="utf8").read())
    out = {}
    for m in re.finditer(r"^" + kind + r"\s+([\w.']+)(.*?)(?=^\S)", t + "\nend", re.M | re.S):
        body = m.group(2)
        if kind == "theorem":
            body = body.split(":=")[0]
        out[m.group(1)] = norm(body)
    return out

ch_defs, st_defs = decls("Challenge.lean", "def"), decls("TernaryGoldbach/Statement.lean", "def")
for name, body in ch_defs.items():
    if st_defs.get(name) != body:
        fail("challenge", f"`{name}` in Challenge.lean differs from TernaryGoldbach/Statement.lean")
ch_thms, mt_thms = decls("Challenge.lean", "theorem"), decls("TernaryGoldbach/MainTheorems.lean", "theorem")
for name, sig in ch_thms.items():
    if mt_thms.get(name) != sig:
        fail("challenge", f"theorem `{name}` in Challenge.lean differs from TernaryGoldbach/MainTheorems.lean")
cfg = json.load(open("comparator/config.json"))
if sorted(n.removeprefix("TernaryGoldbach.") for n in cfg["theorem_names"]) != sorted(ch_thms):
    fail("challenge", "comparator/config.json does not name exactly the theorems of Challenge.lean")
if not ch_thms:
    fail("challenge", "no theorems found in Challenge.lean")

# --- 5. vendored sources unchanged ------------------------------------------------------------------
r = subprocess.run([sys.executable, "vendor/rsbounds/check_source_provenance.py"],
                   capture_output=True, text=True)
if r.returncode:
    fail("vendor", r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "provenance check failed")
    for line in r.stdout.splitlines()[:20]:
        if line.startswith(("MISMATCH", "UNLISTED")):
            fail("vendor", line)

# --- 6. file paths in the docs exist ---------------------------------------------------------------
tracked = set(subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split())
docs = ["README.md", "HYPOTHESES.md", "NOTES.md", "BLUEPRINT.md", "comparator/README.md",
        "scripts/rigorous/README.md"]
for d in docs:
    for ln, line in enumerate(open(d, encoding="utf8"), 1):
        for tok in re.findall(r"`([^`\s]+\.(?:lean|py|md|json|yaml|c|tmpl|sh))`", line):
            if "*" in tok or "–" in tok or tok.startswith("/"):
                continue
            if tok in tracked or any(t.endswith("/" + tok) for t in tracked):
                continue
            fail("docs", f"{d}:{ln}: `{tok}` does not exist")

if problems:
    print("\n".join(problems))
    print(f"\n{len(problems)} problem(s)")
    sys.exit(1)
print(f"all checks passed ({len(files)} Lean files, {len(libs)} libraries)")
