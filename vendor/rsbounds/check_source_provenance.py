"""Check the vendored RSBounds sources against source-provenance.json (SHA-256 of every file).

Usage: python3 vendor/rsbounds/check_source_provenance.py"""
import hashlib, json, os, sys
here = os.path.dirname(os.path.abspath(__file__))
man = json.load(open(os.path.join(here, "source-provenance.json")))
bad = 0
for f in man["files"]:
    p = os.path.join(here, f["vendored"])
    if not os.path.exists(p) or hashlib.sha256(open(p, "rb").read()).hexdigest() != f["sha256"]:
        print("MISMATCH", f["vendored"]); bad += 1
listed = {f["vendored"] for f in man["files"]}
for root, _, names in os.walk(here):
    for n in names:
        if n.endswith(".lean"):
            rel = os.path.relpath(os.path.join(root, n), here)
            if rel not in listed:
                print("UNLISTED", rel); bad += 1
print(f"{len(man['files'])} files, {bad} problems")
sys.exit(1 if bad else 0)
