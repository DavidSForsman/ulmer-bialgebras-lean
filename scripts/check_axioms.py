"""Print the axioms used by every theorem in `comparator.all.json` (or `comparator.json`), verify `permitted_axioms` equals the fixed standard set, and print a summary.

Usage: python3 scripts/check_axioms.py [--config PATH] [--check-config-only]
  (from the repository root, after `lake build`)
"""
import argparse, json, os, re, subprocess, sys, tempfile

EXPECTED_PERMITTED_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})


def validate_permitted_axioms(cfg):
    """Return an error string if `permitted_axioms` is not the fixed standard set, else None."""
    raw = cfg.get("permitted_axioms")
    if not isinstance(raw, list) or not all(isinstance(a, str) for a in raw):
        return f"INVALID permitted_axioms: expected list of strings, got {raw!r}"
    got = set(raw)
    if got != EXPECTED_PERMITTED_AXIOMS or len(raw) != len(got):
        return (
            f"INVALID permitted_axioms: got {sorted(raw)}, "
            f"expected exactly {sorted(EXPECTED_PERMITTED_AXIOMS)}"
        )
    return None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--config", help="path to comparator.json")
    ap.add_argument("--check-config-only", action="store_true",
                    help="validate permitted_axioms without invoking Lean")
    args = ap.parse_args(argv)

    default_cmp = "twin/ulmer/palomar/comparator.json"
    if not args.config and os.path.exists(default_cmp):
        sys.path.insert(0, "scripts/lib")
        from checked_lists import CONFIGS, all_names
        for _, rel in CONFIGS.items():
            if os.path.exists(rel):
                cfg_i = json.load(open(rel, encoding="utf-8"))
                err = validate_permitted_axioms(cfg_i)
                if err:
                    print(f"{rel}: {err}", file=sys.stderr)
                    return 1
        names = all_names()
    else:
        default_exported = ("comparator.all.json" if os.path.exists("comparator.all.json")
                            else "comparator.json")
        cmp_path = args.config or (default_cmp if os.path.exists(default_cmp) else default_exported)
        cfg = json.load(open(cmp_path, encoding="utf-8"))
        err = validate_permitted_axioms(cfg)
        if err:
            print(err, file=sys.stderr)
            return 1
        names = cfg["theorem_names"]

    if args.check_config_only:
        print(f"permitted_axioms OK: {sorted(EXPECTED_PERMITTED_AXIOMS)}")
        return 0

    allowed = set(EXPECTED_PERMITTED_AXIOMS)
    src = "import Companion.Proofs\n\n" + "".join(f"#print axioms {n}\n" for n in names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=".", delete=False) as f:
        f.write(src)
        path = f.name
    try:
        result = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
        out = result.stdout
    finally:
        os.remove(path)
    if result.returncode:
        print(out, end="")
        print(result.stderr, end="", file=sys.stderr)
        return result.returncode
    proved, open_, bad = [], [], []
    # Lean wraps long messages, so a report may span several lines: match across whitespace.
    for m in re.finditer(r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]", out):
        axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
        (open_ if "sorryAx" in axs else proved if axs <= allowed else bad).append(m.group(1))
    for m in re.finditer(r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", out):
        proved.append(m.group(1))
    print(f"{len(proved)} proved, {len(open_)} open (sorry), {len(bad)} with other axioms, of {len(names)}")
    for n in open_:
        print("  open:", n)
    for n in bad:
        print("  NON-STANDARD AXIOMS:", n)
    reported = proved + open_ + bad
    missing = sorted(set(names) - set(reported))
    for n in missing:
        print("  MISSING AXIOM REPORT:", n)
    if len(reported) != len(set(reported)):
        print("  DUPLICATE AXIOM REPORTS")
    return 1 if bad or open_ or missing or len(reported) != len(names) else 0


if __name__ == "__main__":
    sys.exit(main())
