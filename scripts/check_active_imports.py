#!/usr/bin/env python3
"""Check local Lean imports and reject retired modules without trusting cached oleans."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^(?:public\s+)?import\s+([\w.]+)", re.MULTILINE)
RETIRED = {"ComputingLanguage", "CheckedSemantics", "SubstSemantics", "TrinitaryCC", "FeltPass"}


def check_imports():
    # Inspect tests as well: an old olean must not conceal a deleted source import.
    sources = [ROOT / "Heyting.lean", ROOT / "Main.lean"]
    sources += sorted((ROOT / "Heyting").rglob("*.lean"))
    sources += sorted((ROOT / "tests").rglob("*.lean"))
    for source in sources:
        for dep in IMPORT.findall(source.read_text()):
            if dep == "Heyting" or dep.startswith("Heyting."):
                path = ROOT / (dep.replace(".", "/") + ".lean")
                if not path.is_file():
                    raise SystemExit(f"Missing source import: {source.relative_to(ROOT)} -> {dep}")
    pending = [(name, [name]) for name in ("Heyting", "Main")]
    seen = set()
    while pending:
        name, chain = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if "FlatIR" in name or "StructIR" in name or name.split(".")[-1] in RETIRED:
            raise SystemExit("Legacy dependency: " + " -> ".join(chain))
        path = ROOT / (name.replace(".", "/") + ".lean")
        if path.is_file():
            pending.extend((dep, chain + [dep]) for dep in IMPORT.findall(path.read_text()))
    print("Local source/test imports resolve; active imports exclude retired compiler modules.")


if __name__ == "__main__":
    check_imports()
