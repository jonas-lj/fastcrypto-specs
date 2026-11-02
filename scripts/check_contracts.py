#!/usr/bin/env python3
"""Check that every contract has an entry in its folder's `checks.toml`, and vice versa.

A contract is a field of a structure whose name ends in `Contracts`, in a `.lean` file under
`FastcryptoSpecs/<Folder>/`. The entries record which fastcrypto revision each contract was checked
against; see STYLE.md.
"""
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "FastcryptoSpecs"
STRUCTURE = re.compile(r"^structure (\w*Contracts)\b")
FIELD = re.compile(r"^  (\w+) :")


def contracts(folder: Path) -> set[str]:
    names = set()
    for lean in sorted(folder.glob("*.lean")):
        inside = False
        for line in lean.read_text().splitlines():
            if STRUCTURE.match(line):
                inside = True
            elif line and not line[0].isspace():
                inside = False
            elif inside and (m := FIELD.match(line)):
                names.add(m.group(1))
    return names


def main() -> int:
    ok = True
    for folder in sorted(p for p in ROOT.iterdir() if p.is_dir()):
        names = contracts(folder)
        if not names:
            continue
        checks = folder / "checks.toml"
        listed = set(tomllib.loads(checks.read_text())) if checks.exists() else set()
        for name in sorted(names - listed):
            print(f"{checks}: missing entry for contract `{name}`")
            ok = False
        for name in sorted(listed - names):
            print(f"{checks}: entry `{name}` is not a contract")
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
