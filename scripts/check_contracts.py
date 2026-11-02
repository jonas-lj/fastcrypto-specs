#!/usr/bin/env python3
"""Check that every contract has an entry in its folder's `checks.toml`, and vice versa, and warn
about contracts that have not been checked yet.

A contract is a field of a structure whose name ends in `Contracts`, in a `.lean` file under
`FastcryptoSpecs/<Folder>/`. The entries record which fastcrypto revision each contract was checked
against; see STYLE.md. A mismatch fails; an unchecked contract (an entry without a `fastcrypto`
revision) only gives a warning, shown as a GitHub annotation in CI.
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


def entry_line(checks: Path, name: str) -> int:
    for number, line in enumerate(checks.read_text().splitlines(), start=1):
        if line.strip() == f"[{name}]":
            return number
    return 1


def main() -> int:
    ok = True
    unchecked = 0
    for folder in sorted(p for p in ROOT.iterdir() if p.is_dir()):
        names = contracts(folder)
        if not names:
            continue
        checks = folder / "checks.toml"
        entries = tomllib.loads(checks.read_text()) if checks.exists() else {}
        listed = set(entries)
        for name in sorted(names - listed):
            print(f"{checks}: missing entry for contract `{name}`")
            ok = False
        for name in sorted(listed - names):
            print(f"{checks}: entry `{name}` is not a contract")
            ok = False
        for name in sorted(names & listed):
            if "fastcrypto" not in entries[name]:
                path = checks.relative_to(ROOT.parent)
                print(f"::warning file={path},line={entry_line(checks, name)}::"
                      f"Contract `{name}` has not been checked against fastcrypto")
                unchecked += 1
    print(f"{unchecked} contract(s) not checked yet")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
