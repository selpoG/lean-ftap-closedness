#!/usr/bin/env python3
"""Reject source declarations outside the main theorem's proof dependency closure.

Run `lake build` first. Lean supplies the transitive type/opaque-value closure;
.ilean files supply exact source ranges. Structures, instances, and `where`
helpers are grouped with their originating source declaration: Lean necessarily
generates some unused projections, recursors, and equation lemmas for them.
"""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def check_documented_declarations(declarations, documents):
    """Every qualified declaration in the TeX correspondence table must be used."""
    by_name = {declaration["name"]: declaration for declaration in declarations}
    referenced = set()
    errors = []
    for document in documents:
        for name in re.findall(r"\\path\{(FTAPTheorem42\.[^}]+)\}", document.read_text()):
            referenced.add(name)
            if name not in by_name:
                errors.append(f"Unknown documented declaration: {document.name}: {name}")
            elif not by_name[name]["used"]:
                errors.append(f"Documented declaration outside main proof: {document.name}: {name}")
    if not referenced:
        errors.append("No qualified Lean declarations found in the mathematical documentation")
    if errors:
        raise ValueError("\n".join(errors))
    print(f"Verified {len(referenced)} mathematical-document declaration references")


def check(module_report=None):
    with tempfile.TemporaryDirectory(prefix="ftap-declaration-audit-") as work:
        output = Path(work) / "declarations.json"
        env = dict(os.environ, FTAP_DECLARATION_AUDIT_OUTPUT=str(output))
        subprocess.run(["lake", "env", "lean", "scripts/AuditMainTheorem.lean"],
                       cwd=ROOT, env=env, check=True)
        declarations = json.loads(output.read_text())

    for language in ("proof.ja", "proof"):
        check_documented_declarations(declarations, (ROOT / "docs" / language).rglob("*.tex"))

    groups, owners = [], {}
    sources = sorted((ROOT / "FTAPTheorem42").rglob("*.lean")) + [ROOT / "FTAPTheorem42.lean"]
    for source in sources:
        relative = source.relative_to(ROOT)
        artifact = ROOT / ".lake/build/lib/lean" / relative.with_suffix(".ilean")
        data = json.loads(artifact.read_text())
        expected_module = str(relative.with_suffix("")).replace("/", ".")
        if data["module"] != expected_module:
            raise ValueError(f"Wrong build artifact: {artifact}")
        line_count = len(source.read_text().splitlines())
        entries = sorted(data["decls"].items(), key=lambda item: item[1][:4])
        local = []
        for name, span in entries:
            start, end = tuple(span[:2]), tuple(span[2:4])
            if end[0] >= line_count:
                raise ValueError(f"Stale build artifact: run lake build ({relative})")
            if local and start < groups[local[-1]]["end"]:
                group = groups[local[-1]]
                group["end"] = max(group["end"], end)
            else:
                local.append(len(groups))
                groups.append(dict(file=str(relative), start=start, end=end, names=[]))
            groups[local[-1]]["names"].append(name)
            owners[name] = local[-1]

    def owner(name):
        # Generated proofs/equations are children of the declaration that creates them.
        current = name
        while current:
            if current in owners:
                return owners[current]
            current = current.rpartition(".")[0]
        # Some match auxiliaries are private even when their source definition is public.
        if name.startswith("_private."):
            parts = name.split(".")
            for index, part in enumerate(parts):
                if part.isdecimal():
                    return owner(".".join(parts[index + 1:]))
        return None

    used, unmapped = set(), []
    for declaration in declarations:
        if not declaration["used"]:
            continue
        group = owner(declaration["name"])
        if group is None:
            unmapped.append(declaration["name"])
        else:
            used.add(group)
    unused = [group for i, group in enumerate(groups) if i not in used]
    for name in unmapped:
        print(f"Cannot locate proof dependency: {name}", file=sys.stderr)
    for group in unused:
        print(f"Unused source declaration: {group['file']}:{group['start'][0] + 1}: "
              f"{group['names'][0]}", file=sys.stderr)
    if unmapped or unused:
        return 1
    counts = Counter(group["file"] for group in groups)
    imports = {}
    for source in sources:
        relative = source.relative_to(ROOT)
        module = str(relative.with_suffix("")).replace("/", ".")
        imports[module] = re.findall(r"^import (FTAPTheorem42\S*)$",
                                     source.read_text(), re.M)
    report = []
    for source in sources:
        relative = source.relative_to(ROOT)
        module = str(relative.with_suffix("")).replace("/", ".")
        report.append(dict(file=str(relative), lines=len(source.read_text().splitlines()),
                           source_declarations=counts[str(relative)],
                           imports=imports[module],
                           importers=sorted(m for m, deps in imports.items() if module in deps)))
    internal = [row for row in report if row["file"] != "FTAPTheorem42.lean"]
    print(f"Module review indicators: {sum(row['lines'] <= 100 for row in internal)} "
          f"at most 100 lines; "
          f"{sum(row['source_declarations'] == 1 for row in internal)} "
          f"with one source declaration (not rejection criteria)")
    if module_report is not None:
        Path(module_report).write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"OK: all {len(groups)} source declaration groups contribute to the main proof; "
          f"{sum(d['used'] for d in declarations)} transitive project dependencies")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module-report", metavar="PATH",
                        help="write JSON with source declaration counts, lines and import neighbors")
    sys.exit(check(parser.parse_args().module_report))
