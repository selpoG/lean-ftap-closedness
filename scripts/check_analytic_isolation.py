#!/usr/bin/env python3
"""Rebuild the closedness argument without any stochastic implementation.

Requires a successful normal build. Signatures are exported from that build;
only the temporary Interface implementations are replaced by assumptions.
Unchanged shared definitions and closedness proofs are compiled from source.
Only third-party package caches are reused, never project build artifacts.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from check_structure import analytic_document_boundary

ROOT = Path(__file__).resolve().parents[1]


def run(work):
    work.mkdir(parents=True, exist_ok=True)
    if any(work.iterdir()):
        raise ValueError(f"The isolated build directory must be empty: {work}")
    for source in (ROOT / "FTAPTheorem42").rglob("*.lean"):
        relative = source.relative_to(ROOT)
        if relative.parts[1] == "Stochastic":
            continue
        target = work / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    for filename in ("FTAPTheorem42.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(ROOT / filename, work / filename)
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    export_env = dict(env, FTAP_INTERFACE_EXPORT=str(work / "FTAPTheorem42/Interface"))
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true",
                    "scripts/ExportAnalyticInterface.lean"],
                   cwd=ROOT, env=export_env, check=True)
    axioms = json.loads((work / "FTAPTheorem42/Interface/boundary.json").read_text())
    documented = set(analytic_document_boundary().values())
    if documented != set(axioms):
        raise ValueError(f"TeX/Lean boundary mismatch: undocumented={set(axioms) - documented}; "
                         f"not exported={documented - set(axioms)}")
    print(f"TeX/Lean boundary: all {len(axioms)} exported inputs match both languages", flush=True)
    for source in work.rglob("*.lean"):
        if "FTAPTheorem42.Stochastic" in source.read_text():
            raise ValueError(f"Implementation reference in isolated source: {source}")
    (work / ".lake").mkdir()
    (work / ".lake/packages").symlink_to((ROOT / ".lake/packages").resolve(), target_is_directory=True)
    search_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                          cwd=work, env=env, text=True)
    if str(ROOT / ".lake/build") in search_path:
        raise ValueError("Original project artifacts occur in the isolated search path")
    print(f"Isolated source: {work}; no Stochastic sources or project cache", flush=True)
    subprocess.run(["lake", "--wfail", "build"], cwd=work, env=env, check=True)
    if (work / ".lake/build/lib/lean/FTAPTheorem42/Stochastic").exists():
        raise ValueError("Stochastic artifacts were built in the isolated project")
    names = ",\n    ".join("``" + n for n in axioms)
    audit = """import FTAPTheorem42
open Lean Elab Command
#print axioms FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket
run_cmd do
  let boundary := [BOUNDARY]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ boundary
  let actual ← collectAxioms ``FTAPTheorem42.BoundedSourceIntegralMarket.theorem42_generalMarket
  for ax in actual do
    unless allowed.contains ax do throwError "Unexpected isolated-build axiom: {ax}"
  for ax in boundary do
    unless actual.contains ax do throwError "Unused interface assumption: {ax}"
  logInfo "Isolated theorem uses exactly the specified analytic boundary and standard axioms"
""".replace("BOUNDARY", names)
    (work / "AuditIsolation.lean").write_text(audit)
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "AuditIsolation.lean"],
                   cwd=work, env=env, check=True)
    print(f"OK: unchanged main proof rebuilt with {len(axioms)} analytic assumptions; "
          "no Stochastic sources or artifacts", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, help="retain an isolated build in this empty directory")
    args = parser.parse_args()
    if args.work_dir:
        run(args.work_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="ftap-analytic-isolation-") as temporary:
            run(Path(temporary))
