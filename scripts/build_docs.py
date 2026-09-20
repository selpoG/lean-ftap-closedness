#!/usr/bin/env python3
"""Build both proof PDFs and reject unresolved references or box warnings."""

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "docs/build"


def check_log(text):
    problems = re.findall(
        r"^.*(?:Overfull \\[hv]box|Underfull \\[hv]box|"
        r"LaTeX Warning:.*(?:undefined|multiply defined|Rerun)|"
        r"Package \S+ Warning:.*(?:Rerun|Token not allowed)|"
        r"Rerun to get|Rerun LaTeX|Please .*rerun|"
        r"Missing character:).*$", text, re.M)
    if problems:
        raise ValueError("TeX diagnostics:\n" + "\n".join(problems))


def run_logged(command, log):
    with log.open("w") as stdout:
        try:
            subprocess.run(command, cwd=ROOT, stdout=stdout,
                           stderr=subprocess.STDOUT, check=True)
        except subprocess.CalledProcessError:
            stdout.flush()
            print("\n".join(log.read_text(errors="replace").splitlines()[-60:]),
                  file=sys.stderr)
            raise


def build(language, output_directory):
    japanese = language == "ja"
    engine = "uplatex" if japanese else "pdflatex"
    for executable in ((engine, "dvipdfmx") if japanese else (engine,)):
        if shutil.which(executable) is None:
            raise ValueError(f"Required executable not found: {executable}")
    work = BUILD / language
    work.mkdir(parents=True, exist_ok=True)
    stem = "proof.ja" if japanese else "proof"
    for iteration in range(1, 4):
        run_logged([engine, "-interaction=nonstopmode", "-halt-on-error",
                    "-file-line-error", f"-output-directory={work}",
                    f"docs/{stem}.tex"], work / f"{engine}-{iteration}.stdout.log")
    check_log((work / f"{stem}.log").read_text(errors="replace"))
    generated = work / f"{stem}.pdf"
    if japanese:
        run_logged(["dvipdfmx", "-o", str(generated), str(work / f"{stem}.dvi")],
                   work / "dvipdfmx.stdout.log")
    output = (output_directory / f"{stem}.pdf").resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    if output != generated.resolve():
        shutil.copyfile(generated, output)
    print(f"OK: {output}; final TeX log has no reference or box warnings")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--language", choices=("ja", "en", "all"), default="all")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "docs",
                        help="PDF destination directory (default: docs)")
    args = parser.parse_args()
    try:
        for language in (("ja", "en") if args.language == "all" else (args.language,)):
            build(language, args.output_dir)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"{error}\nBuild logs: {BUILD}", file=sys.stderr)
        sys.exit(1)
