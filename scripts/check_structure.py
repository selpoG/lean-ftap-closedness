#!/usr/bin/env python3
"""Check the public import closure and mathematical documentation references."""

import re
import sys
from collections import Counter
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^import[ \t]+(FTAPTheorem42(?:\.[A-Za-z0-9_]+)*)[ \t]*$", re.M)


def analytic_document_boundary():
    """Check the bilingual clause map and forbid appendix bypasses in the main text.

    The isolation build additionally compares the returned declaration names
    with its exported Lean signatures. This checks references, not prose semantics.
    """
    maps = []
    main_names = ("setting", "terminal-compactness", "process-compactness",
                  "component-estimates", "realization", "fatou-weakstar")
    for language in ("proof.ja", "proof"):
        directory = ROOT / "docs" / language
        source = (directory / "integral-domain.tex").read_text()
        clauses = re.findall(r"\\analyticcontract\{([^}]+)\}\{([^}]+)\}", source)
        mapping = dict(clauses)
        if len(mapping) != len(clauses) or len(set(mapping.values())) != len(clauses):
            raise ValueError(f"Duplicate analytic clause or declaration: {language}")
        if not mapping:
            raise ValueError(f"Missing analytic boundary: {language}")
        table = (directory / "appendix/lean-declarations.tex").read_text()
        rows = re.findall(r"\\contractref\{([^}]+)\} & \\path\{([^}]+)\}", table)
        if dict(rows) != mapping or len(rows) != len(mapping):
            raise ValueError(f"Analytic correspondence table differs from inputs: {language}")
        appendix_labels = set()
        for chapter in (directory / "construction").glob("*.tex"):
            appendix_labels.update(re.findall(r"\\label\{([^}]+)\}", chapter.read_text()))
        appendix_labels.update(re.findall(r"\\label\{([^}]+)\}",
                                           (directory / "stochastic-construction.tex").read_text()))
        for name in main_names:
            chapter = directory / (name + ".tex")
            text = chapter.read_text()
            bypasses = appendix_labels.intersection(re.findall(r"\\(?:eq)?ref\{([^}]+)\}", text))
            if bypasses:
                raise ValueError(f"Main proof bypasses analytic inputs: {chapter}: {sorted(bypasses)}")
        for chapter in directory.rglob("*.tex"):
            unknown = set(re.findall(r"\\contractref\{([^}]+)\}", chapter.read_text())) - mapping.keys()
            if unknown:
                raise ValueError(f"Unknown analytic clause: {chapter}: {sorted(unknown)}")
        maps.append(mapping)
    if maps[0] != maps[1]:
        raise ValueError("Japanese and English analytic input maps differ")
    return maps[0]


def header_imports(source):
    """Read imports before the first body command, skipping nested comments."""
    pos = 0
    while pos < len(source):
        if source[pos].isspace():
            pos += 1
        elif source.startswith("--", pos):
            end = source.find("\n", pos)
            pos = len(source) if end < 0 else end + 1
        elif source.startswith("/-", pos):
            depth = 1
            pos += 2
            while pos < len(source) and depth:
                if source.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif source.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
        else:
            match = re.match(r"import[ \t]+([^\s]+)", source[pos:])
            if not match:
                return
            yield match[1]
            pos += match.end()


def check():
    errors = []
    try:
        boundary = analytic_document_boundary()
        print(f"Bilingual analytic boundary: {len(boundary)} entries; no main-text appendix bypass")
    except ValueError as error:
        errors.append(str(error))
    paths = sorted((ROOT / "FTAPTheorem42").rglob("*.lean"))
    paths.append(ROOT / "FTAPTheorem42.lean")
    modules = {str(p.relative_to(ROOT).with_suffix("")).replace("/", "."): p for p in paths}
    graph = {m: IMPORT.findall(p.read_text()) for m, p in modules.items()}
    aggregates = {m for m, p in modules.items()
                  if m.startswith("FTAPTheorem42.Stochastic") and p.with_suffix("").is_dir()}
    for module, imports in graph.items():
        for imported in imports:
            if imported not in modules:
                errors.append(f"Missing local import: {module} -> {imported}")
            if module == "FTAPTheorem42.Main" or module.startswith(("FTAPTheorem42.Closedness.", "FTAPTheorem42.Proof.")):
                if imported.startswith("FTAPTheorem42.Stochastic."):
                    errors.append(f"Closedness bypasses the analytic interface: {module} -> {imported}")
            if module.startswith("FTAPTheorem42.Foundations."):
                if imported.startswith(("FTAPTheorem42.Stochastic.", "FTAPTheorem42.Interface.",
                                        "FTAPTheorem42.Closedness.", "FTAPTheorem42.Proof.")) or imported == "FTAPTheorem42.Main":
                    errors.append(f"Shared foundations import analytic implementation: {module} -> {imported}")
            if module.startswith(("FTAPTheorem42.Stochastic.", "FTAPTheorem42.Interface.")):
                if imported == "FTAPTheorem42.Main" or imported.startswith(("FTAPTheorem42.Closedness.", "FTAPTheorem42.Proof.")):
                    errors.append(f"Analytic layer imports its consumer: {module} -> {imported}")
            if module.startswith("FTAPTheorem42.Stochastic."):
                if module not in aggregates and imported in aggregates:
                    errors.append(f"Leaf imports an aggregate: {module} -> {imported}")
        if module in aggregates:
            text = re.sub(r"/-.*?-/", "", modules[module].read_text(), flags=re.S)
            text = re.sub(r"--[^\n]*", "", text)
            if any(line.strip() and not line.startswith("import ") for line in text.splitlines()):
                errors.append(f"Declarations in aggregate: {module}")

    for directory in sorted(p for p in (ROOT / "FTAPTheorem42").rglob("*") if p.is_dir()):
        children = list(directory.iterdir())
        if len(children) < 2:
            errors.append(f"Redundant source directory: {directory.relative_to(ROOT)} "
                          f"({len(children)} children)")
    for path in paths:
        if len(path.stem) > 64:
            errors.append(f"Overlong module filename: {path.relative_to(ROOT)}")
        source = path.read_text()
        for imported, count in Counter(header_imports(source)).items():
            if count > 1:
                errors.append(f"Duplicate import: {path.relative_to(ROOT)} -> {imported}")
        for match in re.finditer(r"\n(?:[ \t]*\n){2,}", source):
            line = source.count("\n", 0, match.start()) + 2
            errors.append(f"Repeated blank lines: {path.relative_to(ROOT)}:{line}")

    active, seen = set(), set()

    def visit(module):
        if module in active:
            errors.append(f"Import cycle at {module}")
            return
        if module in seen or module not in graph:
            return
        active.add(module)
        for imported in graph[module]:
            visit(imported)
        active.remove(module)
        seen.add(module)

    visit("FTAPTheorem42")
    unreachable = set(modules) - seen
    for module in sorted(unreachable):
        errors.append(f"Module outside the public import closure: {module}")
        visit(module)
    for script in (ROOT / "scripts").glob("*.lean"):
        for imported in IMPORT.findall(script.read_text()):
            if imported not in modules:
                errors.append(f"Missing script import: {script.name} -> {imported}")

    leaf_counts = Counter(str(p.parent.relative_to(ROOT)) for m, p in modules.items()
                          if m.startswith("FTAPTheorem42.Stochastic.") and m not in aggregates)
    for directory, count in leaf_counts.items():
        if directory == "FTAPTheorem42/Stochastic" or count > 64:
            errors.append(f"Review flat directory: {directory} ({count} leaves)")

    documents = list(ROOT.glob("*.md")) + list((ROOT / "docs").rglob("*.md"))
    links = 0
    for doc in documents:
        for target in re.findall(r"\[[^\]\n]*\]\(([^)\n]+)\)", doc.read_text()):
            target = target.strip().strip("<>")
            url = urlsplit(target)
            if url.scheme or url.netloc:
                continue
            dest = (doc.parent / unquote(url.path)).resolve() if url.path else doc
            links += 1
            if not dest.exists():
                errors.append(f"Broken document link: {doc.relative_to(ROOT)} -> {target}")
            elif url.fragment and dest.suffix == ".md":
                headings = re.findall(r"^#+\s+(.+)$", dest.read_text(), re.M)
                anchors = {re.sub(r"[^\w\- ]", "", h.lower()).replace(" ", "-") for h in headings}
                if unquote(url.fragment) not in anchors:
                    errors.append(f"Missing heading: {doc.relative_to(ROOT)} -> {target}")

    inputs = set()
    masters = [ROOT / "docs/proof.ja.tex", ROOT / "docs/proof.tex"]
    chapters = list((ROOT / "docs/proof.ja").rglob("*.tex")) + list((ROOT / "docs/proof").rglob("*.tex"))
    tex_files = masters + chapters
    for tex in tex_files:
        for target in re.findall(r"\\input\{([^}]+)\}", tex.read_text()):
            dest = ROOT / target
            inputs.add(dest)
            if not dest.is_file():
                errors.append(f"Missing TeX input: {target}")
    for tex in chapters:
        if tex not in inputs:
            errors.append(f"Unused TeX chapter: {tex.relative_to(ROOT)}")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"OK: {len(modules)} modules, {len(aggregates)} stochastic aggregates, "
          f"{links} document links, {len(chapters)} TeX chapters")
    print(f"Largest stochastic leaf directory: {max(leaf_counts.values(), default=0)} files")
    print("Source declaration counts and import neighbors: "
          "check_declaration_closure.py --module-report PATH (after build)")
    return 0


if __name__ == "__main__":
    sys.exit(check())
