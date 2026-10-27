#!/usr/bin/env python3
"""Build the current manuscript as build/Main.pdf with a configured TeX installation."""

from pathlib import Path
import argparse
import shutil
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    root = Path(__file__).resolve().parent
    missing = [name for name in ("latexmk", "pdflatex", "bibtex")
               if shutil.which(name) is None]
    if missing:
        print("Missing TeX tools: " + ", ".join(missing), file=sys.stderr)
        print("Install a configured TeX distribution with latexmk, IEEEtran, "
              "TikZ/PGFPlots and the LaTeX packages used by Main.tex. "
              "See docs/REPRODUCING.md.", file=sys.stderr)
        return 1
    result = subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
         "-outdir=build", "Main.tex"],
        cwd=root,
        check=False,
    )
    if result.returncode:
        print("Manuscript build failed; see the TeX output above and "
              "build/Main.log if available. Check that your TeX installation "
              "includes IEEEtran, TikZ/PGFPlots and the required packages.",
              file=sys.stderr)
        return result.returncode
    output = root / "build" / "Main.pdf"
    if not output.is_file() or not output.stat().st_size:
        print("TeX finished without producing build/Main.pdf.", file=sys.stderr)
        return 1
    print(f"Built {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
