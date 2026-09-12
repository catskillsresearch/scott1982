#!/usr/bin/env bash
# Expand the Lean-module appendix into arxiv_with_code.md, then build arxiv.tex.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> Regenerating arxiv_with_code.md (Palomar-linked Lean module appendix)"
bash scripts/generate_arxiv_with_code.sh

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py
