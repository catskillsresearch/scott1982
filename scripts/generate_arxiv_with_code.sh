#!/usr/bin/env bash
# Optional: expand Lean Code GitHub links into arxiv_with_code.md (local review only).
# The arXiv pipeline does NOT use this file — see scripts/build_arxiv_tex.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_arxiv_with_code.py
