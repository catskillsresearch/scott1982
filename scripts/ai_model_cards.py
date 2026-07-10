"""Model-card registry for the AI-assisted development acknowledgements block.

Injected into `arxiv_with_code.md` / `arxiv.tex` by `build_arxiv_tex.py` at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->
  <!-- AI_MODEL_REFERENCES --> … <!-- /AI_MODEL_REFERENCES -->

Because this development may borrow Lean and proof patterns from the sibling
formalizations (`scott1972`, `scott1980`), **every model listed here is treated
as used** for acknowledgement purposes, whether or not it was invoked in a
particular scott1982 session.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    reference: str


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor",
        cite_key="Cur26",
        tool_note=(
            "agent-assisted editing in the Cursor IDE: formalizing Scott's 1982 "
            "information-system layer in Lean 4 / mathlib, `lake build` repair, vision-OCR "
            "transcription of `sources/Domains_for_Denotational_Semantics.md`, drafting this "
            "narrative (`arxiv.md`), and tracking the formalized inventory. Generated Lean was "
            "provisional until it compiled under the pinned toolchain. Also used in the sibling "
            "formalizations whose portable work may be copied into this repo."
        ),
        reference=(
            "Anysphere, Inc. *Cursor: AI-native code editor and agent environment*. "
            "<https://cursor.com> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Cursor Composer 2.5 Fast",
        cite_key="Cmp25",
        tool_note=(
            "routine multi-step work: module scaffolding, dependency-ordered wiring of "
            "`Scott1982/`, documentation and Mermaid blueprints, medium proof obligations where "
            "the strategy was already fixed, and the triple-pass vision OCR pipeline "
            "(`composer-2.5`). Also used in sibling repos whose portable Lean may be adapted here."
        ),
        reference=(
            "Anysphere, Inc. *Composer 2.5*. Model announcement and documentation, "
            "<https://cursor.com/blog/composer-2-5>; model card as integrated in Cursor, "
            "<https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Cursor Grok 4.5",
        cite_key="Grk45",
        tool_note=(
            "primary agent model for the scott1982 information-systems formalization sessions: "
            "inventory design in `arxiv.md`, constructive `InfoSys` / `Approximable` Lean "
            "development, choice-free `Finset` discipline, and adaptation of portable patterns "
            "from prior Scott formalizations. Jointly trained by SpaceXAI and Cursor; used here "
            "via the Cursor agent environment."
        ),
        reference=(
            "SpaceXAI and Anysphere, Inc. *Grok 4.5*. Model documentation, "
            "<https://docs.x.ai/developers/models/grok-4.5>; Cursor announcement, "
            "<https://cursor.com/blog/grok-4-5> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Sonnet 5 (medium reasoning)",
        cite_key="Son26",
        tool_note=(
            "day-to-day formalization and proof-engineering in Cursor at the medium reasoning "
            "tier in sibling Scott formalizations (and available for this repo): inventory and "
            "narrative maintenance, module wiring, and medium-complexity Lean obligations where "
            "the proof strategy was already fixed. Listed because portable prior work may be "
            "copied into scott1982."
        ),
        reference=(
            "Anthropic. *Claude Sonnet 5* (medium reasoning variant). System card, "
            "<https://www.anthropic.com/claude-sonnet-5-system-card>; model documentation as "
            "integrated in Cursor, <https://cursor.com/docs/models> (accessed 2026)."
        ),
    ),
    ModelCard(
        label="Anthropic Claude Opus 4.8 (high reasoning)",
        cite_key="Ant26",
        tool_note=(
            "selective use for the heaviest proof work in sibling formalizations (e.g. continuous "
            "lattices and PRG-19). Every emitted proof term was checked by the Lean kernel. "
            "Listed because portable prior work may be copied into scott1982."
        ),
        reference=(
            "Anthropic. *Claude Opus 4.8* (high thinking/reasoning variant). System card and "
            "announcement, <https://www.anthropic.com/news/claude-opus-4-8>; model documentation "
            "as integrated in Cursor, <https://cursor.com/docs/models/claude-opus-4-8> "
            "(accessed 2026)."
        ),
    ),
    ModelCard(
        label="Google Gemini 3.5 Flash",
        cite_key="Gem25",
        tool_note=(
            "exploratory passes in sibling formalizations (typographic conventions, scope "
            "decisions). Listed because portable prior work may be copied into scott1982."
        ),
        reference=(
            "Google DeepMind. *Gemini 3.5 Flash*. Technical documentation and model cards. "
            "<https://ai.google.dev/gemini-api/docs/models> (accessed 2026)."
        ),
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"

# Acknowledgments live outside `arxiv.md` and are spliced in when building `arxiv.tex`.
ACKNOWLEDGMENTS_MARKDOWN = """## Acknowledgments

- **Dana Scott** — *Domains for Denotational Semantics* **[Sco82]**, the paper this development
  formalizes.

### AI-assisted development

The human author retains sole responsibility for the mathematical content, the choice of
formalization route, and every formal claim in this work. Following standard publisher practice
(e.g., COPE guidance on authorship and AI tools **[COPE24]**), **no large language model is listed
as a co-author** — authorship implies an accountability that automated systems cannot bear.

Because this development may borrow Lean and proof patterns from the sibling formalizations
[`scott1972`](https://github.com/catskillsresearch/scott1972) **[SR72]** and
[`scott1980`](https://github.com/catskillsresearch/scott1980) **[ER80]**, **every model in the
registry is treated as used** for acknowledgement purposes. We gratefully acknowledge assistance
from the following tools (auto-generated from `scripts/ai_model_cards.py` when building
`arxiv.tex`):

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

All definitions, constructivity audits, and final prose were reviewed by the human author, who takes
full responsibility for them.

### Artifact availability

The development is at
[`github.com/catskillsresearch/scott1982`](https://github.com/catskillsresearch/scott1982).
Run `lake build Scott1982` for the formalization; `scripts/generate_arxiv_with_code.sh`
builds `arxiv_with_code.md` from this file plus the Lean source.

"""


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** **[{card.cite_key}]** — {card.tool_note}" for card in MODEL_CARDS
    )


def render_model_references() -> str:
    return "\n".join(f"- **[{card.cite_key}]** {card.reference}" for card in MODEL_CARDS)


def inject_acknowledgments(text: str) -> str:
    """Insert the Acknowledgments section before References (skipped if already present)."""
    if re.search(r"^##\s+Acknowledgments\s*$", text, re.MULTILINE):
        return text
    m = re.search(r"^##\s+References\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError(
            "missing ## References in narrative; needed to place Acknowledgments before it"
        )
    return text[: m.start()] + ACKNOWLEDGMENTS_MARKDOWN + "\n" + text[m.start() :]


def inject_model_cards(text: str) -> str:
    """Insert Acknowledgments (if needed), then expand AI model-card markers."""
    text = inject_acknowledgments(text)
    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} after Acknowledgments injection"
        )
    if REFERENCES_BEGIN not in text:
        raise RuntimeError(
            f"missing {REFERENCES_BEGIN} in narrative; add markers to arxiv.md References"
        )

    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, render_model_references())
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    # Preserve one leading newline after begin marker when present.
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
