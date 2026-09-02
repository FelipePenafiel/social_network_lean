#!/usr/bin/env python3
"""Generate ``STATUS.md``: how far the formalisation has got, and what resists it.

The blueprint (``blueprint/src/content.tex``) is the single source of truth.  Each
numbered statement of arXiv:2607.19651 is a node there, carrying

* ``\\lean{...}``  the Lean declarations that are its counterpart,
* ``\\leanok`` on the statement  the statement is written in Lean,
* ``\\leanok`` on the proof      the proof is written in Lean,
* ``\\uses{...}``                what the proof rests on.

A proof does not have to wait for its ancestors here: a written proof whose upstream
lemmas still carry a ``sorry`` compiles, inherits ``sorryAx``, and turns green the
moment they do.  So *proof written* and *proved* are different questions, and this
script keeps them apart: a node is **proved** when its own proof is written and every
node it uses is proved, which is the transitive closure ``leanblueprint`` itself draws
the dependency graph with.

Run ``python3 scripts/status.py`` to rewrite ``STATUS.md``, or
``python3 scripts/status.py --check`` to verify it is current — that is what CI runs.
Neither needs a Lean toolchain or a compiled project.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CONTENT = REPO / "blueprint" / "src" / "content.tex"
SOURCES = REPO / "SocialNetwork"
OUTPUT = REPO / "STATUS.md"

ENVIRONMENTS = ("theorem", "proposition", "lemma", "corollary", "definition", "remark")

# ---------------------------------------------------------------------------
# Why a node is not proved.  Keyed by blueprint label; the text is the one-line
# summary, and the section is the entry in FOR-THE-AUTHORS.md that carries the
# detail.  Everything else is derived, so this dictionary is the only place in the
# tooling where a judgement is recorded rather than computed.
# ---------------------------------------------------------------------------
BLOCKED_ON_PAPER = "Blocked on the paper"
CITED = "Cited from outside the paper"
BLOCKED_ON_MATHLIB = "Blocked on Mathlib"
UNDECIDED = "Waiting on a decision about the statement"
NOT_YET = "Not formalised yet"

ORDER = [BLOCKED_ON_PAPER, CITED, UNDECIDED, BLOCKED_ON_MATHLIB, NOT_YET]

HEADNOTE = {
    BLOCKED_ON_PAPER:
        "The written proof does not compose.  A repair is new mathematics and is the "
        "authors' to write, not the formalisation's to guess: each of these is left "
        "carrying a `sorry` on purpose.",
    CITED:
        "Not results of arXiv:2607.19651 at all.  Nothing in this library can discharge "
        "them, so no amount of work here will close them.",
    UNDECIDED:
        "Nobody's fault: not a gap in Mathlib, not a gap in the paper.  What is missing "
        "is a decision about what the Lean statement should say.",
    BLOCKED_ON_MATHLIB:
        "The paper's proof is fine; Mathlib has no theory of the object it uses.  "
        "Closing these means contributing to Mathlib, and `blueprint/blueprint.md` is "
        "the audit of exactly what is absent, checked against the pinned revision.",
    NOT_YET:
        "No obstruction known.  The paper proves them and nothing here stands in the "
        "way; they are simply not done.",
}

# Why a node is not proved, keyed by blueprint label.  ``--check`` fails if a node
# that is not proved has no entry here, so an obstruction cannot be introduced
# without being documented.  This is the only place in the tooling where a judgement
# is recorded rather than computed.
REASONS: dict[str, tuple[str, str]] = {
    # -- the written proof does not compose ---------------------------------
    "lem:lemma19": (
        BLOCKED_ON_PAPER,
        "the sequence of `⌊m⌋ + 1` distinct actors is asserted "
        '("by (25)"), never constructed, and the degenerate case is ruled out '
        "through `τ(u) = 2` rather than through `m = 0`",
    ),
    "lem:lemma20": (
        BLOCKED_ON_PAPER,
        "the induction invariant is not preserved: the actor that expresses at step `k` "
        "has its row reset, and at the terminal `k` the bound is negative",
    ),
    "prop:biased-confinement": (
        BLOCKED_ON_PAPER,
        "does not follow from Proposition 6 as Appendix C asserts: under near-greedy "
        "expression the chain gives `N - 1 + 1/(2γ)`, which reaches `N` only for "
        "`γ ≥ 1/2`, and here `γ < 1/(M-1)`",
    ),
    "prop:biased-reach-ladder": (
        BLOCKED_ON_PAPER,
        "assembles biased analogues of Lemmas 19 and 20, which the paper does not state",
    ),
    "lem:biased-hitting": (
        BLOCKED_ON_PAPER,
        "the biased twin of Lemma 13, and its ingredients — the biased forms of the two "
        "displays below — are not in the paper either",
    ),
    # -- citations ----------------------------------------------------------
    "prop:exit-exponential": (
        CITED,
        "Theorem 5.3 of [LM22].  Declared as an `axiom`, not a `sorry`",
    ),
    "prop:biased-exit-exponential": (
        CITED,
        "the same citation over `Profile N M`.  Two are needed because the abstract "
        "statement is inconsistent",
    ),
    "lem:hitting-rate": (
        CITED,
        "displayed inside the proof of Theorem 2.2 and never stated; Theorem 2.2 is a "
        "limit, and a limit has thrown the rate away",
    ),
    "lem:hitting-zero-decomp": (
        CITED,
        "equation (19), displayed inside the proof of Lemma 13 and attributed to "
        "Corollary 11, which is likewise only a limit",
    ),
    # -- the Lean statement has still to be settled -------------------------
    "lem:measurable-hitting": (
        UNDECIDED,
        "an infimum over uncountably many times: it needs right-continuity of the path, "
        "which holds only almost surely.  Wants an almost-sure statement, or a proof "
        "that goes through the null set",
    ),
    # -- Mathlib ------------------------------------------------------------
    "thm:invariant-skeleton": (
        BLOCKED_ON_MATHLIB,
        "Doeblin's minorisation criterion.  The keystone: six results below wait on it",
    ),
    "thm:invariant": (BLOCKED_ON_MATHLIB, "Doeblin, then the transfer of equation (13)"),
    "thm:biased-existence": (BLOCKED_ON_MATHLIB, "Doeblin, as Theorem 1.2"),
    "lem:transfer": (
        BLOCKED_ON_MATHLIB,
        "the stationary-law transfer; needs Doeblin to be worth stating, and its own "
        "statement is one the authors may want to change",
    ),
    "thm:concentration": (BLOCKED_ON_MATHLIB, "Doeblin, then Kac's lemma"),
    "thm:biased-concentration": (BLOCKED_ON_MATHLIB, "Doeblin, then Kac's lemma"),
    "prop:skeleton-concentration": (BLOCKED_ON_MATHLIB, "Kac's lemma"),
    "prop:biased-skeleton-concentration": (BLOCKED_ON_MATHLIB, "Kac's lemma"),
    "cor:zero": (BLOCKED_ON_MATHLIB, "Kac's lemma, through Proposition 9"),
    "cor:hitting-zero": (BLOCKED_ON_MATHLIB, "Doeblin and Kac, through Theorem 2"),
    "thm:nonexplosion": (BLOCKED_ON_MATHLIB, "Poisson point processes"),
    "thm:biased-nonexplosion": (BLOCKED_ON_MATHLIB, "Poisson point processes"),
    "lem:exit-bounds": (BLOCKED_ON_MATHLIB, "the continuous-time analysis of Appendix B"),
    "lem:biased-exit-bounds": (BLOCKED_ON_MATHLIB, "Appendix B, as Lemma 14"),
    # -- simply not done ----------------------------------------------------
    "prop:biased-absorb": (
        NOT_YET,
        "the paper proves it and nothing here stands in the way",
    ),
    "thm:phase": (NOT_YET, "combines Theorem 16 and Proposition 18"),
    "rem:remark6": (
        NOT_YET,
        "the one numbered statement of the paper with no Lean counterpart; nothing "
        "downstream uses it",
    ),
}


# The reference a node's title carries is not always the statement it formalises, and a
# few titles are mostly mathematics.  Both are fixed here rather than by contorting the
# blueprint's own prose.  ``None`` demotes a node to the auxiliary table: the two
# displays Lemma 13 rests on are references *into* proofs, not numbered statements.
PAPER_OVERRIDE: dict[str, str | None] = {
    "thm:invariant-skeleton": "Theorem 1.2, skeleton half",
    "prop:biased-exit-exponential": "Proposition 12, biased twin",
    "lem:hitting-rate": None,
    "lem:hitting-zero-decomp": None,
}

NAME_OVERRIDE: dict[str, str] = {
    "lem:hitting-rate": "the display inside the proof of Theorem 2.2",
    "lem:hitting-zero-decomp": "equation (19)",
    "lem:state-stable": "S is stable under expression",
    "lem:state-along": "S along a realisation",
    "lem:ladder-consensus": "a ladder is a consensus state",
    "rem:biased-ladder-steep": "a biased ladder is a biased steep ladder",
    "lem:ladder-nonempty": "the ladder set is inhabited",
    "lem:biased-ladder-nonempty": "the biased ladder set is inhabited",
    "rem:ladder-steep": "every ladder is a steep ladder",
    "lem:eta": "the bound η",
    "lem:eta-pow": "the bound η, iterated",
    "lem:gap": "the gap estimate",
    "lem:consensus-ladder": "from a consensus state to a ladder",
    "lem:favouring-max": "the opening step",
    "lem:closing": "the closing step",
}


class Node:
    __slots__ = ("label", "kind", "title", "paper", "lean", "stmt_ok", "proof_ok",
                 "has_proof", "uses", "order")

    def __init__(self, label: str, kind: str, title: str, order: int) -> None:
        self.label = label
        self.kind = kind
        self.title = title
        self.paper = (PAPER_OVERRIDE[label] if label in PAPER_OVERRIDE
                      else paper_reference(title))
        self.lean: list[str] = []
        self.stmt_ok = False
        self.proof_ok = False
        self.has_proof = False
        self.uses: list[str] = []
        self.order = order


PAPER_REF = re.compile(
    r"\b(Theorem|Proposition|Lemma|Corollary|Definition|Remark)~([0-9]+(?:\.[0-9]+)?)"
)
EQUATION_REF = re.compile(r"\b(?:equation|eq\.)~?\(([0-9]+)\)")


def paper_reference(title: str) -> str | None:
    """The statement of the paper a blueprint node corresponds to, if any.

    Nodes whose title carries no reference are auxiliaries of the formalisation: they
    have no counterpart in arXiv:2607.19651 and are not counted as progress on it.
    """
    m = PAPER_REF.search(title)
    if m:
        return f"{m.group(1)} {m.group(2)}"
    m = EQUATION_REF.search(title)
    if m:
        return f"equation ({m.group(1)})"
    return None


def strip_braces(text: str, start: int) -> tuple[str, int]:
    """Read a balanced ``{...}`` group beginning at ``start`` (the opening brace)."""
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1:i], i + 1
    raise ValueError("unbalanced braces in the blueprint")


def read_optional_title(text: str, start: int) -> tuple[str, int]:
    """Read a ``[...]`` title following ``\\begin{env}``, tolerating nested brackets."""
    if start >= len(text) or text[start] != "[":
        return "", start
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return text[start + 1:i], i + 1
    raise ValueError("unbalanced brackets in the blueprint")


def parse_blueprint() -> list[Node]:
    text = CONTENT.read_text(encoding="utf-8")
    nodes: list[Node] = []
    pos = 0
    order = 0
    begin = re.compile(r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}")
    while True:
        m = begin.search(text, pos)
        if m is None:
            break
        kind = m.group(1)
        title, after = read_optional_title(text, m.end())
        end = text.find("\\end{" + kind + "}", after)
        if end == -1:
            raise ValueError(f"unterminated {kind} in the blueprint")
        body = text[after:end]
        label_m = re.search(r"\\label\{([^}]*)\}", body)
        if label_m is None:
            pos = end
            continue
        node = Node(label_m.group(1), kind, title, order)
        order += 1
        lean_m = re.search(r"\\lean\{", body)
        if lean_m:
            names, _ = strip_braces(body, lean_m.end() - 1)
            node.lean = [n.strip() for n in names.split(",") if n.strip()]
        node.stmt_ok = "\\leanok" in body
        uses_m = re.search(r"\\uses\{", body)
        if uses_m:
            refs, _ = strip_braces(body, uses_m.end() - 1)
            node.uses = [r.strip() for r in refs.split(",") if r.strip()]

        # A proof, when there is one, follows the environment immediately.
        tail = text[end:]
        proof_m = re.match(r"\s*\\end\{" + kind + r"\}\s*\\begin\{proof\}", tail)
        if proof_m:
            proof_end = text.find("\\end{proof}", end)
            proof_body = text[end + proof_m.end() - len("\\begin{proof}"):proof_end]
            node.has_proof = True
            node.proof_ok = "\\leanok" in proof_body
            uses_m = re.search(r"\\uses\{", proof_body)
            if uses_m:
                refs, _ = strip_braces(proof_body, uses_m.end() - 1)
                node.uses += [r.strip() for r in refs.split(",") if r.strip()]
            pos = proof_end
        else:
            pos = end
        nodes.append(node)
    return nodes


DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|axiom|def|abbrev|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)")
STRUCTURE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_.']*)"
)
FIELD = re.compile(r"^\s+([a-z_][A-Za-z0-9_']*)\s*:[^=]")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_.'!?]*)")
SORRY = re.compile(r"^\s*sorry\s*$")


def declarations() -> tuple[set[str], set[str], set[str]]:
    """Every declaration in the library, those that are axioms, those with a bare ``sorry``.

    A ``sorry`` is attributed to the declaration whose block it falls in, which is the
    last one opened before it.  That is exact for this library, where every ``sorry`` is
    the whole proof of the declaration above it.
    """
    found: set[str] = set()
    axioms: set[str] = set()
    sorries: set[str] = set()
    for path in sorted(SOURCES.glob("*.lean")):
        stack: list[str] = []
        structure: str | None = None
        current: str | None = None
        for line in path.read_text(encoding="utf-8").splitlines():
            if structure is not None:
                if line.strip() and not line[0].isspace():
                    structure = None
                else:
                    m = FIELD.match(line)
                    if m:
                        found.add(f"{structure}.{m.group(1)}")
                    if structure is not None:
                        continue
            m = NAMESPACE.match(line)
            if m:
                stack.append(m.group(1))
                continue
            m = END.match(line)
            if m:
                if stack and stack[-1] == m.group(1):
                    stack.pop()
                continue
            if SORRY.match(line) and current is not None:
                sorries.add(current)
                continue
            m = DECL.match(line)
            if m:
                name = m.group(1)
                full = ".".join(stack + [name]) if stack else name
                found.add(full)
                current = full
                if AXIOM.match(line):
                    axioms.add(full)
                if STRUCTURE.match(line) and line.rstrip().endswith("where"):
                    structure = full
    return found, axioms, sorries


def is_prose(node: Node) -> bool:
    """A commentary node: no Lean counterpart and nothing to prove."""
    return not node.lean and not node.stmt_ok


def has_obligation(node: Node) -> bool:
    """Does the node carry a proof obligation?

    Definitions do not, nor do the two remarks that bundle a construction: their
    content is the declarations they name.  Everything else does.
    """
    if is_prose(node) and node.label not in REASONS:
        return False
    return node.kind != "definition" and node.has_proof or node.label in REASONS


def resolve(nodes: list[Node], axioms: set[str], sorries: set[str]) -> dict[str, str]:
    """The status of every node, as a least fixed point over ``\\uses``.

    ``proved`` means the proof is written *and* everything it uses is proved, which is
    the transitive closure ``leanblueprint`` draws its green nodes with.  A proof here
    does not have to wait for its ancestors: a written proof whose upstream lemmas still
    carry a ``sorry`` compiles and inherits ``sorryAx``, so the two questions are kept
    apart.  A cycle in ``\\uses`` would be a circular argument and resolves to *not*
    proved rather than to a false green.
    """
    by_label = {n.label: n for n in nodes}
    status: dict[str, str] = {}
    for node in nodes:
        if any(name in axioms for name in node.lean):
            status[node.label] = "axiom"
        elif any(name in sorries for name in node.lean):
            status[node.label] = "unproved"
        elif is_prose(node):
            status[node.label] = "not stated" if node.label in REASONS else "prose"
        elif not has_obligation(node):
            status[node.label] = "stated"
        elif node.proof_ok:
            status[node.label] = "pending"
        else:
            status[node.label] = "unproved"

    changed = True
    while changed:
        changed = False
        for node in nodes:
            if status[node.label] != "pending":
                continue
            deps = [status[u] for u in node.uses if u in by_label]
            if all(d in ("proved", "stated", "prose") for d in deps):
                status[node.label] = "proved"
                changed = True
    for node in nodes:
        if status[node.label] == "pending":
            status[node.label] = "rests on"
    return status


def blockers(node: Node, by_label: dict[str, Node], status: dict[str, str]) -> list[str]:
    """The unproved nodes the proof of ``node`` ultimately rests on."""
    seen: set[str] = set()
    out: list[str] = []
    stack = list(node.uses)
    while stack:
        label = stack.pop()
        if label in seen or label not in by_label:
            continue
        seen.add(label)
        if status[label] in ("proved", "stated", "prose"):
            continue
        if status[label] == "rests on":
            stack.extend(by_label[label].uses)
        else:
            out.append(label)
    return sorted(out, key=lambda l: by_label[l].order)


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

def short_title(node: Node) -> str:
    """The node's title with the mathematics stripped, for use as a name."""
    if node.label in NAME_OVERRIDE:
        return NAME_OVERRIDE[node.label]
    title = re.sub(r"\$[^$]*\$", "", node.title)
    title = re.sub(r"\\[a-zA-Z]+", "", title).replace("~", " ")
    title = re.sub(r",\s*(Theorem|Proposition|Lemma|Corollary|Definition|Remark|eq\.)"
                   r"[^,]*$", "", title)
    return re.sub(r"\s+", " ", title).strip().strip(",")


def name(node: Node) -> str:
    """How a node is called in the tables: its statement in the paper, or its title."""
    return node.paper or short_title(node)


def display(node: Node, shared: set[str]) -> str:
    """``name``, disambiguated when several nodes decompose one statement of the paper."""
    if node.paper and node.paper in shared:
        title = short_title(node)
        if title and not title.startswith(node.paper):
            return f"{node.paper} — {title}"
    return name(node)


def lean_cell(node: Node) -> str:
    if not node.lean:
        return "—"
    head = node.lean[0]
    extra = f" +{len(node.lean) - 1}" if len(node.lean) > 1 else ""
    return f"`{head.removeprefix('SocialNetwork.')}`{extra}"


def render(nodes: list[Node], status: dict[str, str]) -> str:
    by_label = {n.label: n for n in nodes}
    seen: dict[str, int] = {}
    for n in nodes:
        if n.paper and status[n.label] != "prose":
            seen[n.paper] = seen.get(n.paper, 0) + 1
    shared = {ref for ref, count in seen.items() if count > 1}
    paper = [n for n in nodes if n.paper and status[n.label] != "prose"]
    auxiliary = [n for n in nodes if not n.paper and status[n.label] != "prose"]
    resisting = [n for n in nodes if n.label in REASONS]

    out: list[str] = []
    w = out.append
    w("# Status")
    w("")
    w("*Generated by `scripts/status.py` from `blueprint/src/content.tex` and the Lean")
    w("sources. Do not edit by hand — run `python3 scripts/status.py`. CI checks that")
    w("this file is current, and refuses an obstruction that is not documented below.*")
    w("")
    w("Three words are used throughout, and they mean different things.")
    w("")
    w("- **proved** — the proof is written in Lean *and* everything it rests on is")
    w("  proved. This is what the build checks: no `sorryAx`, and neither [LM22] axiom.")
    w("- **rests on** — the proof is written, but an upstream statement is not. It")
    w("  compiles, inherits `sorryAx`, and turns green the moment its ancestors do,")
    w("  with no edit. Writing a proof before its ancestors is deliberate here: it is")
    w("  the only test of whether the upstream *statements* are strong enough.")
    w("- **unproved** — the statement is in Lean and carries a `sorry`.")
    w("")

    # --- what resists ------------------------------------------------------
    w("## 1. What resists formalisation")
    w("")
    w(f"{len(resisting)} statements. They are unproved for five different reasons, and")
    w("the reasons are not comparable: one of these groups will never close here, one")
    w("needs mathematics only the authors can supply, and one is only work.")
    w("[`FOR-THE-AUTHORS.md`](FOR-THE-AUTHORS.md) carries the detail and what each item")
    w("asks for.")
    w("")
    for category in ORDER:
        group = [n for n in resisting if REASONS[n.label][0] == category]
        if not group:
            continue
        w(f"### {category} ({len(group)})")
        w("")
        for line in HEADNOTE[category].split("  "):
            w(line)
        w("")
        w("| Statement | Lean | Why |")
        w("|---|---|---|")
        for node in sorted(group, key=lambda n: n.order):
            w(f"| {display(node, shared)} | {lean_cell(node)} | {REASONS[node.label][1]} |")
        w("")

    # --- how far it has got ------------------------------------------------
    w("## 2. How far the formalisation has got")
    w("")
    counts = {k: 0 for k in ("proved", "rests on", "unproved", "axiom", "stated", "not stated")}
    for node in paper + auxiliary:
        counts[status[node.label]] += 1
    w("| | statements of the paper | auxiliary | total |")
    w("|---|---:|---:|---:|")
    for key, label in (
        ("proved", "Proved"),
        ("rests on", "Proof written, resting on an unproved statement"),
        ("stated", "Definitions and constructions"),
        ("unproved", "Stated in Lean, unproved"),
        ("axiom", "Axioms ([LM22])"),
        ("not stated", "Not stated in Lean"),
    ):
        a = sum(1 for n in paper if status[n.label] == key)
        b = sum(1 for n in auxiliary if status[n.label] == key)
        if a or b:
            w(f"| {label} | {a} | {b} | {a + b} |")
    w(f"| **Total** | **{len(paper)}** | **{len(auxiliary)}** | **{len(paper) + len(auxiliary)}** |")
    w("")
    statements = {n.paper for n in paper}
    unstated = {n.paper for n in paper if status[n.label] == "not stated"}
    w(f"The rows above are blueprint nodes, and several of them decompose a single "
      f"statement of")
    w(f"the paper. Counted as the paper numbers them, {len(statements)} statements and "
      f"displayed equations")
    w(f"are covered, of which {len(statements) - len(unstated)} are stated in Lean. The "
      f"only one that is not is "
      + ", ".join(sorted(unstated)) + ".")
    w("")

    w("### The statements of the paper")
    w("")
    w("| Statement | Lean | Status |")
    w("|---|---|---|")
    for node in sorted(paper, key=lambda n: n.order):
        w(f"| {display(node, shared)} | {lean_cell(node)} | {status_cell(node, by_label, status, shared)} |")
    w("")

    w("### Auxiliary results, with no counterpart in the paper")
    w("")
    w("Steps the paper leaves implicit, plumbing for the sample space, and the")
    w("witnesses that keep a vacuous statement from passing for a theorem.")
    w("")
    w("| Statement | Lean | Status |")
    w("|---|---|---|")
    for node in sorted(auxiliary, key=lambda n: n.order):
        w(f"| {display(node, shared)} | {lean_cell(node)} | {status_cell(node, by_label, status, shared)} |")
    w("")
    return "\n".join(out) + "\n"


def status_cell(node: Node, by_label: dict[str, Node], status: dict[str, str],
                shared: set[str]) -> str:
    state = status[node.label]
    if state == "rests on":
        names = ", ".join(display(by_label[b], shared)
                          for b in blockers(node, by_label, status))
        return f"proof written, rests on {names}"
    if state in ("unproved", "axiom", "not stated") and node.label in REASONS:
        category = REASONS[node.label][0]
        return f"{state} — {category[0].lower()}{category[1:]}"
    return state


# Declarations that no blueprint node cites — internal helpers, mostly arithmetic —
# and that are nonetheless claimed complete.  Everything else the axiom check covers is
# derived from the blueprint, so this list is the only part of it kept by hand.
INTERNAL: tuple[str, ...] = (
    "SocialNetwork.isConsensus_state",
    "SocialNetwork.hittingTimeCts_mono",
    "SocialNetwork.mul_exp_neg_le_exp_neg_one",
    "SocialNetwork.mul_exp_neg_div_le",
    "SocialNetwork.one_le_eight_mul_exp_neg_one",
    "SocialNetwork.const_bounds",
    "SocialNetwork.exp_add_zeta_pow_le",
    "SocialNetwork.Bias.Profile.pressure_le_heard",
    "SocialNetwork.Bias.heard_stateAfter_le",
    "SocialNetwork.Bias.heard_stateAfter_expressed",
    "SocialNetwork.Bias.pressure_stateAfter_le_of_biasedGreedy",
    "SocialNetwork.Bias.biasedZeta_le_biasedJumpPMF_nearArgmaxFinset",
    "SocialNetwork.Bias.inv_le_biasedJumpPMF_biasedArgmaxFinset",
    "SocialNetwork.Bias.le_partialTraj_succ",
    "SocialNetwork.Bias.pow_le_historyMeasure",
    "SocialNetwork.Bias.pow_le_pathMeasure_stepEvents",
    "SocialNetwork.Bias.biasedHittingTimeCts_mono",
)


def axiom_check(nodes: list[Node], status: dict[str, str]) -> str:
    """The body of ``CheckAxioms.lean``: every declaration claimed complete.

    Claimed complete means a blueprint node the graph resolves to *proved* or *stated* —
    so the blueprint's own green nodes are what the build verifies, and a
    ``\\leanok`` that is not earned fails CI instead of going unnoticed.  Before this
    was generated the list was typed by hand, and two of its names had gone dead.
    """
    out = ["import SocialNetwork"]
    seen: set[str] = set()
    for node in sorted(nodes, key=lambda n: n.order):
        if status[node.label] not in ("proved", "stated"):
            continue
        out.append(f"-- {node.label}")
        for cited in node.lean:
            if cited not in seen:
                seen.add(cited)
                out.append(f"#print axioms {cited}")
    out.append("-- cited by no blueprint node")
    for cited in INTERNAL:
        if cited not in seen:
            seen.add(cited)
            out.append(f"#print axioms {cited}")
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="verify STATUS.md is current instead of rewriting it")
    parser.add_argument("--axioms", metavar="FILE",
                        help="write the CheckAxioms.lean the build runs, and exit")
    args = parser.parse_args()

    nodes = parse_blueprint()
    known, axioms, sorries = declarations()

    problems: list[str] = []
    for node in nodes:
        for cited in node.lean:
            if cited not in known:
                problems.append(f"{node.label}: cites {cited}, which the library does not declare")
    cited_names = {n for node in nodes for n in node.lean}
    for orphan in sorted(sorries - cited_names):
        problems.append(f"{orphan} carries a sorry and no blueprint node cites it")

    status = resolve(nodes, axioms, sorries)
    if args.axioms:
        Path(args.axioms).write_text(axiom_check(nodes, status), encoding="utf-8")
        print(f"wrote {args.axioms}")
        return 0
    for node in nodes:
        if status[node.label] in ("unproved", "axiom", "not stated") and node.label not in REASONS:
            problems.append(f"{node.label} is {status[node.label]} and scripts/status.py "
                            f"records no reason for it")

    if problems:
        print("blueprint and library disagree:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    text = render(nodes, status)
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text(encoding="utf-8") != text:
            print("STATUS.md is out of date; run python3 scripts/status.py", file=sys.stderr)
            return 1
        print(f"STATUS.md is current: {len(nodes)} blueprint nodes, "
              f"{sum(1 for s in status.values() if s == 'proved')} proved, "
              f"{len(REASONS)} documented obstructions")
        return 0
    OUTPUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(REPO)}: {len(nodes)} nodes, "
          f"{sum(1 for s in status.values() if s == 'proved')} proved, "
          f"{len(REASONS)} documented obstructions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
