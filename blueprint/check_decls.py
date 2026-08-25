#!/usr/bin/env python3
"""Check that every Lean name cited in the blueprint exists in the library.

This is a *syntactic* approximation of `lake exe checkdecls`, which is the real
thing: it parses the `SocialNetwork/*.lean` sources, tracking `namespace`/`end`
to reconstruct fully qualified names, and compares that set with the
`blueprint/lean_decls` file that plasTeX writes when building the blueprint.

It is used instead of `lake exe checkdecls` because it needs neither a Lean
toolchain nor a compiled project, so the blueprint workflow stays independent of
the build.  Besides the declarations the source spells out, it collects the
fields of `structure` blocks, since those become projections and the blueprint
cites several of them.  It will still miss names Lean generates by other means —
`to_additive` translations, anonymous instances, constructors.  Add such a name
to KNOWN_GENERATED below if the need arises, or run
`lake exe checkdecls blueprint/lean_decls` for the exact check.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)")
STRUCTURE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:structure|class)\s+([A-Za-z_][A-Za-z0-9_.']*)"
)
# A field of a `structure ... where` block: indented, an identifier, then `:`.
FIELD = re.compile(r"^\s+([a-z_][A-Za-z0-9_']*)\s*:[^=]")

# Names Lean generates that the sources do not spell out.
KNOWN_GENERATED: set[str] = set()


def declarations(root: Path) -> set[str]:
    found: set[str] = set()
    for path in sorted(root.glob("*.lean")):
        stack: list[str] = []
        structure: str | None = None
        for line in path.read_text(encoding="utf-8").splitlines():
            if structure is not None:
                # Fields are indented; the first non-indented, non-blank line ends
                # the structure body.
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
            m = DECL.match(line)
            if m:
                name = m.group(1)
                full = ".".join(stack + [name]) if stack else name
                found.add(full)
                if STRUCTURE.match(line) and line.rstrip().endswith("where"):
                    structure = full
    return found


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    cited_file = repo / "blueprint" / "lean_decls"
    if not cited_file.exists():
        print("blueprint/lean_decls not found: build the blueprint first", file=sys.stderr)
        return 1

    cited = {line.strip() for line in cited_file.read_text(encoding="utf-8").splitlines()}
    cited.discard("")
    known = declarations(repo / "SocialNetwork") | KNOWN_GENERATED

    missing = sorted(name for name in cited if name not in known)
    print(f"{len(cited)} declarations cited in the blueprint, {len(known)} declared in the library")
    if missing:
        print("\nCited in the blueprint but not found in the library:", file=sys.stderr)
        for name in missing:
            print(f"  {name}", file=sys.stderr)
        return 1
    print("every declaration cited in the blueprint exists")
    return 0


if __name__ == "__main__":
    sys.exit(main())
