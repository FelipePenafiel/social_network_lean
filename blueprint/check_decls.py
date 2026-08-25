#!/usr/bin/env python3
"""Check that every Lean name cited in the blueprint exists in the library.

This is a *syntactic* approximation of `lake exe checkdecls`, which is the real
thing: it parses the `SocialNetwork/*.lean` sources, tracking `namespace`/`end`
to reconstruct fully qualified names, and compares that set with the
`blueprint/lean_decls` file that plasTeX writes when building the blueprint.

It is used instead of `lake exe checkdecls` because it needs neither a Lean
toolchain nor a compiled project, so the blueprint workflow stays independent of
the build.  It will miss names that Lean generates rather than the source
spelling out — structure projections, `to_additive` translations, instances
declared without a name.  Add such a name to KNOWN_GENERATED below if the need
arises, or run `lake exe checkdecls blueprint/lean_decls` for the exact check.
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

# Names Lean generates that the sources do not spell out.
KNOWN_GENERATED: set[str] = set()


def declarations(root: Path) -> set[str]:
    found: set[str] = set()
    for path in sorted(root.glob("*.lean")):
        stack: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
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
                found.add(".".join(stack + [name]) if stack else name)
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
