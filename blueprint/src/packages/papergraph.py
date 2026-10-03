"""
Package papergraph: the dependency graph of the paper's results.

The graph plastexdepgraph draws has one node per blueprint node, and the blueprint
splits the paper finely: every definition and equation, the auxiliary lemmas the
formalisation adds, and the parts a statement is proved in are nodes of their own.
That is the right graph to formalise against and the wrong one to read the paper's
structure from.  This package draws a second graph for that:

* one node per result of the paper, that is per Theorem, Proposition, Lemma and
  Corollary, named as the paper names it.  Every blueprint node the paper gives that
  name to is drawn there, and so are the parts of a theorem (Theorem 1.1 and 1.2 are
  Theorem 1) and the displays the paper makes inside a proof (``DISPLAYED_IN``);
* no node for the rest --- definitions, equations, remarks, and the statements the
  paper does not make (``\\aux``).  An arrow runs through them instead: when a result
  rests on one of them and it on another result, the second result is drawn as an
  ancestor of the first.

A node is coloured as leanblueprint colours one, read over all the blueprint nodes it
stands for: its proof is formalised when all of theirs are, and fully when all of
their ancestors' are too.  The ancestors include the remarks, which leanblueprint
leaves out of its own count, so the full graph is recoloured the same way.

The result is the page ``Dependency graph`` links to.  The graph plastexdepgraph built is
kept, and written to ``dep_graph_full.html``.

This reaches into plastexdepgraph and leanblueprint (the graph objects, the
userdata keys they fill, the template) rather than through an interface of theirs:
if either changes, this is the file to look at.
"""
import re
from pathlib import Path

from jinja2 import Template
from pygraphviz import AGraph

import plastexdepgraph
from plastexdepgraph.Packages.depgraph import DepGraph, item_kind
from plasTeX.Logging import getLogger
from plasTeX.PackageResource import PackagePreCleanupCB

log = getLogger()

KINDS = ('theorem', 'proposition', 'lemma', 'corollary', 'definition', 'remark')

# The names of the paper's results.  Anything else is drawn through.
RESULT = re.compile(r'(Theorem|Proposition|Lemma|Corollary) \d+$')

# \aux numbers a statement A.1, A.2, ...: the paper does not make it.
AUX = re.compile(r'A\.\d+$')

# The blueprint numbers the parts of a theorem: Theorem 1.2 is part 2 of Theorem 1.
PART = re.compile(r'^(Theorem \d+)\.\d+$')

# Displays the paper makes inside a proof, and the result whose proof it is.
DISPLAYED_IN = {
    'Equation (13)': 'Theorem 1',   # p. 18, in the proof of part 2
    'Equation (19)': 'Lemma 13',
}

FULL_TARGET = 'dep_graph_full.html'


def paper_name(node) -> str:
    """The name ``\\paper`` or ``\\aux`` gave the node, as its reference prints it."""
    return ' '.join(node.ref.textContent.split())


def result_name(node) -> str:
    """The result of the paper the node belongs to, or '' if it belongs to none."""
    name = paper_name(node)
    if AUX.search(name):
        return ''
    name = DISPLAYED_IN.get(name, name)
    name = PART.sub(r'\1', name)
    return name if RESULT.match(name) else ''


class Result:
    """One result of the paper, as the graph template needs a node to look.

    The template reads ``id`` (the node's name in the dot source, which is how a click
    finds its statement), ``thmName``, ``caption``, ``ref``, ``title``, ``url`` and
    ``userdata['lean_urls']``, and renders the object itself as the statement.
    """

    def __init__(self, name: str, members: list):
        self.name = name
        # The node the paper's name is given to whole comes first, and stands for the
        # rest: Lemma 13 before the display (19) inside its proof.
        self.members = sorted(members, key=lambda node: paper_name(node) != name)
        first = self.members[0]
        self.id = first.id
        self.thmName = first.thmName
        self.caption = first.caption
        # One blueprint node per name the paper uses: Theorem 1 shows Theorem 1.1, 1.2
        # and the display (13), not each part the proof of 1.2 is split into.
        self.shown = []
        seen = set()
        for node in self.members:
            if paper_name(node) not in seen:
                seen.add(paper_name(node))
                self.shown.append(node)
        # Whole, the statement's own heading heads the node; in parts, each part has one.
        self.whole = len(self.shown) == 1 or paper_name(first) == name
        if self.whole:
            self.ref, self.title = first.ref, first.title
        else:
            self.ref, self.title = name, ''
        self.userdata: dict = {'lean_urls': []}
        self.colors = ('', '')

    @property
    def url(self) -> str:
        # Known only once the document is rendered.
        return self.members[0].url

    def __str__(self) -> str:
        parts = [str(self.shown[0])] if self.whole else []
        for node in self.shown[len(parts):]:
            title = (f' <span class="{node.thmName}_thmtitle">{node.title}</span>'
                     if node.title else '')
            parts.append(
                '<div class="thm_thmheading">'
                f'<span class="{node.thmName}_thmlabel">{node.ref}</span>{title}'
                f'</div><div class="thm_thmcontent">{node}</div>')
        return '\n'.join(parts)


class PaperGraph(DepGraph):
    """The results of the paper, and which rests on which."""

    def to_dot(self, shapes: dict) -> AGraph:
        graph = AGraph(directed=True, bgcolor='transparent')
        graph.node_attr['penwidth'] = 1.8
        graph.edge_attr.update(arrowhead='vee')
        for result in self.nodes:
            color, fillcolor = result.colors
            attrs = dict(label=result.name, shape='ellipse', color=color)
            if fillcolor:
                attrs.update(style='filled', fillcolor=fillcolor)
            graph.add_node(result.id, **attrs)
        for s, t in self.edges:
            graph.add_edge(s.id, t.id, style='dashed')
        for s, t in self.proof_edges:
            graph.add_edge(s.id, t.id)
        return graph


def ProcessOptions(options, document):
    """This is called when the package is loaded."""
    data = document.userdata['dep_graph']
    uses: dict = {}

    def record_uses() -> None:
        """What each statement and each proof uses.

        Read between plastexdepgraph resolving ``\\uses`` and leanblueprint appending
        each proof's uses to its statement's, after which the two cannot be told apart.
        """
        for node in document.context.labels.values():
            if item_kind(node) not in KINDS or node in uses:
                continue
            proof = node.userdata.get('proved_by')
            uses[node] = (list(node.userdata.get('uses', [])),
                          list(proof.userdata.get('uses', [])) if proof else [])

    document.addPostParseCallbacks(120, record_uses)

    def lean_urls(nodes) -> list:
        dochome = document.userdata.get(
            'project_dochome', 'https://leanprover-community.github.io/mathlib4_docs')
        decls = []
        for node in nodes:
            decls += [d for d in node.userdata.get('leandecls', []) if d not in decls]
        return [(d, f'{dochome}/find/#doc/{d}') for d in decls]

    def build() -> None:
        nodes = list(uses)
        name = {node: result_name(node) for node in nodes}
        members: dict = {}
        for node in nodes:
            if name[node]:
                members.setdefault(name[node], []).append(node)
        results = {n: Result(n, ms) for n, ms in members.items()}
        for result in results.values():
            result.userdata['lean_urls'] = lean_urls(result.shown)

        # Which results each result rests on, through the nodes that are not drawn.
        # A statement that uses a node needs that node's statement; a proof that uses
        # it needs its proof as well.
        def reach(node, in_proof: bool, found: dict, seen: set) -> None:
            if (node, in_proof) in seen or node not in uses:
                return
            seen.add((node, in_proof))
            if name[node]:
                result = results[name[node]]
                found[result] = found.get(result, False) or in_proof
                return
            statement, proof = uses[node]
            for used in statement:
                reach(used, in_proof, found, seen)
            if in_proof:
                for used in proof:
                    reach(used, True, found, seen)

        graph = PaperGraph()
        graph.document = document
        graph.nodes = set(results.values())
        for result in results.values():
            found: dict = {}
            seen: set = set()
            for node in result.members:
                statement, proof = uses[node]
                for used in statement:
                    reach(used, False, found, seen)
                for used in proof:
                    reach(used, True, found, seen)
            found.pop(result, None)
            for source, in_proof in found.items():
                (graph.proof_edges if in_proof else graph.edges).add((source, result))

        for result in graph.nodes:
            if result in graph.ancestors(result):
                log.warning(f'papergraph: {result.name} rests on itself')

        # Colours, as leanblueprint gives them, over the blueprint nodes each result
        # stands for.
        ancestors: dict = {}

        def ancestors_of(node) -> set:
            if node not in ancestors:
                ancestors[node] = set()
                for used in sum(uses.get(node, ([], [])), []):
                    ancestors[node] |= {used} | ancestors_of(used)
            return ancestors[node]

        def stated(node) -> bool:
            return bool(node.userdata.get('leanok'))

        def proved(node) -> bool:
            proof = node.userdata.get('proved_by')
            return bool(proof and proof.userdata.get('leanok'))

        def can_state(node) -> bool:
            return (all(stated(u) for u in uses[node][0])
                    and not node.userdata.get('notready', False))

        def can_prove(node) -> bool:
            return all(stated(u) for u in sum(uses[node], []))

        def fully_proved(node) -> bool:
            return all(proved(a) or item_kind(a) == 'definition'
                       for a in ancestors_of(node) | {node})

        colors = data['colors']
        for result in graph.nodes:
            ms = result.members
            color = ''
            if all(m.userdata.get('mathlibok') for m in ms):
                color = colors['mathlib'][0]
            elif all(stated(m) for m in ms):
                color = colors['stated'][0]
            elif all(stated(m) or can_state(m) for m in ms):
                color = colors['can_state'][0]
            elif any(m.userdata.get('notready') for m in ms):
                color = colors['not_ready'][0]
            fillcolor = ''
            with_proof = [m for m in ms if m.userdata.get('proved_by')]
            if with_proof and all(proved(m) for m in with_proof):
                fillcolor = colors['fully_proved' if all(fully_proved(m) for m in ms)
                                  else 'proved'][0]
            elif all((stated(m) or can_state(m)) and (proved(m) or can_prove(m))
                     for m in with_proof):
                fillcolor = colors['can_prove'][0]
            result.colors = (color, fillcolor)

        graphs = data['graphs']
        # leanblueprint decides whether a node is proved only for the nodes it draws,
        # and a remark is not one of them: a result resting on Remark 4 or 5 was never
        # drawn as fully proved.  Decided over every node, as above, it is.
        for node in graphs[document].nodes:
            node.userdata['fully_proved'] = fully_proved(node)
        data['full_graph'] = graphs[document]
        graphs[document] = graph

        legend = data['legend']
        data['full_legend'] = legend + [
            ('This graph', 'every node of the blueprint.  The '
             '<a href="dep_graph_document.html">dependency graph</a> draws the '
             "paper's results only.")]
        legend[:] = [
            ('Ellipses', "the results of the paper, one per result: a theorem's parts "
             'and the steps its proof is split into are drawn as the theorem'),
            ('Not drawn', 'definitions, equations, remarks, and the lemmas the '
             'formalisation adds; an arrow runs through them.  The '
             f'<a href="{FULL_TARGET}">full graph</a> draws every node'),
        ] + [entry for entry in legend if entry[0] not in ('Boxes', 'Ellipses')]

        document.rendererdata['html5']['extra_toc_items'].append(
            {'text': 'Full dependency graph', 'url': FULL_TARGET})

    document.addPostParseCallbacks(160, build)

    template = Path(plastexdepgraph.__file__).parent/'templates'/'dep_graph.html'

    def write_full_graph(document) -> list:
        full = data['full_graph']
        dot = full.to_dot(data.get('shapes', {'definition': 'box'})).tred()
        Template(template.read_text()).stream(
            graph=full,
            dot=dot.to_string(),
            context=document.context,
            title='Dependencies, every node of the blueprint',
            legend=data['full_legend'],
            extra_modal_links=data.get('extra_modal_links_tpl', []),
            document=document,
            config=document.config).dump(FULL_TARGET)
        return [FULL_TARGET]

    document.addPackageResource([PackagePreCleanupCB(data=write_full_graph)])
