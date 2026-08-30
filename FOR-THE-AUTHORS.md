# Where the paper resists formalisation

For Felipe Penafiel and Kádmo Laxa.  This file collects everything in
arXiv:2607.19651 that formalising has *not* been able to close, and separates the
places that need a decision from the places that only need work.

**The rule this repository follows, and why this file exists.**  A Lean proof here
must follow the paper's proof; a departure needs a written reason, and the reason
must be that the paper's route cannot be followed.  **No proof of a statement of
the paper has been invented here.**  Where the written argument does not close, the
statement is left carrying a `sorry` and the obstruction is recorded — in the
blueprint for the mathematics, and here for the decision.  Nothing in §1 has been
"repaired" by an argument you have not seen.

The blueprint (`blueprint/src/content.tex`, chapter *Notes on the formalisation*)
holds the full mathematical detail of each item.  This file is the index, and says
what each one asks of you.

---

## 1. Proofs that do not survive formalisation

Three written proofs do not compose.  Each is left unproved on purpose.  A repair
is new mathematics and is yours to write, not the formalisation's to guess.

### 1.1 Lemma 19 — the `⌊m⌋ + 1` distinct actors

*Blueprint:* `rem:lemma19`. *Lean:* `SocialNetwork.isFavouring_state_firstRepeat`.

The written proof asserts, "by (25)", a sequence of `⌊m⌋ + 1` distinct actors
without giving the construction, and rules out the degenerate case `m = 0` through
`τ (u) = 2` rather than through `m = 0` itself.

**What is needed:** the construction, and the corrected case split.  The blueprint
records a first-passage decomposition of the backward walk that does produce the
actors, and the case split that works — but as a *proposal for you to check*, not
as something the formalisation has adopted.

### 1.2 Lemma 20 — the induction invariant is not preserved

*Blueprint:* `rem:lemma20`. *Lean:* `SocialNetwork.isConsensus_state_of_favouring`.

The invariant of the written proof, `Ũₖ (a, p) ≤ n(u) + r - (k+1)/(M-1)` for
`p ≠ o`, is not preserved: the actor that expresses at step `k` has its row reset
to `0`, and at the terminal `k` the bound is negative.

**What is needed:** a preserved invariant.  The blueprint proposes
`max (0, n(u) + r - (k+1)/(M-1))` together with a staircase mechanism that
replenishes the witnesses, again as a proposal to check.

### 1.3 Proposition 22 — does not follow from Proposition 6

*Blueprint:* `rem:prop22`. *Lean:* `SocialNetwork.Bias.entry_mem_of_nearGreedy`.

Appendix C says only that "the proof of Propositions 22, 23 and 24 follows as the
proofs of Propositions 6, 7 and 8".  For Proposition 24 that holds.  For
Proposition 22 it does not.

Proposition 6 splits on whether the first `N` expressions come from distinct
actors.  The distinct case transports unchanged.  In the repeat case an actor
expressing at steps `j < k < N` has heard `k - j - 1` expressions at step `k`, and
*exact* greediness makes its entry the maximum of the whole matrix, so the matrix
is capped at `(k - j - 1) + (N - k) = N - j - 1 ≤ N - 1`.

Under `ξ̃` the expressed pair is only within `1/(2γ)` of the maximum, so the same
chain gives `N - 1 + 1/(2γ)`, which is below `N` only when `γ ≥ 1/2`.  Here
`γ = 1/(M-1) - α` with `α > 0`, so `γ < 1/(M-1)`: **the transported bound never
reaches `N` for any `M ≥ 3`.**

The statement is not obviously false.  Since `u (a, p) ≤ nₐ`, the slack is
self-correcting: a large maximum forces an actor that has heard a lot to express,
and expressing resets it.  A run from `n = (0,1,2)` with `M = N = 3` and `γ = 1/4`
climbs to `3` after two expressions and is pushed back to `2` by the third,
because the only pair within `1/(2γ) = 2` of the maximum belongs to the actor
carrying it.

**Decision for you:** either a proof that uses that feedback — Proposition 6's
chain never looks past step `k`, so it cannot supply one — or a weaker constant.
`N + 1/(2γ)` would do: Propositions 23 and 17 only need a bound depending on
`α`, `M` and `N`.  If you take the weaker constant, it has to be carried through
those two statements.

---

## 2. Statements that had to be changed

These are not gaps in reasoning; they are places where the statement as written
cannot be used, and the Lean statement differs from the paper's display.

| # | Where | What is wrong | What was done |
|---|---|---|---|
| 2.1 | **Proposition 12**, (15)–(18) | `ε₁ ε₂ s₁ s₂` are introduced before `β`, but Section 5.3 instantiates them at `s₂ = 2β` and `ε₂ = (M+1)²N²e^{-β/((M+1)N)}`, and needs `ε₁ + ε₂ ≤ 1/2` only "for β sufficiently big".  Bound as constants ahead of `β`, **the hypotheses are unsatisfiable** — Theorem 3 could never have been derived from them. | Made functions of `β`; (15)–(18) required only above a threshold `β₁`.  Theorem 3 now follows. |
| 2.2 | **Corollary 15** (and 30) | Quantifies over `l ∈ L^o` and concludes about `L^o`, so it is vacuous unless `L^o ≠ ∅`, which the paper never records. | `SocialNetwork.ladderOf` supplies the witness — the staircase itself.  Blueprint `lem:ladder-nonempty`. |
| 2.3 | **Equation (6)** | The second condition is not stable under `π_α^{a,o}`, though the justification the paper gives for it proves a stronger condition that is. | Blueprint `rem:eq6`; the stronger condition is what `IsBiasedState` carries. |
| 2.4 | **Definition 4** | Needs a sign condition to be the set the proofs use. | Blueprint `rem:steep`; recorded, and the Lean definition carries it. |
| 2.5 | **Equation (13)**, the transfer | The statement takes *both* `μ` and `μ̃` as given and concludes the formula.  Combined with uniqueness for the skeleton it yields the **uniqueness** half of Theorem 1.2 — but not existence, since it presupposes that `μ` exists. | Not changed.  The converse direction — "the measure defined by (13) from `μ̃` is invariant for the semigroup" — is what the paper uses and is not what is stated.  **Your call** whether to restate it. |
| 2.6 | **Theorem 31** | Its route needs a biased analogue of Proposition 12, which does not exist: Proposition 12 is stated over `Pressure N M` and Theorem 31 lives over `Profile N M`.  Proposition 23 likewise has no biased analogues of Lemmas 19 and 20 to assemble from. | Nothing done.  See §3.2. |

---

## 3. The one axiom, and the second one you will need

### 3.1 Proposition 12 is a citation, not a theorem of this paper

`SocialNetwork.exitTime_approx_exponential` is declared as an `axiom`.  The paper
derives Proposition 12 from Theorem 5.3 of [LM22], a metastability estimate for a
general time-homogeneous strong Markov process.  Nothing inside this repository
can discharge it, so leaving it as a `sorry` would have made it look like work
someone could pick up.  CI now fails if any result claimed complete reaches it,
and a separate step records what is true only modulo it.

### 3.2 It cannot be stated once for both models

An earlier note in this project suggested stating Proposition 12 abstractly, over
an arbitrary family of measures and an arbitrary hitting time, so that Theorems 3
and 31 could share it.  **That suggestion was wrong: such an axiom is
inconsistent.**  Take the zero measure with an empty ladder set — (15)–(18) hold
vacuously and the conclusion fails at `t = 0`.  What excludes that is the strong
Markov property, which is the entire content of [LM22] and is not expressible
here.

So the axiom is attached to the concrete process, as the paper states it, and
**Theorem 31 will need its own twin.**  That is a second thing to trust, and it is
your decision whether to add it.

---

## 4. Steps asserted in the text, argued here

None of these is new mathematics and none needed a decision; they are recorded so
that you know where the written argument leaves a step to the reader.  The
blueprint's audit section classifies every formalised proof this way.

* **Remark 5.**  The paper writes the two inequalities defining `η` in one line
  and argues neither.  The comparison showing the worst case over `L̂` is attained
  on `L` rests on a monotone form of a gap in Mathlib.
* **Remark 5 iterated.**  The `m`-step bound `η^m` is used in the sketch of
  Proposition 9 without being derived.
* **Remark 8.**  The case `k ≥ 1` is supplied; the count `cₚ` the pigeonhole
  returns is kept rather than rounded to `⌈nₐ/M⌉`, which only enlarges the
  intermediate bound.
* **Proposition 6.**  The passage from the repeat time to the global bound, which
  the paper compresses into "this implies", is carried out explicitly.
* **Proposition 7.**  The "by definition" at the end; blueprint `rem:by-definition`.
* **Proposition 8.**  The iteration over `m`, which the paper does by conditioning
  in (10), goes through the Ionescu–Tulcea kernels — Mathlib offers no
  decomposition of that shape.  Same Markov property, different formalism.
* **Proposition 21.**  The quantity that resets and grows by one per step is `nₐ`,
  not the row supremum; the passage is `u (a, p) = cₚ(1+γ) - γnₐ ≤ nₐ`.
* **Theorem 3 / Section 5.3.**  Three steps: the inclusion `L ⊆ L^o ∪ C^{-o}`
  (the paper cites a bound about `L` for a condition about `L^o ∪ C^{-o}`); the
  supremum `sup_{β≥0} β e^{-β/a} = a e^{-1}` of step (20); and an explicit
  threshold above which `ε₁ + ε₂ ≤ 1/2`.  Proposition 12 also fixes an opinion
  while Theorem 3 quantifies over it, so the constants are taken uniform over the
  finitely many opinions.
* **Measurability.**  The paper does not address it anywhere.  Every measurability
  lemma here has no counterpart in the text.

---

## 5. Not the paper's fault

Unproved because Mathlib has no theory of it, not because anything is wrong:
Doeblin's minorisation criterion (Theorem 1.2, Theorem 25), Kac's lemma
(Proposition 9, Corollary 10, Proposition 26), Poisson point processes
(Theorem 1.1, Theorem 16), and the continuous-time analysis of Appendix B
(Lemma 14, Lemma 29).  `blueprint/blueprint.md` is the engineering audit of what
Mathlib does and does not provide, checked against the pinned revision.

One item is neither: `SocialNetwork.measurable_hittingTimeCts`.  The hitting time
is an infimum over an uncountable family of times, so it needs path regularity
that holds only almost surely.  **It wants a decision** — an almost-sure
formulation, or a proof that goes through the null set — and that decision is
about what the paper means, so it is yours.

---

## How this file stays honest

Every claim above is checked by the build.  A statement listed as unproved carries
a `sorry` and appears in the CI inventory; a statement listed as complete appears
in the CI axiom list and fails the build if it ever reaches `sorryAx` or the
[LM22] axiom.  If an item here is fixed, the blueprint and this file are updated
in the same commit as the code.
