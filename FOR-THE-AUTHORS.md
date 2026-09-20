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

Three files, three jobs.  [`STATUS.md`](STATUS.md) is the generated index: every
statement of the paper, whether it is proved, and — for the ones that are not — which
of five kinds of obstruction it has met.  It is rebuilt from the sources and checked by
CI, so it cannot drift.  The blueprint (`blueprint/src/content.tex`, chapter *Notes on
the formalisation*) holds the mathematics of each item.  **This file says what each one
asks of you**, and nothing else.

[`GL24.md`](GL24.md) reads the `M = 2` paper your proofs follow against this list:
which of the shortened steps are written out there, which are not, and which of
the requests below [GL24] has already answered.

---

## At a glance

**These need a decision.**  Nothing in the repository can move until you make it.

| | Statement | The problem | What we need from you |
|---|---|---|---|
| [§1.1](#1-proofs-that-do-not-survive-formalisation) | **Lemma 19** | the `⌊m⌋ + 1` distinct actors are asserted, never constructed, and the degenerate case is ruled out through the wrong hypothesis | the construction, and the corrected case split.  A proposal is in the blueprint, for you to check or reject |
| [§1.2](#1-proofs-that-do-not-survive-formalisation) | **Lemma 20** | the induction invariant is not preserved: the expressing actor's row is reset, and at the last step the bound is negative | an invariant that survives.  A proposal is in the blueprint |
| [§1.3](#1-proofs-that-do-not-survive-formalisation) | **Proposition 22** | does not follow from Proposition 6.  The transported bound is `N - 1 + 1/(2γ)`, below `N` only for `γ ≥ 1/2`, and here `γ < 1/(M-1)` | either a proof using the feedback `u(a,p) ≤ nₐ`, or the weaker constant `N + 1/(2γ)` carried through Propositions 23 and 17 |
| [§2.5](#2-statements-that-had-to-be-changed) | **Equation (13)** | as stated it takes both `μ` and `μ̃` as given, so with uniqueness it yields the *uniqueness* half of Theorem 1.2 and not existence | whether to restate it as the converse, which is what the paper actually uses |
| [§2.7](#2-statements-that-had-to-be-changed) | **Lemma 13** | rests on two inequalities displayed inside proofs and never stated; the numbered statements they are attributed to are limits, which have thrown the rate away | whether either display should become a numbered statement.  Only that: both are steps of your own proofs, [GL24] writes both out, and both are now proved here |

**These are recorded, and need nothing.**  Formalising turned each one up; the
repository has already taken the only route available, and says so at the declaration.

| | Statement | What was found |
|---|---|---|
| [§1.4](#1-proofs-that-do-not-survive-formalisation) | **Proposition 7** | the written route carries `⋃_o S^o` from `τ(u)` to `N+1`, which needs a stability the paper never proves.  Applying Lemma 20 where Lemma 19 lands removes the need, with your arithmetic unchanged.  **Proved** |
| [§1.6](#1-proofs-that-do-not-survive-formalisation) | **Proposition 9** | "without visiting `u`" does not come from Proposition 7, and was the fourth item needing a decision.  It is Corollary 8 of [GL24], and the argument is now written out and machine-checked.  **Proved** modulo Lemmas 19 and 20 |
| [§1.5](#1-proofs-that-do-not-survive-formalisation) | **Lemma 28** | the biased twin of Lemma 13, so it inherits Lemma 13's two missing displays in biased form |
| [§2.1](#2-statements-that-had-to-be-changed) | **Proposition 12** | with `ε₁ ε₂ s₁ s₂` bound ahead of `β`, the hypotheses are unsatisfiable and Theorem 3 could never have followed.  Made functions of `β` |
| [§2.2](#2-statements-that-had-to-be-changed) | **Corollaries 15 and 30** | vacuous unless `L^o ≠ ∅`, which is nowhere recorded.  Witnesses supplied; both now proved |
| [§2.3](#2-statements-that-had-to-be-changed) | **Equation (6)** | the second condition is not stable under `π_α^{a,o}`, though your justification for it proves a stronger one that is |
| [§2.4](#2-statements-that-had-to-be-changed) | **Definition 4** | needs a sign condition to be the set the proofs use |
| [§2.6](#2-statements-that-had-to-be-changed), [§3.3](#3-the-two-axioms) | **Theorem 31** | its route needs a biased Proposition 12, which the paper does not state.  Declared as a second axiom; Theorem 31 is **proved** from it |
| [§2.8](#2-statements-that-had-to-be-changed) | **Proof of Lemma 13** | `τ` is exponential of mean `1/(MN)`, so `P(τ > β) = e^{-MNβ}`; the proof writes `e^{-β/(MN)}`.  Harmless — the written form is the weaker one |
| [§3](#3-the-two-axioms) | **Proposition 12, twice** | it is Theorem 5.3 of [LM22], not a result of this paper, and cannot be stated once for both models without becoming inconsistent |
| [§5](#5-not-the-papers-fault) | **Remark 6** | was the one numbered statement with no Lean counterpart.  Now stated and **proved**, outright: its route needs only the last stage of Proposition 7, not Lemmas 19 and 20 |
| [§5](#5-not-the-papers-fault) | **Measurability of `R^{β,u}(θ)`** | was listed here as needing a decision from you.  It did not: the diagnosis was wrong and it is now **proved**, for every realisation |
| [§2.10](#2-statements-that-had-to-be-changed) | **Proposition 9** | the statement quantifies over `u ∉ L̂` with no other hypothesis, but its proof calls Proposition 7, which is stated on `S` | `IsState u` added.  The paper works in `S` throughout |
| [§5](#5-not-the-papers-fault) | **Doeblin, page 17** | the criterion and this chain's minorisation are both now **proved**, so `μ̃^β` is unique unconditionally and only *existence* is missing.  Your `ε*` becomes an explicit constant, and (12) is proved from *any* matrix — which is what lets the minorising measure be a single Dirac mass |
| [§5](#5-not-the-papers-fault) | **Kac's lemma** | was listed as a gap in Mathlib blocking Proposition 9 and four results below it.  It was not: the proof needs only the *inequality*, which holds for every invariant measure and is now **proved** outright |
| [§2.11](#2-statements-that-had-to-be-changed), [§5](#5-not-the-papers-fault) | **Corollary 11** | our Lean statement of it was **false**: it rendered the independent `τ` as a supremum, whose `s = 0` term tends to one.  Restated with the process's own first jump time, which is the reading your equation (19) uses, and **proved** under it |
| [§5](#5-not-the-papers-fault) | **Theorem 4, part 1** | the "strong Markov property at `T_N`" is the *simple* one: for the skeleton `T_N` is a deterministic index.  Mathlib has no strong Markov property, and none was needed.  **Proved** |

---

## 1. Proofs that do not survive formalisation

Three written proofs do not compose — §§1.1–1.3.  Each is left unproved on
purpose.  A repair is new mathematics and is yours to write, not the
formalisation's to guess.

Three more belong here for different reasons.  **Proposition 7** (§1.4) composes
only along a different route; the missing step turned out to be avoidable, so it
is proved, but you should know the written route does not run.  **Lemma 28**
(§1.5) is blocked one level up, on ingredients Lemma 13 needs that the paper
displays inside proofs rather than states.  And **Proposition 9** (§1.6) stood
here as a fourth item needing a decision, for one clause of one sentence; it does
not any more, because [GL24] states that clause as its Corollary 8.

### 1.1 Lemma 19 — the `⌊m⌋ + 1` distinct actors

*Blueprint:* `note-lem19`. *Lean:* `SocialNetwork.isFavouring_state_firstRepeat`.

The written proof asserts, "by (25)", a sequence of `⌊m⌋ + 1` distinct actors
without giving the construction, and rules out the degenerate case `m = 0` through
`τ (u) = 2` rather than through `m = 0` itself.

**What is needed:** the construction, and the corrected case split.  The blueprint
records a first-passage decomposition of the backward walk that does produce the
actors, and the case split that works — but as a *proposal for you to check*, not
as something the formalisation has adopted.

### 1.2 Lemma 20 — the induction invariant is not preserved

*Blueprint:* `note-lem20`. *Lean:* `SocialNetwork.isConsensus_state_of_favouring`.

The invariant of the written proof, `Ũₖ (a, p) ≤ n(u) + r - (k+1)/(M-1)` for
`p ≠ o`, is not preserved: the actor that expresses at step `k` has its row reset
to `0`, and at the terminal `k` the bound is negative.

**What is needed:** a preserved invariant.  The blueprint proposes
`max (0, n(u) + r - (k+1)/(M-1))` together with a staircase mechanism that
replenishes the witnesses, again as a proposal to check.

### 1.3 Proposition 22 — does not follow from Proposition 6

*Blueprint:* `note-prop22`. *Lean:* `SocialNetwork.Bias.entry_mem_of_nearGreedy`.

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

*The contrast is sharp, and worth having in front of you.*  **Proposition 17 is
now proved**, and its deterministic half is the same two-case argument over the
same quantity `nₐ`.  It closes because its event `ξ` is *exact* greediness: the
maximum at the repeat time is the expressing actor's own entry, and there is
nothing to absorb.  Proposition 22 differs from it only by the slack, and that
is precisely what the argument cannot carry.

### 1.4 Proposition 7 — the written route needs a step that is not there

*Blueprint:* `prop7`. *Lean:* `SocialNetwork.isLadder_state_of_greedy`,
**proved** (modulo Lemmas 19 and 20).

The written proof has three stages and its arithmetic is right.  What it does not
have is the glue between the first two.

Lemma 19 delivers `Ũ_{τ(u)} ∈ ⋃_o S^o` at the first repeat `τ(u)`.  The proof of
Proposition 7 then writes

> so by Lemma 19 we have `⋂_{j=1}^{N+1} ξ_j^u ⊆ {Ũ_{N+1} ∈ ⋃_o S^o}`

— that is, it carries the membership from `τ(u)` up to `N+1`, using only
`τ(u) ≤ N+1`.  That carry needs **`⋃_o S^o` to be stable under a greedy
expression**, which is neither stated nor proved anywhere.

It is not a formality.  A greedy expression in `S^o` does express `o`
(Lemma 21 of the formalisation's numbering — `opinion_eq_of_isMax_of_favouring`),
but it resets the row of the expressing actor, and that actor may be one of the
witnesses `a₁(u), …, a_{n(u)}(u)`.  New witnesses have to be produced from the
actors that just gained a unit on column `o`, and the bound
`u(a,p) ≤ n(u) + r - 1/(M-1)` on the other columns then has to be re-established
with the *new* `n` and `r`.  That is exactly the bookkeeping of Lemma 20, whose
written invariant does not survive either (§1.2).

**What was done, and why it is not a repair you have to check.**  Lemma 20 is
applied where Lemma 19 actually lands — at `τ(u)` — instead of at `N+1`.  Then no
stability of `S^o` is needed at all, and the arithmetic is yours, unchanged:

```
τ(u) + (M-1)(n(u)+1) - 1  ≤  (N+1) + (M-1)N - 1  =  MN.
```

The written proof needs a *second* carry of the same kind, from
`N+1 + (M-1)(n(u)+1) - 1` up to `MN`, and that one is unavoidable — the last stage
must start at `MN` for the total to be `(M+1)N`.  It is also available: it is your
own observation from the last stage of this same proof, that a greedy expression
in `C^o` expresses `o` and that `C^o` is stable under it.  So the formalisation
keeps that carry and drops the other.

**Nothing here needs a decision.**  It is recorded because the paper as printed
asserts a step that does not follow, and you may want either to add the `S^o`
stability lemma or to restate Proposition 7's proof along the shorter route.

### 1.5 Lemma 28 — inherits Lemma 13's missing displays

*Blueprint:* `lem28`. *Lean:* `SocialNetwork.Bias.biasedProbHitting_le`.

Lemma 28 is Lemma 13 with `1/((M+1)N)` replaced by `1/(2γ)`, and Appendix C gives
it no proof of its own.  Lemma 13's proof runs on two inequalities the paper
displays inside proofs and never states (§2.7); the biased proof needs those two
in biased form, and they are not in the paper either.

So Lemma 28 is unproved not because its own argument fails but because the
argument it is told to copy rests on statements that do not exist.  Once §2.7 is
settled the same two transcriptions serve here, and its remaining ingredients —
Propositions 22 and 23 — are §1.3.

The Lean statement was also wrong, and that was a fault of this repository rather
than of the paper; it is now restated in the paper's own form.  See §2.9.

### 1.6 Proposition 9 — "without visiting `u`" does not come from Proposition 7

*Blueprint:* `aux-greedy-avoids`. *Lean:* `SocialNetwork.skeleton_ne_of_greedy`.
*Proposition 9 itself:* `SocialNetwork.measure_le_of_notMem_steepLadderSet`,
**proved** modulo this one step (and, through Proposition 7, modulo Lemmas 19
and 20).

The proof of Proposition 9 bounds the return time below by

> we first consider Proposition 7 to show that a sequence of events `ξ_j^u`,
> `j = 1, …, (M+1)N`, leads the process to `L`, **without visiting `u`**, with a
> lower bounded probability.

Proposition 7 says where the greedy run *ends* — at a ladder, after `(M+1)N`
expressions — and says nothing about where it passes.  The clause is needed:
Kac's inequality bounds `μ̃^β(u)` by the probability of avoiding `u` at *every*
one of the first `m` times, so a single return inside the transient makes the
event empty and the bound vacuous.

After the run has reached `L̂` the claim is immediate, and that part is
formalised: the process stays in `L̂` (Remark 5) and `u ∉ L̂`.  What is missing is
only the times `1 ≤ k < (M+1)N`.

**It is not a formality.**  Greedy runs do return to matrices they have already
visited: from a ladder they cycle with period `N`, three of them for `N = 3`,
`M = 2`.  So the hypothesis `u ∉ L̂` is doing work, and an argument that rules out
a return has to use it.  A monotone quantity will not do it either — the maximum
entry can fall along a greedy step, and on the ladder cycle every symmetric
function of the matrix is constant.

**This no longer needs anything from you.**  It is Corollary 8 of [GL24], stated
there for `M = 2` and proved "directly by Part 2 of Proposition 5, by
contradiction".  Written out: suppose the run returns to `u` at step `k`, and
repeat its first `k` expressions for ever.  The greedy event at a step reads only
the matrix and the expression at that step, and the repeated realisation has the
same state at `n` as the original at `n mod k` — which is where the return is
used — so it is greedy at *every* step and sits at `u` at every multiple of `k`.
Proposition 7 puts it on `L` at step `(M+1)N`; a greedy expression on a steep
ladder is made from a positive entry, so Remark 5 keeps it on `L̂` from there on,
including at the multiple `k(M+1)N`.  Hence `u ∈ L̂`, against the hypothesis —
and the hypothesis is used exactly once, at that last step.

The argument is deterministic, so it needed no restart and no Markov property,
and it is stated on one realisation.  **Proved**; Proposition 9 now rests only on
Lemmas 19 and 20, through Proposition 7.  [`GL24.md`](GL24.md) §2.1 records how
it was found.

---

## 2. Statements that had to be changed

These are not gaps in reasoning; they are places where the statement as written
cannot be used, and the Lean statement differs from the paper's display.

| # | Where | What is wrong | What was done |
|---|---|---|---|
| 2.1 | **Proposition 12**, (15)–(18) | `ε₁ ε₂ s₁ s₂` are introduced before `β`, but Section 5.3 instantiates them at `s₂ = 2β` and `ε₂ = (M+1)²N²e^{-β/((M+1)N)}`, and needs `ε₁ + ε₂ ≤ 1/2` only "for β sufficiently big".  Bound as constants ahead of `β`, **the hypotheses are unsatisfiable** — Theorem 3 could never have been derived from them. | Made functions of `β`; (15)–(18) required only above a threshold `β₁`.  Theorem 3 now follows. |
| 2.2 | **Corollary 15** (and 30) | Quantifies over `l ∈ L^o` and concludes about `L^o`, so it is vacuous unless `L^o ≠ ∅`, which the paper never records. | `SocialNetwork.ladderOf` and `SocialNetwork.Bias.biasedLadderOf` supply the witnesses — the staircase itself, and the profile in which actor `a` has heard exactly `a` expressions of `o`.  Blueprint `aux-ladder-nonempty` and `aux-biased-ladder-nonempty`.  Both corollaries are now proved. |
| 2.3 | **Equation (6)** | The second condition is not stable under `π_α^{a,o}`, though the justification the paper gives for it proves a stronger condition that is. | Blueprint `note-eq6`; the stronger condition is what `IsBiasedState` carries. |
| 2.4 | **Definition 4** | Needs a sign condition to be the set the proofs use. | Blueprint `note-def4`; recorded, and the Lean definition carries it. |
| 2.5 | **Equation (13)**, the transfer | The statement takes *both* `μ` and `μ̃` as given and concludes the formula.  Combined with uniqueness for the skeleton it yields the **uniqueness** half of Theorem 1.2 — but not existence, since it presupposes that `μ` exists. | Not changed.  The converse direction — "the measure defined by (13) from `μ̃` is invariant for the semigroup" — is what the paper uses and is not what is stated.  **Your call** whether to restate it. |
| 2.6 | **Theorem 31** | Its route needs a biased analogue of Proposition 12, which the paper does not state: Proposition 12 is over `Pressure N M` and Theorem 31 lives over `Profile N M`.  Proposition 23 likewise has no biased analogues of Lemmas 19 and 20 to assemble from. | The analogue is now declared as a second axiom and **Theorem 31 is proved** from it.  See §3.3.  Proposition 23 is untouched. |
| 2.7 | **Lemma 13** | Its proof rests on two inequalities the paper displays but never states: the bound on `P (R^{β,u} (L) > t)` inside the proof of part 2 of Theorem 2, and equation (19), which reads Corollary 11 quantitatively.  Theorem 2.2 and Corollary 11 are *both* stated only as limits, and a limit has thrown the rate away, so **Lemma 13 does not follow from the numbered statements it cites**. | The two displays are transcribed verbatim as Lean statements of their own — `probHittingGT_ladderSet_le_of_ne_zero` and `probHittingGT_ladderSet_zero_le`, blueprint `aux-hitting-rate` and `eq19` — each carrying a `sorry`, and Lemma 13 is proved from them.  They were filed here as *citations from outside the paper*, which was wrong: they are steps of your own proofs of part 2 of Theorem 2 and of Corollary 11, and [GL24] writes both out at its p. 19 — the first as its equations (16)–(18), the second as its Corollary 13.  Both are now **proved**: the first along the [GL24] argument, modulo Lemmas 19 and 20; the second outright, from a restart of the continuous-time process at its first jump (§4).  **Your call** whether either should become a numbered statement of the paper. |
| 2.8 | **Proof of Lemma 13**, the term `P (τ > β)` | `τ` is declared exponential of mean `1/(MN)`, for which `P (τ > β) = e^{-MNβ}`; the proof writes `e^{-β/(MN)}`. | Harmless, and no decision needed: `e^{-MNβ} ≤ e^{-β/(MN)}` for `β ≥ 0`, so the written form is the weaker of the two and Lemma 13 follows from either.  The Lean statement uses the written form, so it assumes the weaker one. |
| 2.9 | **Lemma 28**, as formalised | The Lean statement was about the skeleton path measure and the discrete steps `k ≤ ⌈2β⌉`, not the continuous-time hitting time `R^{α,β,u}`, and it bound `C` *after* `β` and `u`, so the constant could depend on both.  It therefore could not serve as (16) for the biased Proposition 12, which is what the lemma exists for. | Restated in the shape of Lemma 13 with `1/((M+1)N)` replaced by `1/(2γ)`, and `C` quantified in front.  **A formalisation-side correction, not a correction to the paper** — the paper's display was right all along. |
| 2.10 | **Proposition 9** | The statement quantifies over `β > 0` and `u ∉ L̂`, with no hypothesis on `u` beyond that; its proof calls Proposition 7, which is stated for `u ∈ S`, and the whole paper works in `S`. | `IsState u` added to the Lean statement.  Also stated for an *arbitrary* invariant probability measure of the skeleton rather than for a named `μ̃^β`, since its existence is Theorem 1.2 — which, with Kac's inequality in place of Kac's identity, Proposition 9 no longer needs. |
| 2.11 | **Corollary 11**, as formalised | The Lean statement rendered "`τ` exponential of mean `1/(MN)`, independent from `(U_t^{β,u})_t`" as a supremum over `s ≥ 0` of `e^{-MNs} · P(R^{β,0}(L) > s + ε_β)`.  Its `s = 0` term is `P(R^{β,0}(L) > ε_β)` at weight `1`, which tends to **one**, so the statement was **false**. | Restated as `P(R^{β,0}(L) > T₁ + ε_β) → 0` with `T₁` the process's own first jump time — `probHittingGTAfterFirstJump` — which from `0` is exponential of mean `1/(MN)` (`totalRate_zero`, now proved).  **A formalisation-side correction, not a correction to the paper.**  But see the reading below: your `τ` has to be `T₁`, and the sentence can be read otherwise. |

---

## 3. The two axioms

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
Theorem 31 needs its own twin.

### 3.3 The twin, added on your instruction

`SocialNetwork.Bias.biasedExitTime_approx_exponential` is the same statement over
`Profile N M` instead of `Pressure N M`.  Appendix C never states it: it says only
that "the proof of Theorem 31 follows exactly as the proof of Theorem 3", and that
proof runs through Proposition 12, which is stated for the unbiased process alone.

**So the repository now asks you to trust two things, not one**, and they are the
same citation applied twice.  If [LM22] Theorem 5.3 is right, both are right; the
duplication is a limitation of what can be *stated* here, not a second
mathematical assumption.  Should you prefer a single hypothesis, the way to get it
is to formalise enough of the strong Markov property that the abstract version
stops being vacuous — that is real work, and it is the only honest route.

CI gates both: no result claimed complete may reach either, and the inventory step
now records what is true modulo each of them separately.

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
* **Proposition 9, the composition.**  The greedy run of Proposition 7 and the
  positive expressions of Remark 5 are composed on the realisation — the two are
  one event of the sample space — rather than by restarting the chain at time
  `(M+1)N`, which is how the paper reads it.
* **Proposition 9, the constant.**  Reaching the printed `C' = (NM)^{(M+1)N+1}`
  needs the regime `MN e^{-β/(M-1)} > 1` treated separately: there `C'` already
  exceeds `e^{β(N-1)}` and `μ̃^β(u) ≤ 1` suffices.  The paper does not split.
* **Remark 8.**  The case `k ≥ 1` is supplied; the count `cₚ` the pigeonhole
  returns is kept rather than rounded to `⌈nₐ/M⌉`, which only enlarges the
  intermediate bound.
* **Proposition 6.**  The passage from the repeat time to the global bound, which
  the paper compresses into "this implies", is carried out explicitly.
* **Proposition 7.**  The "by definition" at the end; blueprint `note-prop7`.
* **Proposition 8.**  The iteration over `m`, which the paper does by conditioning
  in (10), goes through the Ionescu–Tulcea kernels — Mathlib offers no
  decomposition of that shape.  Same Markov property, different formalism.
* **Corollary 11 and equation (19), the restart.**  Both read the process after
  its first expression — "conditionally on the first jump" — and the paper does
  not say in what sense.  In Lean it is the Markov property at the first jump for
  the jump–hold representation, proved from the construction: one step of the
  driving kernel keeps the history and appends a step drawn at the matrix that
  history reaches, so dropping the first entry of a history shifts that reading by
  one.  The corresponding statement about hitting times,
  `R^{β,u}(θ)(ω) ≤ T₁(ω) + R^{β,v}(θ)(σω)`, needs every holding time positive,
  which is almost sure, and splits on the jump counter: on the explosion event the
  counter is junk on both sides, and there the matrix at stake is the one the first
  expression reaches, shown at `T₁` itself.  Theorem 1.1 would remove that case.
* **Proposition 21.**  The quantity that resets and grows by one per step is `nₐ`,
  not the row supremum; the passage is `u (a, p) = cₚ(1+γ) - γnₐ ≤ nₐ`.
* **Propositions 17 and 24.**  Appendix C invokes the proofs of Propositions 6
  and 8 in one sentence each, and for these two that is right.  The iteration
  common to both is run once in Lean, for an arbitrary choice of admissible
  pairs at each profile, since neither uses anything else about its event.
* **Theorem 3 / Section 5.3.**  Three steps: the inclusion `L ⊆ L^o ∪ C^{-o}`
  (the paper cites a bound about `L` for a condition about `L^o ∪ C^{-o}`); the
  supremum `sup_{β≥0} β e^{-β/a} = a e^{-1}` of step (20); and an explicit
  threshold above which `ε₁ + ε₂ ≤ 1/2`.  Proposition 12 also fixes an opinion
  while Theorem 3 quantifies over it, so the constants are taken uniform over the
  finitely many opinions.
* **Lemma 13.**  "Putting the inequalities above together" is the comparison of
  each of the three terms with `e^{-β/((M+1)N)}` — using `MN ≤ (M+1)N`,
  `M - 1 ≤ (M+1)N` and `e^{β/(M-1)} ≥ 1` — which leaves the integer inequality
  `1 + (M+1)N ≤ (M+1)N²`, true since `N ≥ 3`.  It is tight enough to be worth
  writing down: the greedy term alone already uses `M(M+1)N²` of the `(M+1)²N²`
  available.
* **Corollary 30.**  Appendix C gives it as "the rearrangement of Corollary 15
  with `1/(M-1)` replaced by `1/(2γ)`", and it is exactly that; the Lean proof is
  Corollary 15's, transposed.
* **Theorem 31.**  Appendix C says only "the proof follows exactly as the proof of
  Theorem 3", and names none of the constants.  The four taken here are what
  Section 5.3 produces with `1/(2γ)` in place of `1/(M-1)`: `s₁ = 1`,
  `ε₁ = 2N³(M+1)³e^{-β/(2γ)}`, `s₂ = 2β`, `ε₂ = Ce^{-β/(2γ)}` with `C` from
  Lemma 28, and `δ = θ = 1/(4γ)` — the exponent halved to absorb the factor `β` of
  step (20), which is why the two coincide here where the unbiased proof had
  `1/((M+1)N)` and `1/(2(M-1))`.  The threshold above which `ε₁ + ε₂ ≤ 1/2` is
  `β₁ = max(1, 4γ(2N³(M+1)³ + C))`.
* **Measurability.**  The paper does not address it anywhere.  Every measurability
  lemma here has no counterpart in the text.

---

## 5. Not the paper's fault

Unproved because Mathlib has no theory of it, not because anything is wrong:
the existence of the invariant measure `μ̃^β` (Theorem 1.2, part 1 of Theorem 2,
Theorems 25 and 27), Poisson point processes (Theorem 1.1, Theorem 16), and the
continuous-time analysis of Appendix B (Lemma 14, Lemma 29).  `blueprint/blueprint.md` is the engineering
audit of what Mathlib does and does not provide, checked against the pinned
revision.

The first of those is now down to one half.  The **criterion** is proved here
(`SocialNetwork/Doeblin.lean`), for a general Markov kernel on a countable
space: if some iterate is bounded below at one state by `c > 0`, uniformly over
a set carrying the measures, there is at most one invariant probability measure
carried by that set.  This chain's **minorisation** — your page 17 — is proved
here as well (`SocialNetwork/Minorisation.lean`), so **the skeleton has at most
one invariant probability measure carried by `S`, unconditionally**
(`eq_of_invariant_skeletonKernel`).  What is left at Theorem 1.2 is
**existence**, and that alone: the construction of an invariant measure from one
excursion of a positive recurrent chain, which is theory Mathlib lacks.

Two remarks on the minorisation, neither of them a request.  Your `ε*` is a
minimum over the finite set of bounded matrices of a probability you do not
compute; the Lean proof has the explicit `e^{-2βR/(M-1)}/MN` per expression
instead, with `R = MN(M-1) + N(M-1)`, since the rates of (3) are exponentials of
bounded exponents — so `ε* ≥ (e^{-2βR/(M-1)}/MN)^N` and the finite set is never
exhibited.  And (12) is proved in the form it is actually used in: the `N`
expressions of `o` in decreasing actor order send **any** matrix to `l^o`, with
no hypothesis on where they start.  That is what lets the minorising measure be
a single Dirac mass, which is what the criterion consumes; it is worth stating
that way if you revise.

Nothing is unproved for neither reason any more.  **Every numbered statement of
the paper is now stated in Lean**, and what is unproved is blocked on Mathlib,
blocked on the paper, or cited from outside it.

There were three in this group.  **Corollary 11** was filed under Doeblin and
**equation (19)** as a citation; reading part 2 apart from part 1 moved both, and
part 2 and the first display of §2.7 with them.  Part 2 says nothing about the
invariant measure, so nothing it needed was missing from this repository: what it
wanted was the clock, and the clock is the construction's own
(`aux-holding-times` in the blueprint).  What Corollary 11 and equation (19)
wanted beyond that was one lemma, the restart of the process at its first jump
(§4).  The third was **Remark 6**, the one numbered statement with no Lean
counterpart at all.

Two of the three turned out to be provable **outright**, and in both cases
because the route this repository had assumed was not the route: equation (19)
does not pass through part 2 of Theorem 2 (the supremum it bounds by is on its
own right-hand side), and Remark 6 needs only the *last* stage of Proposition 7
— consensus to a ladder, which is proved — because it starts inside `C^o`, and
getting to `C^o` is exactly what Lemmas 19 and 20 are for.  Corollary 11 does use
part 2 and inherits its `sorry`.

None of what is proved there is proved *outright*: part 2 and the display rest
on Proposition 7, hence on Lemmas 19 and 20, and turn green with no edit the
moment those do.  What changed is what the rest is waiting for: work here,
rather than a contribution to Mathlib or a decision from you.

**Corollary 10**, which stood here until the description of the states from
which the zero matrix can be entered was written out, is now proved modulo
Proposition 9: the description is exhaustive because the invariant measure
charges only matrices with a null row, and the extra exponent `1/(M-1)` is what
the step into the zero matrix costs against the normalisation of the rates.

### Kac's lemma: listed as a gap in Mathlib, and it was not one

This section used to say that Proposition 9, Corollary 10 and Proposition 26
were blocked because **Mathlib has no Kac lemma**.  The first half is true —
every `Kac` in Mathlib is a Kac--Moody algebra — and the conclusion was wrong.

The proof of Proposition 9 opens with the *identity*
`1/μ̃^β(u) = E[R̃^{β,u}(u)]`, and the identity really does need the chain to be
irreducible, so reading it as a citation of Theorem 1.2 was reasonable.  But the
proof goes on to use only

```
μ̃^β(u) · E[R̃^{β,u}(u)] ≤ 1,
```

since what it wants is an *upper* bound on `μ̃^β(u)`.  **That inequality holds
for every invariant probability measure**, with no irreducibility, no recurrence
and no existence theorem: the events "the last visit to `u` before time `m` was
at time `j`", `j < m`, are disjoint, and stationarity gives each of them
probability `μ̃^β(u) · P_u(R > m-1-j)`.  Only the identity needs the union of
those events to have full measure, which is where ergodicity comes in.  The
counterexample to the identity without it is two absorbing states with
`μ̃ = (½, ½)`, where the return time is `1` and `1/μ̃` is `2`.

`SocialNetwork/Kac.lean` proves the inequality outright, for a Markov kernel on
a countable space, in about a hundred lines and using nothing from Mathlib
beyond `Kernel.Invariant` and the Lebesgue integral.  So Proposition 9 waits on
neither Mathlib nor Doeblin, and §1.6, the one thing it did wait on, is now
proved as well.

The lesson is the one below, again: **a citation is not an obstruction until one
has checked which half of it the proof needs.**

### Measurability of the hitting times: a decision we asked for and did not need

An earlier version of this file put `SocialNetwork.measurable_hittingTimeCts`, and
its biased twin, in the table above: the hitting time is an infimum over an
uncountable family of times, reducing it to a countable one appeared to need
right-continuity of `t ↦ U_t (ω)`, and right-continuity holds only almost
surely — so, we said, the statement wanted an almost-sure formulation, and the
choice was yours.

**Both are now proved, for every realisation, with the statement unchanged.**  The
mistake was to take one route to the reduction for the only one.  Write
`S (t) = {n : Tₙ ≤ t}`, so the jump count at `t` is `sup S (t)`.  Where `S (t)` is
bounded, `k = sup S (t)` lies in `S (t)` and bounds it, so `max (T_k, 0) ≤ t` and
the jump count there is again `k`: the infimum over that level set is *attained*,
at a time named by `k` alone.  Where `S (t)` is unbounded — the explosion event —
every larger time has `S` unbounded too, so every rational above `t` sits in the
same level set.  The countable family `{max (T_k, 0)} ∪ (ℚ ∩ [0, ∞))` therefore
meets the infimum outright.  Nothing in it mentions the holding times, which is
why the biased twin costs one line.

Nothing was asked of you and nothing is now.  It is recorded because this file
had claimed otherwise, and a claim of ours that turned out to be wrong belongs
here as visibly as one about the paper.

### Corollary 11: our transcription was false, and one word of yours decides it

Found while trying to prove it.  The Lean statement was ours and it was wrong;
that is §2.11 and it is now repaired.  What is worth a line to you is *why* the
repair had only one possible shape.

Corollary 11 reads `P(R^{β,0}(L) > τ + e^{-β(1-δ)/(M-1)}) → 0`, "where `τ` is an
exponentially distributed random variable with mean `1/(MN)` independent from
`(U_t^{β,u})_t`".  Everything turns on that superscript `u`.  Read as you use it
in equation (19) — `τ` is the process's own first jump time from `0`, and the
independence asserted is from what happens *after* it, from the state `u` it
lands on — the corollary is true and is exactly Theorem 2, part 2, applied at
`u`.  That is the reading the Lean statement now carries.

Read as "`τ` independent of the process", full stop, the corollary is **false**.
From `0` we have `0 ∉ L`, so `R^{β,0}(L) ≥ T₁`, and `R^{β,0}(L) = T₁ + O(ε_β)`;
the left-hand side then tends to `P(T₁ > τ)` with `T₁` and `τ` independent, both
exponential of rate `MN` — which is `1/2`.

**Nothing is asked of you**, and nothing in the paper needs changing: your proof
of Lemma 13 uses the right reading.  It is recorded because the sentence as
written admits a reading under which the corollary fails, and a formalisation is
the kind of reader that takes it.  Under the right reading the corollary is now
proved, and so is equation (19).

**Remark 6** was the one numbered statement of the paper with no Lean
counterpart, and it now has one: `tendsto_probHittingLadderFirst`, proved
outright.  Two notes on it, neither asking anything of you.

The horizon is `N`, not `(M+1)N`.  "By following the same steps of the proof of
part 2 of Theorem 2" is exactly right, but the steps have to be run from `C^o`
and stopped at `N`: continuing a greedy run past a ladder expresses the same
opinion again and leaves `L^o`, so part 2's bound — which concludes `L`, not
`L^o` — cannot be quoted as it stands.  What Remark 6 uses is the last stage of
Proposition 7 on its own.

And that is why it is proved outright while part 2 is not.  This repository had
filed Remark 6 behind Lemmas 19 and 20, on the grounds that its route is part 2
and part 2 rests on them.  It does not: starting inside `C^o` skips them, since
getting to `C^o` is their whole job.  Nothing downstream uses Remark 6 — it
strengthens Corollary 11 in the direction Lemma 14 needs — but it is the only
statement of Section 5.2 that this repository can offer you sorry-free: part 1 of
Theorem 2 waits on `μ̃^β` existing, and part 2 and Corollary 11 on Lemmas 19
and 20.

**Theorem 4** part 1 is now **proved**, and with it the negative-bias half of the phase
transition: almost surely all but one actor eventually stop expressing. Proposition 18
supplies the uniform chance of settling, Proposition 17 carries it from `B_N^α` to the whole
of `S^α`, and the failure-time recursion closes it.

Two of its steps were supplied rather than read off the paper, and both are recorded at the
node in the blueprint. The first is the Markov property. You write "the strong Markov
property at time `T_N`", but part 1 is a statement about the sequence `(A_n)` — about the
skeleton — and for the skeleton `T_N` is the *deterministic* index `N`; so what is used
there is the simple Markov property. At the failure times a real stopping time does appear,
and for a discrete-time chain the strong Markov property follows from the simple one by
decomposing over its countably many values. Nothing was assumed that you did not use; it is
only that the proof names a stronger tool than the argument needs, and Mathlib has no strong
Markov property to hand it. The second supplied step is that `{η_n < ∞}` is measurable for
the past at `η_n`, which here is the statement that each failure event is decided by the
expressions that precede it.

One reorganisation is worth flagging, since it is visible in the Lean. Your recursion gives
`P(η_{n+1} < ∞) ≤ (1-c) P(η_n < ∞)` and concludes by letting `n → ∞`. That limit is exactly
`q = sup_{v ∈ S^α} P_v(no actor is eventually alone)`, and the single inequality the
recursion uses gives `q ≤ (1-c) q` in one step. The estimate, the time it is applied at and
the constant are yours; only the bookkeeping of the recursion is replaced by the fixed point
it converges to. Say the word if you would rather see the `η_n` written out.

Two smaller notes. Theorem 16 is **not** needed for part 1: the statement is about the
sequence of expressed pairs, and non-explosion is what makes the continuous-time process well
defined. And your part 1 indexes from 1, the formalisation from 0, so where you write
`⋂_{m ≥ N+1} {A_m = A_{N+1}}` the Lean reads `∀ m ≥ N, A_m = A_N`.

With this closed, and with **Corollary 11**, **equation (19)** and **Remark 6**
since written, nothing is left in the repository that is nobody's fault.

---

## How this file stays honest

Every claim above is checked by the build, and the checking is no longer done by
hand.

[`STATUS.md`](STATUS.md) is generated from `blueprint/src/content.tex` and the
Lean sources by `scripts/status.py`, and CI regenerates it and fails on any
difference.  The same script refuses a `sorry` that no blueprint node accounts
for, a Lean name the blueprint cites but the library does not declare, and an
unproved statement with no recorded reason — so an obstruction cannot be
introduced without appearing here.

The axiom check is generated the same way: it is every declaration cited by a
node the blueprint's dependency graph resolves to *proved*, or to a definition
with nothing to prove, and the build fails if any of them reaches `sorryAx` or
either [LM22] axiom.  A green node in
the blueprint is therefore a claim the build verifies, not a claim someone
remembered to keep true.

If an item here is fixed, the blueprint and this file are updated in the same
commit as the code.
