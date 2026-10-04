# Notes for the authors

For Felipe Penafiel and Kádmo Laxa.  This file lists what formalising arXiv:2607.19651
found in the paper.  §1 is what needs a decision: one statement that is false as
printed, one whose proof rests on statements the paper does not give, and the citation
the repository has to assume.  §2 lists the misprints and gaps found along the way,
none of which affects a result.

Everything not listed here is proved; [`STATUS.md`](STATUS.md) gives the status of
every statement.  Each entry names the blueprint node that holds the mathematics.

| | Statement | What was found |
|---|---|---|
| [§1.1](#11-lemma-20-is-false-as-printed-for-m--4) | **Lemma 20** | false as printed for `M ≥ 4`; Proposition 7 and everything after it are written from it |
| [§1.2](#12-proposition-23-rests-on-statements-the-paper-does-not-give) | **Proposition 23** | its proof goes through biased analogues of Lemmas 19 and 20 that the paper does not state |
| [§1.3](#13-proposition-12-is-assumed-twice) | **Proposition 12** | a citation of [LM22], declared as an axiom — once for each model |
| [§2.1](#21-equation-6) | Equation (6) | the second condition is not stable under `π_α^{a,o}` |
| [§2.2](#22-proposition-7) | Proposition 7 | the written route needs `⋃_o S^o` to be stable, which fails for `M ≥ 4`; the final "by definition" hides an argument |
| [§2.3](#23-proposition-9) | Proposition 9 | "without visiting `u`" does not follow from Proposition 7; the hypothesis `u ∈ S` is missing |
| [§2.4](#24-equation-13) | Equation (13) | as stated it gives uniqueness in Theorem 1.2, not existence |
| [§2.5](#25-the-proof-of-theorem-21) | Proof of Theorem 2.1 | `ζ_β^{(M+1)N} ≥ (MN)^{-(M+1)N}` fails for small `β` |
| [§2.6](#26-corollary-11) | Corollary 11 | one reading of "independent" makes it false |
| [§2.7](#27-remark-6) | Remark 6 | the horizon is `N`, not `(M+1)N` |
| [§2.8](#28-proposition-12) | Proposition 12 | with the constants fixed before `β`, (15)–(18) cannot be satisfied |
| [§2.9](#29-lemma-13) | Lemma 13 | rests on two displays that are never stated; `e^{-β/(MN)}` for `e^{-MNβ}` |
| [§2.10](#210-lemma-14-and-lemma-29) | Lemmas 14 and 29 | the conditioning in Appendix B does not hold |
| [§2.11](#211-corollaries-15-and-30) | Corollaries 15 and 30 | vacuous unless `L^o ≠ ∅` |
| [§2.12](#212-lemma-19) | Lemma 19 | a misprint in the last display, and steps left implicit |
| [§2.13](#213-lemma-28) | Lemma 28 | one step of "as the proof of Lemma 13" is not Lemma 13's |

---

## 1. What needs a decision

### 1.1 Lemma 20 is false as printed for `M ≥ 4`

*Blueprint:* `lem20`, `note-lem20`. *Lean:* `SocialNetwork.isConsensus_state_of_favouring`,
stated as printed, **unproved**.

**A counterexample.**  Take `N = 3`, `M = 5`, `o` the first opinion, `p` the second,
and the rows

```
a : ( 7/4, -1/2, -1/2, -1/2, -1/4)     the witness:  n(u) = 1,  r = 3/4
b : (   0,    0,    0,    0,    0)     the null row
c : (   0,  3/2, -1/2, -1/2, -1/2)     3/2 = n(u) + r - 1/(M-1), the bound allowed
```

This is a matrix of `S^o`.  The greedy pair is `(a, o)`.  After it, column `o` reads
`(0, 1, 1)` while `c` carries `3/2 - 1/4 = 5/4` on `p`: the maximum lies off column
`o`, so `ξ_2` forces `O_2 = p`.  The greedy run is unique throughout, and at
`(M-1)(n(u)+1) - 1 = 7` it is in `C^p`, not `C^o`.

**Why.**  Definition 5 bounds the other columns by `n(u) + r - 1/(M-1)`, and each
greedy expression of `o` lowers that bound by only `1/(M-1)`.  Nothing in `S^o` keeps
column `o` above it once the witnesses have been reset.  With one witness and the
null row as the only other support of column `o`, the second step can already leave
column `o` once `r ≥ 2/(M-1)` — through a tie at equality, which `ξ_2` may break away
from `o`, and strictly above it — and that needs `M ≥ 4`.  The same mechanism shows
that `⋃_o S^o` is not stable under a greedy expression (§2.2).  With `N = 3`, `M = 4`
and rows `0`, `(-5/3, 0, 0, 5/3)`, `(-4/3, 0, 4/3, 0)`, the matrix is in `S^o` for `o`
the fourth opinion (`n = 1`, `r = 2/3`).  The greedy pair is unique, and its successor,
with rows `(-1/3, -1/3, -1/3, 1)`, `0`, `(-5/3, -1/3, 1, 1)`, lies in no `S^p`.

**The written proof** fails on the way.  Its invariant
`Ũₖ (a, p) ≤ n(u) + r - (k+1)/(M-1)` for `p ≠ o` is not preserved: the actor that
expresses at step `k` has its row reset to `0`, and at the terminal `k` the bound is
negative.  Its `n(u)` witnesses are not replenished either: when the expressing actor
is a witness and `r > 0`, the actor reset one step earlier reaches only `1 < 1 + r`.

**What appears to survive.**  A computer search over small cases (`N ≤ 5`, `M ≤ 6`,
bounded entries; not part of this repository) found:

* no counterexample for `M = 2` or `3`;
* the conclusion of Lemma 20 holding on every state that Lemma 19 actually produces,
  whatever the witness;
* Proposition 7 holding from every sampled start, under every tie-break.

So the theorems look safe, and the defect looks like one of interface.  `S^o` forgets
what the proof of Lemma 19 delivers: the actors that have expressed carry the partial
sums of the expressions after them, a staircase on column `o`.  Lemma 20 needs that
staircase.

**What is needed:** Lemma 20 restated, most likely with a hypothesis that Lemma 19
delivers, and its proof.  Until then the Lean statement is the one printed, carrying
its `sorry`, and Proposition 7 and everything after it are written from it.  They
become proofs once Lemma 20 is restated and the assembly of Proposition 7 is adapted
to it.

### 1.2 Proposition 23 rests on statements the paper does not give

*Blueprint:* `prop23`. *Lean:* `SocialNetwork.Bias.exists_horizon_isBiasedLadder`,
**unproved**.

Appendix C says that the proof of Proposition 23 "follows as the proof of
Proposition 7", which goes through Lemmas 19 and 20.  Their biased analogues are not
stated, and the analogue of Lemma 20 will have to avoid the failure of §1.1.
Proposition 26, Theorem 27, Lemma 28, Theorem 31 and part 2 of Theorem 4 are written
from Proposition 23.

### 1.3 Proposition 12 is assumed, twice

*Blueprint:* `prop12`, `prop12-biased`. *Lean:* `SocialNetwork.exitTime_approx_exponential`,
`SocialNetwork.Bias.biasedExitTime_approx_exponential`, both `axiom`s.

Proposition 12 is Theorem 5.3 of [LM22], a metastability estimate for a general strong
Markov process, and nothing in this repository can prove it.  It is declared as an
`axiom` rather than left as a `sorry`, so that it is not mistaken for open work.

It has to be declared twice, once for each process.  Stated abstractly, over an
arbitrary family of measures and hitting time, it would be inconsistent: the zero
measure with an empty ladder set satisfies (15)–(18) vacuously and falsifies the
conclusion at `t = 0`.  The strong Markov property is what excludes this, and it
cannot be expressed here.  Theorem 31 therefore needs a biased Proposition 12, which
Appendix C does not state ("the proof of Theorem 31 follows exactly as the proof of
Theorem 3").  The two axioms are the same citation, applied to two processes.  CI
fails if any result declared complete depends on either.

---

## 2. Misprints and gaps

None of these affects a result.  Each is handled in Lean as described, and the
blueprint node gives the detail.

### 2.1 Equation (6)

*Blueprint:* `note-eq6`.  The second condition, `∑ₐ nₐ ≥ N(N-1)/2`, is not stable under
`π_α^{a,o}`, though Remark 1 says `S^α` is.  For `N = 3`, `n = (0, 0, 3)` satisfies it,
and expressing from the third actor gives `(1, 1, 0)`.  The justification the paper
gives proves something stronger that is stable: the `nₐ` are pairwise distinct.
Distinctness together with a null row implies the inequality, and `IsBiasedState`
carries distinctness.

### 2.2 Proposition 7

*Blueprint:* `prop7`, `note-prop7`.

* "So by Lemma 19 we have `⋂_{j=1}^{N+1} ξ_j^u ⊆ {Ũ_{N+1} ∈ ⋃_o S^o}`" carries the
  membership from `τ(u)`, where Lemma 19 delivers it, to `N + 1`.  That needs
  `⋃_o S^o` to be stable under a greedy expression, which is not proved and is false
  for `M ≥ 4` (§1.1).  The Lean assembly applies Lemma 20 at `τ(u)` instead.  The
  arithmetic is yours, `τ(u) + (M-1)(n(u)+1) - 1 ≤ MN`, and the consensus is carried
  up to `MN` by your own observation that `C^o` is stable under a greedy expression.
* The proof ends "by definition, if `v ∈ C^o` and `⋂_{j=1}^N ξ_j` occurs, then
  `Ũ_N ∈ L^o`".  It is true, but not by definition.  Every greedy expression has to be
  shown to express `o`, no actor to express twice, and the actor of step `i` to end at
  `N-1-i`.

### 2.3 Proposition 9

*Blueprint:* `prop9`, `aux-greedy-avoids`.

* The proof uses a greedy run that reaches `L` "without visiting `u`".  Proposition 7
  says where the run ends, not where it passes.  The clause is Corollary 8 of [GL24],
  and it is proved here that way: a run that returned to `u` could be repeated for
  ever, would reach `L̂` by Proposition 7 and Remark 5, and would put `u ∈ L̂`.
* The statement has no hypothesis on `u` beyond `u ∉ L̂`, but its proof calls
  Proposition 7, which is stated on `S`.  `u ∈ S` is added.

### 2.4 Equation (13)

*Blueprint:* `eq13`, `aux-transfer`, `aux-transfer-converse`.

* (13) takes both `μ^β` and `μ̃^β` as given.  With uniqueness for the skeleton it gives
  the uniqueness half of Theorem 1.2, but not existence.  Existence needs the converse,
  that the measure (13) defines from `μ̃^β` is invariant, which the paper uses but does
  not state.  Both directions are proved here.
* The rate floor `q_β(u) ≥ M` is asserted, and the finiteness of `∑ μ̃^β(u)/q_β(u)`,
  without which the right-hand side is not a probability measure, is not stated.  Both
  are proved here.

### 2.5 The proof of Theorem 2.1

*Blueprint:* `thm2-1`.  The proof writes
`μ̃^β(L) ≥ ζ_β^{(M+1)N} ≥ (MN)^{-(M+1)N}`.  The last inequality fails for small `β`:
`ζ_0 = 1/(1+MN) < 1/(MN)`.  Since `ζ_β ≥ 1/(1+MN)` for every `β ≥ 0`, the Lean proof
uses `(1+MN)^{-(M+1)N}`, and only the constant `C` changes.

### 2.6 Corollary 11

*Blueprint:* `cor11`.  "`τ` … independent from `(U_t^{β,u})_t`" admits two readings.

* Read as `τ` independent of the process, the corollary is false.  From `0`,
  `R^{β,0}(L) = T₁ + O(ε_β)`, and the probability tends to `P(T₁ > τ) = 1/2`.
* Read as equation (19) uses it, `τ` is the process's own first jump time from `0`,
  and the corollary is true.

The Lean statement takes the second reading, and is proved.

### 2.7 Remark 6

*Blueprint:* `rem6`.  "By following the same steps of the proof of part 2 of
Theorem 2" does not apply as it stands: part 2 concludes `L`, not `L^o`, and a greedy
run continued past a ladder leaves `L^o`.  What Remark 6 uses is the last stage of
Proposition 7 alone, run from `C^o` and stopped at `N`, and it is proved that way.

### 2.8 Proposition 12

*Blueprint:* `prop12`.  `ε₁, ε₂, s₁, s₂` are introduced before `β`, but Section 5.3
takes them as functions of `β` (`s₂ = 2β`, `ε₂ = (M+1)²N²e^{-β/((M+1)N)}`).  It also
needs `ε₁ + ε₂ ≤ 1/2` only for `β` large.  As constants fixed ahead of `β`, the
hypotheses cannot be satisfied, and Theorem 3 would not follow.  In Lean they are
functions of `β`, with (15)–(18) required above a threshold.

### 2.9 Lemma 13

*Blueprint:* `lem13`, `aux-hitting-rate`, `eq19`.

* The proof uses two inequalities the paper displays but does not state: the bound on
  `P(R^{β,u}(L) > t)` inside the proof of part 2 of Theorem 2, and equation (19).  The
  numbered statements they would come from, Theorem 2.2 and Corollary 11, are limits,
  which lose the rate.  So Lemma 13 does not follow from the numbered statements it
  cites.  Both displays are stated as nodes of their own and proved, following [GL24]
  p. 19, which writes both out.  Whether they should be numbered is your call.
* `τ` is exponential of mean `1/(MN)`, so `P(τ > β) = e^{-MNβ}`; the proof writes
  `e^{-β/(MN)}`.  This is harmless, since the written form is the weaker of the two.

### 2.10 Lemma 14 and Lemma 29

*Blueprint:* `lem14`, `note-lem14`, `lem29`.  The mechanism and the rates of
Appendix B are right; their composition is not.  The proof bounds
`P(τ₁⁻ᵒ ≥ t)` and `P(τ₂⁻ᵒ ≥ t | τ₁⁻ᵒ ≥ t)` and multiplies.  The second goes through
`P(T_{n_j} - T_{n_{j-1}} > t | τ₁⁻ᵒ ≥ T_{n_j}) ≥ P(E_j ≥ t)`, which conditions on an
event involving the interval it bounds.  Asking that no negative expression occur
before `T_{n_j}` favours short intervals, which is the wrong direction for a lower
bound.  The Lean proof composes the same rates, with your constant
`Λ = 2N³(M+1)³e^{-β/(M-1)}`, by a first-step comparison with an exponential clock,
run by induction on the number of jumps.  This handles the two failure modes at
once.  Lemma 29 follows the same way.

### 2.11 Corollaries 15 and 30

*Blueprint:* `cor15`, `cor30`, `aux-ladder-nonempty`, `aux-biased-ladder-nonempty`.
Both quantify over `l ∈ L^o` (resp. `L_α^o`), so they are vacuous unless that set is
non-empty, which the paper never records.  The witnesses are supplied:
`SocialNetwork.ladderOf` and `SocialNetwork.Bias.biasedLadderOf`.

### 2.12 Lemma 19

*Blueprint:* `lem19`, `note-lem19`.  Proved along your proof, with three steps written
out:

* the `⌊m⌋` distinct actors obtained "by (25)" are first passages.  Read backwards from
  `A_{τ(u)-1}`, the pressure for `O_{τ(u)}` climbs at most `1` per step, so the first
  index reaching each level `j + r` overshoots by less than `1`;
* `m ≥ 1` once `τ(u) ≥ 3`, since `A_{τ(u)-2}` carries `1` on `O_{τ(u)-1}`;
* `n(u) ≤ N - 1`, since the witnesses avoid `A_{τ(u)}`.

**Misprint**: the last display bounds the other columns by
`m + (m - ⌊m⌋) - 1/(M-1)`.  Definition 5 needs `⌊m⌋ + (m - ⌊m⌋) - 1/(M-1) = m - 1/(M-1)`,
which is what holds.

### 2.13 Lemma 28

*Blueprint:* `lem28`, `aux-biased-hitting-rate`.  "As the proof of Lemma 13" does not
quite carry over.  Lemma 13 bounds its race term with `e^{β/(M-1)} ≥ 1`.  The same step
here gives the exponent `2/K`, with `K` the horizon of Proposition 23, not `γ/2`.  The
exponent `γ/2` holds all the same, because the rate floor `e^{β(M-1)α}` of Remark 8
grows with `β`.  With `e^x ≥ 1 + x`, the race term is at most
`K exp(-2(M-1)αβ²/K)`, and completing the square bounds it by
`K e^{γ²K/(32(M-1)α)} e^{-βγ/2}`.  The constant `C` therefore also depends on `K`.
