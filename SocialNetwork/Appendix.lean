/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.ContinuousTime
import SocialNetwork.Favouring
import SocialNetwork.Greedy

/-!
# Appendix A: Proposition 7, and the bound of Remark 5

Appendix A of arXiv:2607.19651 proves Proposition 7 in three moves:

1. **Lemma 19** takes an arbitrary state of `S` to the set `⋃_o S^o` of Definition 5, at the
   first repeat time `τ (u) ≤ N + 1`;
2. **Lemma 20** takes a state of `S^o` to the consensus set `C^o`, in
   `(M-1) (n(u) + 1) - 1 ≤ (M-1) N` further steps;
3. a final step takes `C^o` to a ladder `L^o` in `N` further steps.

The third is `SocialNetwork.isLadder_state`, proved.  The first two are stated here and are
**not** proved: the blueprint records, in the section "Two points in Appendix A that the
formalisation has to fill in", exactly where the written proofs fail to compose, and what
repairs appear to work.  Both repairs change the written arguments rather than their
presentation, so they are recorded rather than guessed at.

This file also states the bound `η` of Remark 5, whose deterministic half — expressing a pair
that carries positive pressure keeps a steep ladder steep — is proved, while the probabilistic
half is not.

## Main definitions

* `SocialNetwork.favouringSet` — `⋃_{o ∈ O} S^o`, the target of Lemma 19.
* `SocialNetwork.consensusUnion` — `⋃_{o ∈ O} C^o`, the target of Lemma 20.
* `SocialNetwork.eta` — the constant `η` of Remark 5.
* `SocialNetwork.positivePressureEvent` — the event `{U_0 (A₁, O₁) > 0}` of Remark 5.

## Main statements

* `SocialNetwork.isFavouring_state_firstRepeat` — **Lemma 19**, unproved.
* `SocialNetwork.isConsensus_state_of_favouring` — **Lemma 20**, unproved.
* `SocialNetwork.isLadder_state_of_greedy` — **Proposition 7**, unproved.
* `SocialNetwork.mem_steepLadderSet_of_positivePressure` — the deterministic half of
  Remark 5, proved.
* `SocialNetwork.eta_le_pathMeasure_positivePressure` — the bound `η` of Remark 5, unproved.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The unions of Definition 5 and Definition 2 -/

section Sets

/-- `⋃_{o ∈ O} S^o`, the set that Lemma 19 lands in. -/
def favouringSet (N M : ℕ) : Set (Pressure N M) := {v | ∃ o, IsFavouring o v}

/-- `⋃_{o ∈ O} C^o`, the set that Lemma 20 lands in. -/
def consensusUnion (N M : ℕ) : Set (Pressure N M) := {v | ∃ o, IsConsensus o v}

@[simp]
theorem mem_favouringSet {v : Pressure N M} : v ∈ favouringSet N M ↔ ∃ o, IsFavouring o v :=
  Iff.rfl

@[simp]
theorem mem_consensusUnion {v : Pressure N M} : v ∈ consensusUnion N M ↔ ∃ o, IsConsensus o v :=
  Iff.rfl

theorem ladderSet_subset_consensusUnion (hM : 2 ≤ M) (hN : 2 ≤ N) :
    ladderSet N M ⊆ consensusUnion N M :=
  fun _ ⟨o, hu⟩ => ⟨o, hu.isConsensus hM hN⟩

end Sets

/-! ### Lemma 19 -/

section Lemma19

variable (T : Trajectory N M) {u : Pressure N M}

/-- **Lemma 19.**  For any initial matrix `u ∈ S`, the event `ξ^u_{τ(u)}` implies that
`Ũ_{τ(u)}^{β,u} ∈ ⋃_{o ∈ O} S^o`.

Recall the index convention of `SocialNetwork.Trajectory`: `firstRepeat T` is the paper's
`τ (u) - 1`, and `IsGreedyAt T u k` is the paper's `ξ_{k+1}^u`.  So the hypothesis below is
`ξ_{τ(u)}^u` and the conclusion is about `Ũ_{τ(u)}`.

**Unproved.**  The written proof asserts, "by (25)", a sequence of `⌊m⌋ + 1` distinct actors
without giving the construction, and rules out the degenerate case `m = 0` through
`τ (u) = 2` rather than through `m = 0` itself.  The blueprint gives a construction that
works — a first-passage decomposition of the backward walk — and the corrected case split. -/
theorem isFavouring_state_firstRepeat (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u)
    (hgreedy : IsGreedyAt T u (firstRepeat T)) :
    T.state u (firstRepeat T + 1) ∈ favouringSet N M := by
  sorry

end Lemma19

/-! ### Lemma 20 -/

section Lemma20

variable (T : Trajectory N M) {o : Opinion M} {u : Pressure N M}

/-- **Lemma 20.**  For any matrix `u ∈ S^o` with witness `n (u)`, the event
`⋂_{j=1}^{(M-1)(n(u)+1)-1} ξ_j^u` implies `Ũ_{(M-1)(n(u)+1)-1}^{β,u} ∈ C^o`.

**Unproved.**  The induction invariant of the written proof,
`Ũₖ (a, p) ≤ n(u) + r - (k+1)/(M-1)` for `p ≠ o`, is not preserved: the actor that expresses
at step `k` has its row reset to `0`, and at the terminal `k` the bound is negative.  The
blueprint gives the repaired invariant, `max (0, n(u) + r - (k+1)/(M-1))`, together with the
staircase mechanism that replenishes the witnesses. -/
theorem isConsensus_state_of_favouring (hM : 2 ≤ M) (hN : 3 ≤ N) {n : ℕ} {ρ : ℤ}
    {a : Fin n → Actor N} (hu : IsFavouringWith o u n ρ a)
    (hgreedy : ∀ k < (M - 1) * (n + 1) - 1, IsGreedyAt T u k) :
    IsConsensus o (T.state u ((M - 1) * (n + 1) - 1)) := by
  sorry

end Lemma20

/-! ### Proposition 7 -/

section Proposition7

variable (T : Trajectory N M) {u : Pressure N M}

/-- **Proposition 7.**  For any initial matrix `u ∈ S`,

```
⋂_{j=1}^{(M+1)N} ξ_j^u   ⊆   {U_{T_{(M+1)N}}^{β,u} ∈ L}.
```

The three stages are Lemma 19 (which needs `τ (u) ≤ N + 1` steps), Lemma 20 (which needs
`(M-1)(n(u)+1) - 1 ≤ (M-1) N` further steps, since `n (u) ≤ N - 1`), and the final step
`SocialNetwork.isLadder_state` (`N` further steps).  The total is `(M+1) N`.

**Unproved**, because Lemmas 19 and 20 are. -/
theorem isLadder_state_of_greedy (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u)
    (hgreedy : ∀ k < (M + 1) * N, IsGreedyAt T u k) :
    T.state u ((M + 1) * N) ∈ ladderSet N M := by
  sorry

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
/-- **Proposition 7**, as an inclusion of events on the sample space of the skeleton. -/
theorem greedyEvents_subset_ladder (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u) :
    greedyEvents u ((M + 1) * N)
      ⊆ {ω : ℕ → Jump N M | skeleton u ((M + 1) * N) ω ∈ ladderSet N M} :=
  fun _ hω => isLadder_state_of_greedy _ hM hN hu fun k hk => hω k hk

/-- Proposition 7 combined with Proposition 8 and Remark 4: after `(M+1) N` expressions the
skeleton is on a ladder, except on an event of probability at most
`(M+1) N · M N · e^{-β/(M-1)}`.

This is the shape in which Theorem 2 uses the two propositions together. -/
theorem one_sub_le_pathMeasure_ladder (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u) {β : ℝ}
    (hβ : 0 ≤ β) :
    ENNReal.ofReal
        (1 - (((M + 1) * N : ℕ) : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))))
      ≤ pathMeasure β u {ω : ℕ → Jump N M | skeleton u ((M + 1) * N) ω ∈ ladderSet N M} :=
  le_trans (one_sub_le_pathMeasure_greedyEvents hM hβ ((M + 1) * N))
    (measure_mono (greedyEvents_subset_ladder hM hN hu))

end Proposition7

/-! ### Remark 5 -/

section Remark5

/-- The constant `η` of Remark 5:

```
η = (∑_{j=1}^{N-1} e^{βj}) / (∑_{j=0}^{N-1} e^{βj} + MN).
```

On a ladder, the `N` pressures for the supported opinion are `0, 1, …, N-1`, so the numerator
collects the rates of the `N - 1` actors carrying strictly positive pressure, and the
denominator bounds the total rate: the remaining entries are non-positive, hence have rate at
most `1`, and there are at most `MN` of them. -/
noncomputable def eta (N M : ℕ) (β : ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))) /
    ((∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ))) + ((M * N : ℕ) : ℝ))

theorem eta_nonneg (N M : ℕ) {β : ℝ} : 0 ≤ eta N M β := by
  refine div_nonneg (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) ?_
  exact add_nonneg (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) (Nat.cast_nonneg _)

variable [NeZero N] [NeZero M]

/-- The event `{U_0^{β,u} (A₁, O₁) > 0}` of Remark 5: the first expressed pair carries
strictly positive social pressure. -/
def positivePressureEvent (u : Pressure N M) : Set (ℕ → Jump N M) :=
  {ω | 0 < u (ω 0).1 (ω 0).2}

theorem measurableSet_positivePressureEvent (u : Pressure N M) :
    MeasurableSet (positivePressureEvent u) := by
  have h : positivePressureEvent u
      = (fun ω : ℕ → Jump N M => ω 0) ⁻¹' {p : Jump N M | 0 < u p.1 p.2} := rfl
  rw [h]
  exact MeasurableSet.preimage MeasurableSet.of_discrete (measurable_pi_apply 0)

omit [NeZero N] [NeZero M] in
/-- **The deterministic half of Remark 5**: from a steep ladder, an expression by a pair that
carries strictly positive pressure lands on a steep ladder again,

```
{U_0^{β,l̂} (A₁, O₁) > 0} ⊆ {U_{T_1}^{β,l̂} ∈ L̂}.
```

This is `SocialNetwork.IsSteepLadder.express_of_pos` read on the sample space. -/
theorem mem_steepLadderSet_of_positivePressure (hM : 2 ≤ M) {o : Opinion M}
    {l : Pressure N M} (hl : IsSteepLadder o l) :
    positivePressureEvent l ⊆ {ω : ℕ → Jump N M | skeleton l 1 ω ∈ steepLadderSet N M} := by
  intro ω hω
  refine ⟨o, ?_⟩
  have hstate : skeleton l 1 ω = express (ω 0).1 (ω 0).2 l := by
    rw [skeleton, Trajectory.state_succ, Trajectory.state_zero]
    rfl
  rw [hstate]
  exact hl.express_of_pos hM hω

/-- **Remark 5**, the bound `η`: from any steep ladder the first expressed pair carries
positive pressure with probability at least `η`.

The paper's argument is a comparison: the worst case over `L̂` is attained on `L`, where the
`N` pressures for the supported opinion are exactly `0, 1, …, N-1`.

**Unproved.**  What is missing is the comparison itself; the arithmetic of `η` is available
through `SocialNetwork.jumpPMF_apply`. -/
theorem eta_le_pathMeasure_positivePressure (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ENNReal.ofReal (eta N M β) ≤ pathMeasure β l (positivePressureEvent l) := by
  sorry

/-- Iterating Remark 5: from a steep ladder, the skeleton stays on `L̂` for `m` steps with
probability at least `η^m`.  This is the estimate that Proposition 9 uses to keep the process
away from a state `u ∉ L̂`. -/
theorem eta_pow_le_pathMeasure_steepLadder (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) (m : ℕ) :
    ENNReal.ofReal (eta N M β) ^ m
      ≤ pathMeasure β l {ω : ℕ → Jump N M | ∀ k ≤ m, skeleton l k ω ∈ steepLadderSet N M} := by
  sorry

end Remark5

/-! ### Proposition 9 and Corollary 10 -/

section Proposition9

variable [NeZero N] [NeZero M]

/-- **Proposition 9.**  For any `β > 0` and any `u ∉ L̂`, the invariant measure of the
skeleton satisfies `μ̃^β (u) ≤ C' e^{-β(N-1)}`, with `C' = (NM)^{(M+1)N+1}`.

The paper's proof is Kac's lemma — `1 / μ̃^β (u) = E [R̃^{β,u} (u)]` — followed by a lower
bound on the return time built from Proposition 7 (reach `L` without visiting `u`) and
Remark 5 (stay in `L̂` afterwards).  Mathlib has no Kac lemma.

**Unproved**, and stated for an arbitrary invariant probability measure of the skeleton rather
than for a named `μ̃^β`, since its existence is itself Theorem 1.2. -/
theorem measure_le_of_notMem_steepLadderSet (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {μ : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) {u : Pressure N M}
    (hu : u ∉ steepLadderSet N M) :
    μ {u} ≤ ENNReal.ofReal
      ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1)) * Real.exp (-β * ((N : ℝ) - 1))) := by
  sorry

/-- **Corollary 10.**  `μ̃^β (0) ≤ C'' e^{-β(N-1+1/(M-1))}` with `C'' = (NM) C'`.

The extra `1/(M-1)` in the exponent comes from the observation that the zero matrix can only
be entered from a state in which one actor has a null row and every other actor carries `-1`
on one opinion and `1/(M-1)` on the others — a state whose maximum is `1/(M-1)`.

**Unproved**, since Proposition 9 is. -/
theorem measure_zero_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {μ : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) :
    μ {(0 : Pressure N M)} ≤ ENNReal.ofReal
      ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 2)) *
        Real.exp (-β * ((N : ℝ) - 1 + 1 / ((M : ℝ) - 1)))) := by
  sorry

end Proposition9

end SocialNetwork
