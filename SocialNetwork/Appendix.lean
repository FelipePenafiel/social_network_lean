/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.ContinuousTime
import SocialNetwork.Favouring
import SocialNetwork.Greedy
import SocialNetwork.Markov

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

This file also proves Remark 5 entire: the deterministic half — expressing a pair that carries
positive pressure keeps a steep ladder steep — the probabilistic half, that such a pair is
expressed with probability at least `η`, and the iterate `η^m`, which reruns the conditioning
of Proposition 8 against a one-step bound that holds only on `L̂`.

And it proves **Proposition 9**, which puts those together: Kac's inequality
(`SocialNetwork.kac_tsum_le`) bounds the invariant measure of a matrix by the reciprocal of its
mean return time, and the return time is bounded below by a greedy run to `L` followed by
positive expressions.  The one step it does not have is the paper's "without visiting `u`",
which the written proof reads off Proposition 7 and which Proposition 7 does not give;
`SocialNetwork.skeleton_ne_of_greedy` states it and carries the `sorry`.

And it proves **Corollary 10**, the same bound at the zero matrix with the extra exponent
`1/(M-1)`.  The paper reads that exponent off the states from which the zero matrix can be
entered, in a clause it does not argue; `SocialNetwork.zeroPredecessor` is one of those states,
there are `NM` of them, and the three things the clause needs — that the description is
exhaustive, that none of those states is a steep ladder, and that the step into the zero matrix
costs `e^{-β/(M-1)}` — are proved here.

## Main definitions

* `SocialNetwork.favouringSet` — `⋃_{o ∈ O} S^o`, the target of Lemma 19.
* `SocialNetwork.consensusUnion` — `⋃_{o ∈ O} C^o`, the target of Lemma 20.
* `SocialNetwork.eta` — the constant `η` of Remark 5.
* `SocialNetwork.positivePressureEvent` — the event `{U_0 (A₁, O₁) > 0}` of Remark 5.
* `SocialNetwork.zeroPredecessor` — the state from which expressing `(a, o)` reaches the zero
  matrix, the object of the clause Corollary 10 asserts.

## Main statements

* `SocialNetwork.isFavouring_state_firstRepeat` — **Lemma 19**, unproved.
* `SocialNetwork.isConsensus_state_of_favouring` — **Lemma 20**, unproved.
* `SocialNetwork.isLadder_state_of_greedy` — **Proposition 7**, unproved.
* `SocialNetwork.mem_steepLadderSet_of_positivePressure` — the deterministic half of
  Remark 5, proved.
* `SocialNetwork.eta_le_pathMeasure_positivePressure` — the bound `η` of Remark 5, proved.
* `SocialNetwork.sum_Ico_exp_le_sum_jumpRate` — the comparison it rests on: the worst case
  over `L̂` is attained on `L`.
* `SocialNetwork.eta_pow_le_pathMeasure_steepLadder` — Remark 5 iterated: the skeleton stays
  on `L̂` for `m` steps with probability at least `η^m`.
* `SocialNetwork.returnBound_prod_le` — the lower bound on the return time to `u`, the greedy
  run and the positive expressions composed on the realisation.
* `SocialNetwork.skeleton_ne_of_greedy` — the step the proof of Proposition 9 asserts,
  unproved.
* `SocialNetwork.measure_le_of_notMem_steepLadderSet` — **Proposition 9**, proved modulo that
  step and, through Proposition 7, modulo Lemmas 19 and 20.
* `SocialNetwork.eq_zeroPredecessor_of_express_eq_zero` — a matrix with a null row from which
  one expression reaches `0` is a `SocialNetwork.zeroPredecessor`, proved.
* `SocialNetwork.measure_exists_zero_row_eq_one` — the invariant measure charges only the
  matrices with a null row, which is what makes that description exhaustive, proved.
* `SocialNetwork.skeletonKernel_zeroPredecessor_le` — the step into the zero matrix costs
  `e^{-β/(M-1)}`, proved.
* `SocialNetwork.measure_zero_le` — **Corollary 10**, proved modulo Proposition 9.
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

**Formalised, but not sorry-free**: the assembly is complete and inherits `sorryAx` from
Lemmas 19 and 20 alone.

**Supplies a step the paper asserts, and takes a different route through one of them.**  The
written proof reaches `⋃_o S^o` at time `N + 1` --- "so by Lemma 19 we have
`⋂_{j=1}^{N+1} ξ_j^u ⊆ {Ũ_{N+1} ∈ ⋃_o S^o}`" --- whereas Lemma 19 delivers that membership at
the first repeat `τ (u)`, which is only `≤ N + 1`.  Carrying it from `τ (u)` to `N + 1` needs
`⋃_o S^o` to be stable under a greedy expression, and the paper never establishes that; it is
not obvious either, since expressing resets the row of one of the very actors that witness
`S^o`.  Lemma 20 is therefore applied here at `τ (u)` itself, where Lemma 19 leaves the
process, and no stability of `S^o` is needed.  The arithmetic is unchanged:
`τ (u) + (M-1)(n(u)+1) - 1 ≤ (N+1) + (M-1)N - 1 = MN`.

The padding the paper does need is the other one, and that one is available: the consensus is
carried from the time Lemma 20 delivers it up to `MN` by
`SocialNetwork.isConsensus_state`, which is the paper's own observation that a greedy
expression in `C^o` expresses `o` and that `C^o` is stable under it. -/
theorem isLadder_state_of_greedy (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u)
    (hgreedy : ∀ k < (M + 1) * N, IsGreedyAt T u k) :
    T.state u ((M + 1) * N) ∈ ladderSet N M := by
  have hN2 : 2 ≤ N := by omega
  -- The three horizons, with the products left as atoms for `omega`.
  have hprod : (M - 1) * N + N = M * N := by
    have hM1 : M - 1 + 1 = M := by omega
    calc (M - 1) * N + N = (M - 1 + 1) * N := by ring
      _ = M * N := by rw [hM1]
  have hBN : N ≤ (M - 1) * N := Nat.le_mul_of_pos_left N (by omega)
  have hMN : 2 * N ≤ M * N := Nat.mul_le_mul_right N hM
  have hlast : M * N + N = (M + 1) * N := by ring
  -- Stage 1: Lemma 19, at the first repeat, which is where it delivers.
  have hτ : firstRepeat T ≤ N := firstRepeat_le T
  have h19 := isFavouring_state_firstRepeat T hM hN hu (hgreedy _ (by omega))
  rw [mem_favouringSet] at h19
  obtain ⟨o, n, ρ, a, hfav⟩ := h19
  -- Stage 2: Lemma 20 from that state, for `(M-1)(n(u)+1) - 1` further steps.
  have hn : n + 1 ≤ N := by have := hfav.le_pred; have := hfav.one_le; omega
  have hstep : (M - 1) * (n + 1) ≤ (M - 1) * N := Nat.mul_le_mul (le_refl (M - 1)) hn
  have hbound : firstRepeat T + 1 + ((M - 1) * (n + 1) - 1) ≤ M * N := by omega
  have h20 : IsConsensus o (T.state u (firstRepeat T + 1 + ((M - 1) * (n + 1) - 1))) := by
    rw [T.state_add u (firstRepeat T + 1) ((M - 1) * (n + 1) - 1)]
    exact isConsensus_state_of_favouring (T.shift (firstRepeat T + 1)) hM hN hfav
      fun k hk => (isGreedyAt_shift T u (firstRepeat T + 1) k).2 (hgreedy _ (by omega))
  -- Stage 3: carry the consensus up to `MN`, where the last stage has to start.
  have h3 : IsConsensus o (T.state u (M * N)) := by
    have hcarry := isConsensus_state (T.shift (firstRepeat T + 1 + ((M - 1) * (n + 1) - 1)))
      hM hN2 h20
      (fun k hk =>
        (isGreedyAt_shift T u (firstRepeat T + 1 + ((M - 1) * (n + 1) - 1)) k).2
          (hgreedy _ (by omega)))
      (M * N - (firstRepeat T + 1 + ((M - 1) * (n + 1) - 1))) le_rfl
    rw [← T.state_add] at hcarry
    rwa [show firstRepeat T + 1 + ((M - 1) * (n + 1) - 1)
        + (M * N - (firstRepeat T + 1 + ((M - 1) * (n + 1) - 1))) = M * N from by omega]
      at hcarry
  -- Stage 4: `N` greedy expressions from a consensus state land on the staircase.
  refine ⟨o, ?_⟩
  have h4 := isLadder_state (T.shift (M * N)) hM hN2 h3
    (fun k hk => (isGreedyAt_shift T u (M * N) k).2 (hgreedy _ (by omega)))
  rw [← T.state_add] at h4
  rwa [hlast] at h4

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

/-- The denominator of `η` is `1` more than its numerator: `∑_{j=0}^{N-1} e^{βj}` is
`e^0 = 1` plus `∑_{j=1}^{N-1} e^{βj}`. -/
theorem sum_range_eq_one_add_sum_Ico (hN : 1 ≤ N) (β : ℝ) :
    (∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ)))
      = 1 + ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N)]
  simp

/-- A monotone function summed over a finite set of naturals all at least `m` is at least its
sum over `m, m+1, …, m + #s - 1`.

**No counterpart in the paper**, and a Mathlib gap of the same kind as
`SocialNetwork.Bias.sum_range_card_le_sum`, which is the case `m = 0`, `f = id`.  The proof is
the same: induction on the largest element.  Adjoining a new maximum `a` to `s` adds `f a` to
the sum and `f (m + #s)` to the bound, and `m + #s ≤ a` because `s ⊆ Ico m a`. -/
theorem sum_range_add_le_sum {f : ℕ → ℝ} (hf : Monotone f) (m : ℕ) :
    ∀ s : Finset ℕ, (∀ x ∈ s, m ≤ x) →
      ∑ i ∈ Finset.range s.card, f (m + i) ≤ ∑ x ∈ s, f x := by
  intro s
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hs
      have hmem : a ∉ s := fun h => lt_irrefl a (ha a h)
      have hma : m ≤ a := hs a (Finset.mem_insert_self a s)
      have hsub : ∀ x ∈ s, m ≤ x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hcard : m + s.card ≤ a := by
        have h1 : s ⊆ Finset.Ico m a := fun x hx => Finset.mem_Ico.2 ⟨hsub x hx, ha x hx⟩
        have h2 := Finset.card_le_card h1
        rw [Nat.card_Ico] at h2
        omega
      rw [Finset.card_insert_of_notMem hmem, Finset.sum_insert hmem, Finset.sum_range_succ]
      have hih := ih hsub
      have hfa : f (m + s.card) ≤ f a := hf hcard
      linarith

/-- The elementary inequality behind `η`: if the pairs carrying positive pressure have total
rate at least `∑_{j=1}^{N-1} e^{βj}` and the remaining pairs at most `MN`, then the first carry
at least the fraction `η` of the total rate.  This is `SocialNetwork.zeta_le_div_of_le` for
Remark 5. -/
theorem eta_le_div_of_le (N M : ℕ) {β S T : ℝ}
    (hA : 0 < ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)))
    (hAS : (∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))) ≤ S)
    (hT0 : 0 ≤ T) (hT : T ≤ ((M * N : ℕ) : ℝ))
    (hden : (∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ)))
      = 1 + ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))) :
    eta N M β ≤ S / (S + T) := by
  have hS : 0 < S := lt_of_lt_of_le hA hAS
  have hST : 0 < S + T := by linarith
  have hMN : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold eta
  rw [hden, div_le_div_iff₀ (by linarith) hST]
  nlinarith [mul_le_mul_of_nonneg_right hAS hT0, mul_le_mul_of_nonneg_left hT hS.le]

variable [NeZero N] [NeZero M]

/-- The event `{U_0^{β,u} (A₁, O₁) > 0}` of Remark 5: the first expressed pair carries
strictly positive social pressure. -/
def positivePressureEvent (u : Pressure N M) : Set (ℕ → Jump N M) :=
  {ω | 0 < u (ω 0).1 (ω 0).2}

omit [NeZero N] [NeZero M] in
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

/-- `Y⁺ (v) = {(a, p) ∈ A × O : v (a, p) > 0}`, the pairs carrying strictly positive social
pressure: the pairs whose expression Remark 5 keeps on a steep ladder. -/
def posFinset (v : Pressure N M) : Finset (Jump N M) :=
  Finset.univ.filter fun p => 0 < v p.1 p.2

omit [NeZero N] [NeZero M] in
theorem mem_posFinset {v : Pressure N M} {p : Jump N M} :
    p ∈ posFinset v ↔ 0 < v p.1 p.2 := by simp [posFinset]

omit [NeZero N] [NeZero M] in
theorem positivePressureEvent_eq_preimage (l : Pressure N M) :
    positivePressureEvent l
      = (fun ω : ℕ → Jump N M => ω 0) ⁻¹' (posFinset l : Set (Jump N M)) := by
  ext ω
  simp [positivePressureEvent, posFinset]

omit [NeZero N] [NeZero M] in
/-- On a steep ladder the pairs carrying positive pressure have total rate at least
`∑_{j=1}^{N-1} e^{βj}`.

**This is the comparison Remark 5 makes**: the worst case over `L̂` is attained on `L`.  On a
steep ladder the `o`-column is `N` pairwise distinct non-negative integers, one of them `0`, so
the `N-1` positive ones are `N-1` distinct integers `≥ 1`; being distinct, they dominate
`1, 2, …, N-1` term by term once sorted, and `j ↦ e^{βj}` is increasing.  On a ladder they are
exactly `1, …, N-1`, which is the worst case.  Every other entry is non-positive, by the
`other` field of Definition 4, so it contributes nothing to this sum. -/
theorem sum_Ico_exp_le_sum_jumpRate (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))
      ≤ ∑ p ∈ posFinset l, jumpRate β l p.1 p.2 := by
  have hMZ : (0 : ℤ) < (M : ℤ) - 1 := one_lt_of_two_le hM
  have hMR : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  -- the `o`-column in the unscaled coordinates of the paper: `l (a, o) = (M-1) c a`
  have hexists : ∀ a : Actor N, ∃ k : ℕ, l a o = ((M : ℤ) - 1) * (k : ℤ) := by
    intro a
    obtain ⟨k, hk⟩ := hl.dvd a
    have h0 : (0 : ℤ) ≤ ((M : ℤ) - 1) * k := hk ▸ hl.nonneg a
    have hknn : 0 ≤ k := by nlinarith
    exact ⟨k.toNat, by rw [hk, Int.toNat_of_nonneg hknn]⟩
  choose c hc using hexists
  have hcinj : Function.Injective c := fun a b hab =>
    hl.injective (show l a o = l b o by rw [hc a, hc b, hab])
  have hrate : ∀ a : Actor N, jumpRate β l a o = Real.exp (β * (c a : ℝ)) := by
    intro a
    have hcast : ((l a o : ℤ) : ℝ) = ((M : ℝ) - 1) * (c a : ℝ) := by
      rw [hc a]; push_cast; ring
    unfold jumpRate
    rw [hcast]
    congr 1
    rw [div_eq_iff (ne_of_gt hMR)]
    ring
  -- the positive pairs are the actors off the bottom of the `o`-column
  obtain ⟨a₀, ha₀⟩ := hl.exists_zero
  have hpaeq : (Finset.univ.filter fun a : Actor N => 0 < l a o) = Finset.univ.erase a₀ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro hpos hcon
      rw [hcon, ha₀] at hpos
      exact lt_irrefl 0 hpos
    · intro hne
      rcases lt_or_eq_of_le (hl.nonneg a) with hlt | heq
      · exact hlt
      · exact absurd (hl.injective (show l a o = l a₀ o by rw [← heq, ha₀])) hne
  have hcard : (Finset.univ.filter fun a : Actor N => 0 < l a o).card = N - 1 := by
    rw [hpaeq, Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ,
      Fintype.card_fin]
  -- rewrite the sum over pairs as a sum over those actors
  have hposF : posFinset l
      = (Finset.univ.filter fun a : Actor N => 0 < l a o).image (fun a => (a, o)) := by
    ext p
    simp only [mem_posFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      have h2 : p.2 = o := hl.opinion_eq_of_pos hM hp
      exact ⟨p.1, by rw [← h2]; exact hp, by rw [← h2]⟩
    · rintro ⟨a, hapos, rfl⟩
      exact hapos
  have hstep : ∑ p ∈ posFinset l, jumpRate β l p.1 p.2
      = ∑ a ∈ Finset.univ.filter (fun a : Actor N => 0 < l a o),
          Real.exp (β * (c a : ℝ)) := by
    rw [hposF, Finset.sum_image fun a _ b _ hab => by simpa using hab]
    exact Finset.sum_congr rfl fun a _ => hrate a
  -- the values `c a` are pairwise distinct naturals, all at least `1`
  have hsum : ∑ a ∈ Finset.univ.filter (fun a : Actor N => 0 < l a o),
        Real.exp (β * (c a : ℝ))
      = ∑ x ∈ (Finset.univ.filter fun a : Actor N => 0 < l a o).image c,
        Real.exp (β * (x : ℝ)) := by
    rw [Finset.sum_image fun a _ b _ hab => hcinj hab]
  have hcardimg : ((Finset.univ.filter fun a : Actor N => 0 < l a o).image c).card = N - 1 := by
    rw [Finset.card_image_of_injective _ hcinj, hcard]
  have hge1 : ∀ x ∈ (Finset.univ.filter fun a : Actor N => 0 < l a o).image c, 1 ≤ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have hapos : 0 < l a o := (Finset.mem_filter.1 ha).2
    rcases Nat.eq_zero_or_pos (c a) with h0 | h0
    · exfalso
      have hzero : l a o = 0 := by rw [hc a, h0]; simp
      linarith
    · exact h0
  have hmono : Monotone fun j : ℕ => Real.exp (β * (j : ℝ)) := fun i j hij =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hβ)
  have hkey := sum_range_add_le_sum hmono 1 _ hge1
  rw [hcardimg] at hkey
  rw [hstep, hsum, Finset.sum_Ico_eq_sum_range]
  exact hkey

omit [NeZero N] [NeZero M] in
/-- The pairs that carry no positive pressure have total rate at most `MN`: each of them has a
non-positive entry, hence a rate at most `1`, and there are at most `MN` of them.

**Supplies a step the paper asserts**: the denominator of `η` is written down in Remark 5
without argument.  It is the same counting as in Proposition 8. -/
theorem sum_jumpRate_compl_le {β : ℝ} (hβ : 0 ≤ β) (hM : 2 ≤ M) (v : Pressure N M) :
    ∑ p ∈ Finset.univ \ posFinset v, jumpRate β v p.1 p.2 ≤ ((M * N : ℕ) : ℝ) := by
  have hMR : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hle : ∀ p ∈ Finset.univ \ posFinset v, jumpRate β v p.1 p.2 ≤ 1 := by
    intro p hp
    have hnp : v p.1 p.2 ≤ 0 :=
      not_lt.1 fun hcon => (Finset.mem_sdiff.1 hp).2 (mem_posFinset.2 hcon)
    have hcast : ((v p.1 p.2 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hnp
    have hexp : β * ((v p.1 p.2 : ℤ) : ℝ) / ((M : ℝ) - 1) ≤ 0 := by
      rw [div_le_iff₀ hMR]
      nlinarith
    calc jumpRate β v p.1 p.2 = Real.exp (β * ((v p.1 p.2 : ℤ) : ℝ) / ((M : ℝ) - 1)) := rfl
      _ ≤ Real.exp 0 := Real.exp_le_exp.2 hexp
      _ = 1 := Real.exp_zero
  have hcard : (((Finset.univ \ posFinset v).card : ℕ) : ℝ) ≤ ((M * N : ℕ) : ℝ) := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ \ posFinset v))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_comm] at h
    exact_mod_cast h
  calc ∑ p ∈ Finset.univ \ posFinset v, jumpRate β v p.1 p.2
      ≤ (Finset.univ \ posFinset v).card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hle
    _ = (((Finset.univ \ posFinset v).card : ℕ) : ℝ) := by simp
    _ ≤ ((M * N : ℕ) : ℝ) := hcard

/-- **Remark 5**, the bound `η`, at the level of one expression: from any steep ladder the
first expressed pair carries positive pressure with probability at least `η`. -/
theorem eta_le_jumpPMF_posFinset (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ENNReal.ofReal (eta N M β) ≤ (jumpPMF β l).toMeasure (posFinset l) := by
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ posFinset l, jumpRate β l p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (jumpRate_pos β l p.1 p.2).le
  have hT0 : (0 : ℝ) ≤ ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (jumpRate_pos β l p.1 p.2).le
  have hApos : 0 < ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _)
      ⟨1, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
  have hAS := sum_Ico_exp_le_sum_jumpRate hM hβ hl
  have hT := sum_jumpRate_compl_le hβ hM l
  have hSpos : (0 : ℝ) < ∑ p ∈ posFinset l, jumpRate β l p.1 p.2 :=
    lt_of_lt_of_le hApos hAS
  have hreal : eta N M β
      ≤ (∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
        / ((∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
          + ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2) :=
    eta_le_div_of_le N M hApos hAS hT0 hT
      (sum_range_eq_one_add_sum_Ico (N := N) (by omega) β)
  -- transport the real inequality to the Gibbs law of equation (3)
  have hw : ∀ s : Finset (Jump N M),
      (∑ p ∈ s, jumpWeight β l p) = ENNReal.ofReal (∑ p ∈ s, jumpRate β l p.1 p.2) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β l p.1 p.2).le]
    rfl
  have hsplit : (∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
      + (∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2)
      = ∑ p : Jump N M, jumpRate β l p.1 p.2 := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ _)
  have hST : (0 : ℝ) < (∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
      + ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2 := by linarith
  have htsum : (∑' q : Jump N M, jumpWeight β l q)
      = ENNReal.ofReal ((∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
        + ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp,
      hw Finset.univ, hsplit]
  rw [PMF.toMeasure_apply_finset]
  simp only [jumpPMF_apply]
  rw [← Finset.sum_mul, hw (posFinset l), htsum, ← ENNReal.ofReal_inv_of_pos hST,
    ← ENNReal.ofReal_mul hS0, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Remark 5**, the bound `η`: from any steep ladder the first expressed pair carries
positive pressure with probability at least `η`.

Follows the paper's argument, which is a comparison: the worst case over `L̂` is attained on
`L`, where the `N` pressures for the supported opinion are exactly `0, 1, …, N-1`.  That
comparison is `SocialNetwork.sum_Ico_exp_le_sum_jumpRate`; the denominator is
`SocialNetwork.sum_jumpRate_compl_le`, and the two are combined by the elementary inequality
`SocialNetwork.eta_le_div_of_le`.

**Supplies a step the paper asserts**: that the worst case over `L̂` is attained on `L`.  Remark
5 writes the two inequalities down in a single line and argues neither. -/
theorem eta_le_pathMeasure_positivePressure (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ENNReal.ofReal (eta N M β) ≤ pathMeasure β l (positivePressureEvent l) := by
  rw [positivePressureEvent_eq_preimage l, pathMeasure_preimage_zero]
  exact eta_le_jumpPMF_posFinset hM hN hβ hl

/-! #### Iterating Remark 5

Remark 5 gives one expression: from a steep ladder, the next pair carries positive pressure
with probability at least `η`, and the state that results is again a steep ladder.  Iterating
it is Proposition 8's induction run against a different one-step bound, and it goes the same
way — along the finite-horizon kernels `ProbabilityTheory.Kernel.partialTraj` of the
Ionescu-Tulcea construction, which is what `SocialNetwork.zeta_le_partialTraj_succ` does for
the greedy event.

One thing differs, and it is what makes the event move with the state.  The greedy bound
`ζ_β` holds at *every* matrix, so the induction step of Proposition 8 needs nothing of the
history it conditions on.  The bound `η` holds only on `L̂`, so the step here has to know that
the history it conditions on has kept the state there — which is exactly what the event under
the induction says, by `SocialNetwork.IsSteepLadder.state_of_isPositiveAt`. -/

section Iterate

variable {β : ℝ} {o : Opinion M} {l : Pressure N M}

/-- The expression at step `k` is made by a pair carrying strictly positive social pressure.
This is to Remark 5 what `SocialNetwork.IsGreedyAt` is to Proposition 8: a condition on the
realisation, so a predicate on trajectories. -/
def IsPositiveAt (T : Trajectory N M) (u : Pressure N M) (k : ℕ) : Prop :=
  0 < T.state u k (T.actor k) (T.opinion k)

omit [NeZero N] [NeZero M] in
theorem isPositiveAt_iff (T : Trajectory N M) (u : Pressure N M) (k : ℕ) :
    IsPositiveAt T u k ↔ 0 < T.state u k (T.actor k) (T.opinion k) := Iff.rfl

omit [NeZero N] [NeZero M] in
/-- **The deterministic half of Remark 5, iterated**: while every expression is made from a
positive entry, the state stays on the steep ladder it started on.  This is
`SocialNetwork.IsSteepLadder.express_of_pos` run along a trajectory. -/
theorem IsSteepLadder.state_of_isPositiveAt (hM : 2 ≤ M) (hl : IsSteepLadder o l)
    (T : Trajectory N M) (n : ℕ) (hpos : ∀ k < n, IsPositiveAt T l k) :
    IsSteepLadder o (T.state l n) := by
  induction n with
  | zero => rw [Trajectory.state_zero]; exact hl
  | succ n ih =>
      rw [Trajectory.state_succ]
      exact (ih fun k hk => hpos k (by omega)).express_of_pos hM (hpos n (by omega))

/-- The event that each of the first `m` expressions is made from a positive entry. -/
def positiveEvents (u : Pressure N M) (m : ℕ) : Set (ℕ → Jump N M) :=
  {ω | ∀ k < m, IsPositiveAt (Trajectory.ofPath ω) u k}

/-- The same event, read on histories of the first `n + 1` expressed pairs. -/
def positiveHistory (u : Pressure N M) (n : ℕ) : Set ((i : Finset.Iic n) → Jump N M) :=
  {h | ∀ k ≤ n, IsPositiveAt (Trajectory.ofHistory h) u k}

omit [NeZero N] [NeZero M] in
theorem measurableSet_positiveHistory (u : Pressure N M) (n : ℕ) :
    MeasurableSet (positiveHistory u n) := MeasurableSet.of_discrete

omit [NeZero N] [NeZero M] in
/-- The condition at step `k` only constrains the first `k + 1` expressed pairs, so reading it
off a truncated path gives the same answer. -/
theorem isPositiveAt_ofHistory_frestrictLe (u : Pressure N M) (ω : ℕ → Jump N M) {n k : ℕ}
    (hk : k ≤ n) :
    IsPositiveAt
        (Trajectory.ofHistory (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) u k
      ↔ IsPositiveAt (Trajectory.ofPath ω) u k := by
  have hstate := Trajectory.state_ofHistory_frestrictLe u ω (n := n) (k := k) (by omega)
  have hactor : (Trajectory.ofHistory
      (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)).actor k = (ω k).1 := by
    rw [Trajectory.ofHistory_actor _ hk, Preorder.frestrictLe_apply]
  have hopinion : (Trajectory.ofHistory
      (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)).opinion k = (ω k).2 := by
    rw [Trajectory.ofHistory_opinion _ hk, Preorder.frestrictLe_apply]
  simp only [IsPositiveAt, hstate, hactor, hopinion, Trajectory.actor_ofPath,
    Trajectory.opinion_ofPath]

omit [NeZero N] [NeZero M] in
/-- `positiveEvents u (n+1)` is the cylinder over `positiveHistory u n`. -/
theorem positiveEvents_eq_preimage (u : Pressure N M) (n : ℕ) :
    positiveEvents u (n + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹' positiveHistory u n := by
  ext ω
  constructor
  · exact fun hω k hk => (isPositiveAt_ofHistory_frestrictLe u ω hk).2 (hω k (by omega))
  · exact fun hω k hk =>
      (isPositiveAt_ofHistory_frestrictLe u ω (show k ≤ n by omega)).1 (hω k (by omega))

omit [NeZero N] [NeZero M] in
/-- On `positiveHistory l n` the state stays on the steep ladder `l` started on, for every time
up to `n + 1`.  This is what makes the one-step bound `η` available at the induction step. -/
theorem isSteepLadder_state_ofHistory (hM : 2 ≤ M) (hl : IsSteepLadder o l) {n : ℕ}
    {h : (i : Finset.Iic n) → Jump N M} (hh : h ∈ positiveHistory l n) {k : ℕ}
    (hk : k ≤ n + 1) : IsSteepLadder o ((Trajectory.ofHistory h).state l k) :=
  hl.state_of_isPositiveAt hM _ k fun j hj => hh j (by omega)

omit [NeZero N] [NeZero M] in
/-- If a history of length `n + 2` restricts to one in `positiveHistory l n` and its last
coordinate carries positive pressure at the matrix that replaying the restriction reaches, then
it lies in `positiveHistory l (n + 1)`. -/
theorem mem_positiveHistory_succ {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (hh : h ∈ positiveHistory l n)
    (hlast : x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩
      ∈ posFinset ((Trajectory.ofHistory h).state l (n + 1))) :
    x ∈ positiveHistory l (n + 1) := by
  intro k hk
  rw [isPositiveAt_iff]
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · have hkn : k ≤ n := by omega
    have hprev := (isPositiveAt_iff _ _ _).1 (hh k hkn)
    rw [ofHistory_state_eq hx l (k := k) (by omega), ofHistory_actor_eq hx hkn,
      ofHistory_opinion_eq hx hkn]
    exact hprev
  · have hkeq : k = n + 1 := le_antisymm hk hge
    subst hkeq
    rw [ofHistory_state_eq hx l (k := n + 1) le_rfl,
      Trajectory.ofHistory_actor _ (le_refl (n + 1)),
      Trajectory.ofHistory_opinion _ (le_refl (n + 1))]
    exact mem_posFinset.1 hlast

/-- **The induction step.**  Given a history that has kept the state on the steep ladder `l`
started on, the next expression is made from a positive entry with probability at least `η`.

This is `SocialNetwork.zeta_le_partialTraj_succ` with the one-step bound of Proposition 8
replaced by that of Remark 5; the steepness the latter needs is
`SocialNetwork.isSteepLadder_state_ofHistory`. -/
theorem eta_le_partialTraj_succ (hM : 2 ≤ M) (hN : 3 ≤ N) (hβ : 0 ≤ β)
    (hl : IsSteepLadder o l) (n : ℕ) {h : (i : Finset.Iic n) → Jump N M}
    (hh : h ∈ positiveHistory l n) :
    ENNReal.ofReal (eta N M β)
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h
          (positiveHistory l (n + 1)) := by
  -- the past is almost surely `h`
  have hmapA : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (drivingKernel β l) n (n + 1) h).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      = Measure.dirac h := by
    rw [Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Jump N M) h
      (Nat.le_succ n), Kernel.partialTraj_self, Kernel.id_apply]
  have hAone : Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h}) = 1 := by
    have hm := Measure.map_apply
      (μ := Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h)
      (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      (measurableSet_singleton h)
    rw [hmapA] at hm
    rw [← hm]
    exact Measure.dirac_apply_of_mem rfl
  have hAcompl : Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})ᶜ = 0 :=
    (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hAone
  -- the last coordinate follows the Gibbs law of equation (3) at the matrix `h` reaches
  have hmapB : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (drivingKernel β l) n (n + 1) h).map
      (fun x : (i : Finset.Iic (n + 1)) → Jump N M => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      = drivingKernel β l n h := by
    rw [← Kernel.map_apply _ Measurable.of_discrete, Kernel.map_partialTraj_succ_self]
  have hB : ENNReal.ofReal (eta N M β)
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h
          ((fun x : (i : Finset.Iic (n + 1)) → Jump N M =>
              x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            (posFinset ((Trajectory.ofHistory h).state l (n + 1)))) := by
    rw [← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete, hmapB,
      drivingKernel_apply]
    exact eta_le_jumpPMF_posFinset hM hN hβ (isSteepLadder_state_ofHistory hM hl hh le_rfl)
  exact le_measure_of_inter hAcompl hB fun x hx => mem_positiveHistory_succ hx.1 hh hx.2

theorem eta_le_historyMeasure_zero (hM : 2 ≤ M) (hN : 3 ≤ N) (hβ : 0 ≤ β)
    (hl : IsSteepLadder o l) :
    ENNReal.ofReal (eta N M β) ≤ historyMeasure β l 0 (positiveHistory l 0) := by
  have hpre : toHistoryZero ⁻¹' positiveHistory l 0 = (posFinset l : Set (Jump N M)) := by
    ext z
    have hact : (Trajectory.ofHistory (toHistoryZero z)).actor 0 = z.1 :=
      Trajectory.ofHistory_actor _ (le_refl 0)
    have hopi : (Trajectory.ofHistory (toHistoryZero z)).opinion 0 = z.2 :=
      Trajectory.ofHistory_opinion _ (le_refl 0)
    constructor
    · intro hz
      have h0 := (isPositiveAt_iff _ _ _).1 (hz 0 le_rfl)
      rw [Trajectory.state_zero, hact, hopi] at h0
      exact mem_posFinset.2 h0
    · intro hz k hk
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      rw [isPositiveAt_iff, Trajectory.state_zero, hact, hopi]
      exact mem_posFinset.1 hz
  unfold historyMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply measurable_toHistoryZero MeasurableSet.of_discrete, hpre]
  exact eta_le_jumpPMF_posFinset hM hN hβ hl

theorem eta_pow_le_historyMeasure (hM : 2 ≤ M) (hN : 3 ≤ N) (hβ : 0 ≤ β)
    (hl : IsSteepLadder o l) (n : ℕ) :
    ENNReal.ofReal (eta N M β) ^ (n + 1) ≤ historyMeasure β l n (positiveHistory l n) := by
  induction n with
  | zero => simpa using eta_le_historyMeasure_zero hM hN hβ hl
  | succ n ih =>
      have hstep : historyMeasure β l (n + 1) (positiveHistory l (n + 1))
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h
              (positiveHistory l (n + 1)) ∂(historyMeasure β l n) := by
        unfold historyMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_positiveHistory l (n + 1)) (Kernel.aemeasurable _)]
      rw [hstep]
      calc ENNReal.ofReal (eta N M β) ^ (n + 1 + 1)
          = ENNReal.ofReal (eta N M β) * ENNReal.ofReal (eta N M β) ^ (n + 1) := by ring
        _ ≤ ENNReal.ofReal (eta N M β) * historyMeasure β l n (positiveHistory l n) := by gcongr
        _ = ∫⁻ h, (positiveHistory l n).indicator
              (fun _ => ENNReal.ofReal (eta N M β)) h ∂(historyMeasure β l n) := by
            rw [lintegral_indicator (measurableSet_positiveHistory l n), setLIntegral_const]
        _ ≤ ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β l) n (n + 1) h
              (positiveHistory l (n + 1)) ∂(historyMeasure β l n) := by
            refine lintegral_mono fun h => ?_
            by_cases hh : h ∈ positiveHistory l n
            · rw [Set.indicator_of_mem hh]
              exact eta_le_partialTraj_succ hM hN hβ hl n hh
            · rw [Set.indicator_of_notMem hh]
              exact zero_le

/-- **Remark 5, iterated**: from a steep ladder, the first `m` expressions are all made from a
positive entry with probability at least `η^m`. -/
theorem eta_pow_le_pathMeasure_positiveEvents (hM : 2 ≤ M) (hN : 3 ≤ N) (hβ : 0 ≤ β)
    (hl : IsSteepLadder o l) (m : ℕ) :
    ENNReal.ofReal (eta N M β) ^ m ≤ pathMeasure β l (positiveEvents l m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have huniv : positiveEvents l 0 = Set.univ := by
      ext ω
      simp [positiveEvents]
    rw [pow_zero, huniv, measure_univ]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hmap : (pathMeasure β l).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n) = historyMeasure β l n := by
      unfold historyMeasure
      rw [pathMeasure_def, Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
        Kernel.traj_map_frestrictLe]
    rw [positiveEvents_eq_preimage, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
      (measurableSet_positiveHistory l n), hmap]
    exact eta_pow_le_historyMeasure hM hN hβ hl n

end Iterate

/-- Iterating Remark 5: from a steep ladder, the skeleton stays on `L̂` for `m` steps with
probability at least `η^m`.  This is the estimate that Proposition 9 uses to keep the process
away from a state `u ∉ L̂`.

Follows the paper, which writes, in the sketch of Proposition 9, ``by Remark 5 we show that
starting from `l ∈ L`, a sequence of events `{U_{T_{j-1}} (A_j, O_j) > 0}`'' keeps the process
on `L̂`.  The two halves of Remark 5 are `SocialNetwork.IsSteepLadder.state_of_isPositiveAt`
and `SocialNetwork.eta_pow_le_pathMeasure_positiveEvents`; the inclusion between the two events
is the only step here.

**Supplies a step the paper asserts**: the iteration itself.  Remark 5 states the one-step
bound and the sketch of Proposition 9 uses the `m`-step one without deriving it. -/
theorem eta_pow_le_pathMeasure_steepLadder (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) (m : ℕ) :
    ENNReal.ofReal (eta N M β) ^ m
      ≤ pathMeasure β l {ω : ℕ → Jump N M | ∀ k ≤ m, skeleton l k ω ∈ steepLadderSet N M} := by
  refine le_trans (eta_pow_le_pathMeasure_positiveEvents hM hN hβ hl m) (measure_mono ?_)
  intro ω hω k hk
  exact ⟨o, hl.state_of_isPositiveAt hM (Trajectory.ofPath ω) k fun j hj => hω j (by omega)⟩

end Remark5

/-! ### Proposition 9 and Corollary 10 -/

section Proposition9

variable [NeZero N] [NeZero M]

/-- The events the proof of Proposition 9 runs one after the other: the first `(M+1)N`
expressions are greedy, as in Proposition 7, and every later one is made from a positive
entry, as in Remark 5. -/
noncomputable def returnStep : ℕ → Pressure N M → Finset (Jump N M) :=
  fun k v => if k < (M + 1) * N then argmaxFinset v else posFinset v

/-- The one-step probabilities of those events: `ζ_β` while the expressions are greedy, then
`η`. -/
noncomputable def returnBound (N M : ℕ) (β : ℝ) : ℕ → ℝ≥0∞ :=
  fun k => if k < (M + 1) * N then ENNReal.ofReal (zeta N M β) else ENNReal.ofReal (eta N M β)

omit [NeZero N] [NeZero M] in
theorem isPositiveAt_shift (T : Trajectory N M) (u : Pressure N M) (m k : ℕ) :
    IsPositiveAt (T.shift m) (T.state u m) k ↔ IsPositiveAt T u (m + k) := by
  rw [isPositiveAt_iff, isPositiveAt_iff, ← T.state_add, Trajectory.shift_actor,
    Trajectory.shift_opinion]

/-- **Proposition 7 and Remark 5, composed.**  While the prescribed expressions are being
made, the skeleton is on a steep ladder from time `(M+1)N` on: the greedy run lands on
`L ⊆ L̂` (Proposition 7), and the positive expressions keep it there (Remark 5).

**No counterpart in the paper**: the paper composes the two estimates by the Markov property
at time `(M+1)N`; here they are composed on the realisation, which needs no restart. -/
theorem isSteepLadder_skeleton_of_returnStep (hM : 2 ≤ M) (hN : 3 ≤ N) {u : Pressure N M}
    (hu : IsState u) {ω : ℕ → Jump N M} {k : ℕ} (hk : (M + 1) * N ≤ k)
    (hω : ∀ j < k, ω j ∈ returnStep j (skeleton u j ω)) :
    skeleton u k ω ∈ steepLadderSet N M := by
  have hgreedy : ∀ j < (M + 1) * N, IsGreedyAt (Trajectory.ofPath ω) u j := by
    intro j hj
    have hj' := hω j (by omega)
    rw [returnStep, if_pos hj] at hj'
    exact (mem_greedyEvent_iff u j ω).2 hj'
  obtain ⟨o, hlad⟩ : skeleton u ((M + 1) * N) ω ∈ ladderSet N M :=
    isLadder_state_of_greedy (Trajectory.ofPath ω) hM hN hu hgreedy
  refine ⟨o, ?_⟩
  have hpos : ∀ j < k - (M + 1) * N,
      IsPositiveAt ((Trajectory.ofPath ω).shift ((M + 1) * N))
        ((Trajectory.ofPath ω).state u ((M + 1) * N)) j := by
    intro j hj
    rw [isPositiveAt_shift]
    have hj' := hω ((M + 1) * N + j) (by omega)
    rw [returnStep, if_neg (by omega)] at hj'
    exact mem_posFinset.1 hj'
  have hsteep := (hlad.isSteepLadder hM).state_of_isPositiveAt hM
    ((Trajectory.ofPath ω).shift ((M + 1) * N)) (k - (M + 1) * N) hpos
  have hstate : ((Trajectory.ofPath ω).shift ((M + 1) * N)).state
      (skeleton u ((M + 1) * N) ω) (k - (M + 1) * N) = skeleton u k ω := by
    show ((Trajectory.ofPath ω).shift ((M + 1) * N)).state
        ((Trajectory.ofPath ω).state u ((M + 1) * N)) (k - (M + 1) * N)
      = (Trajectory.ofPath ω).state u k
    rw [← Trajectory.state_add, Nat.add_sub_cancel' hk]
  rw [hstate] at hsteep
  exact hsteep

/-- **The step the proof of Proposition 9 asserts.**  Proposition 9 needs the greedy run of
Proposition 7 to reach `L` *without visiting `u`*, and reads that off Proposition 7:

> we first consider Proposition 7 to show that a sequence of events `ξ_j^u`,
> `j = 1, …, (M+1)N`, leads the process to `L`, without visiting `u`, with a lower bounded
> probability.

Proposition 7 says where the greedy run ends, and nothing about where it passes.  After the
run reaches `L̂` the claim is immediate — the process stays in `L̂` and `u ∉ L̂` — so what is
missing is only the transient, the times `1 ≤ k < (M+1)N` before `L` is reached.

**Unproved**, and left as the one gap of Proposition 9.  It is not a formality: greedy runs do
return to earlier matrices — from a ladder they cycle with period `N` — so the hypothesis
`u ∉ L̂` is doing work, and the argument that rules out a return has to use it.

`FOR-THE-AUTHORS.md` §1.6 records what would settle it. -/
theorem skeleton_ne_of_greedy (hM : 2 ≤ M) (hN : 3 ≤ N) {u : Pressure N M} (hu : IsState u)
    (hu' : u ∉ steepLadderSet N M) {ω : ℕ → Jump N M} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ (M + 1) * N) (hgreedy : ∀ j < k, IsGreedyAt (Trajectory.ofPath ω) u j) :
    skeleton u k ω ≠ u := by
  sorry

/-- **The lower bound on the return time**, as Proposition 9 uses it: the probability of not
coming back to `u` within `n` steps is at least `ζ_β^{(M+1)N} η^{n - (M+1)N}`. -/
theorem returnBound_prod_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {u : Pressure N M} (hu : IsState u) (hu' : u ∉ steepLadderSet N M) (n : ℕ) :
    ∏ j ∈ Finset.range n, returnBound N M β j
      ≤ pathMeasure β u {ω : ℕ → Jump N M | ∀ k < n, skeleton u (k + 1) ω ≠ u} := by
  have hone : IsStepBound β (returnStep) u (returnBound N M β) := by
    intro m ω hm
    by_cases hmT : m < (M + 1) * N
    · rw [returnBound, if_pos hmT, returnStep, if_pos hmT]
      exact zeta_le_jumpPMF_argmaxFinset hM hβ _
    · rw [returnBound, if_neg hmT, returnStep, if_neg hmT]
      obtain ⟨o, hsteep⟩ :=
        isSteepLadder_skeleton_of_returnStep hM hN hu (by omega) hm
      exact eta_le_jumpPMF_posFinset hM hN hβ hsteep
  refine le_trans (prod_le_pathMeasure_stepEvents hone n) (measure_mono ?_)
  intro ω hω k hk
  by_cases hkT : k + 1 ≤ (M + 1) * N
  · refine skeleton_ne_of_greedy hM hN hu hu' (by omega) hkT fun j hj => ?_
    have hj' := hω j (by omega)
    rw [returnStep, if_pos (by omega)] at hj'
    exact (mem_greedyEvent_iff u j ω).2 hj'
  · intro hcon
    exact hu' (hcon ▸ isSteepLadder_skeleton_of_returnStep hM hN hu (by omega)
      fun j hj => hω j (by omega))

/-! #### The arithmetic of the constant `C' = (NM)^{(M+1)N+1}` -/

omit [NeZero N] [NeZero M] in
/-- `1 - η ≤ (1 + MN) e^{-β(N-1)}`: the denominator of `η` exceeds its numerator by
`1 + MN`, and the numerator is at least its last term `e^{β(N-1)}`. -/
theorem one_sub_eta_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (_hβ : 0 ≤ β) :
    1 - eta N M β ≤ (1 + ((M * N : ℕ) : ℝ)) * Real.exp (-(β * ((N : ℝ) - 1))) := by
  have hden : (∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ)))
      = 1 + ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) :=
    sum_range_eq_one_add_sum_Ico (by omega) β
  set A := ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) with hA
  have hAterm : Real.exp (β * ((N : ℝ) - 1)) ≤ A := by
    have hmem : N - 1 ∈ Finset.Ico 1 N := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have : (1 : ℕ) ≤ N := by omega
      push_cast [Nat.cast_sub this]
      ring
    have := Finset.single_le_sum (f := fun j : ℕ => Real.exp (β * (j : ℝ)))
      (fun j _ => (Real.exp_pos _).le) hmem
    rwa [hcast] at this
  have hApos : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hAterm
  have hMN : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsub : 1 - eta N M β = (1 + ((M * N : ℕ) : ℝ)) / (1 + A + ((M * N : ℕ) : ℝ)) := by
    rw [eta, hden, ← hA]
    field_simp
    ring
  rw [hsub, Real.exp_neg, ← div_eq_mul_inv]
  gcongr
  all_goals linarith

omit [NeZero N] [NeZero M] in
/-- `(1 + MN) 2^{(M+1)N} ≤ (NM)^{(M+1)N+1}`, the arithmetic that lets the crude bound
`ζ_β ≥ 1/2` reach the paper's constant. -/
theorem one_add_mul_two_pow_le (hM : 2 ≤ M) (hN : 3 ≤ N) :
    (1 + ((M * N : ℕ) : ℝ)) * 2 ^ ((M + 1) * N)
      ≤ ((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1) := by
  set T := (M + 1) * N with hT
  set x := ((N * M : ℕ) : ℝ) with hx
  have hx6 : (6 : ℝ) ≤ x := by
    have h6 : 6 ≤ N * M := le_trans (by norm_num) (Nat.mul_le_mul hN hM)
    rw [hx]
    exact_mod_cast h6
  have hT1 : 1 ≤ T := by
    have : 1 ≤ (M + 1) * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hcast : ((M * N : ℕ) : ℝ) = x := by
    rw [hx]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.mul_comm M N)
  have h3 : (2 : ℝ) ≤ 3 ^ T := by
    calc (2 : ℝ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ T := pow_le_pow_right₀ (by norm_num) hT1
  have hkey : (2 : ℝ) * 2 ^ T ≤ x ^ T := by
    calc (2 : ℝ) * 2 ^ T ≤ 3 ^ T * 2 ^ T := by
          gcongr
      _ = 6 ^ T := by rw [← mul_pow]; norm_num
      _ ≤ x ^ T := by gcongr
  have hxpos : (0 : ℝ) < x := by linarith
  calc (1 + ((M * N : ℕ) : ℝ)) * 2 ^ T = (1 + x) * 2 ^ T := by rw [hcast]
    _ ≤ (2 * x) * 2 ^ T := by nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) T]
    _ = x * (2 * 2 ^ T) := by ring
    _ ≤ x * x ^ T := by gcongr
    _ = x ^ (T + 1) := by ring

omit [NeZero N] [NeZero M] in
/-- The regime the geometric bound does not cover: when `MN e^{-β/(M-1)} > 1`, the constant
`(NM)^{(M+1)N+1}` already exceeds `e^{β(N-1)}`, so the bound of Proposition 9 is weaker than
`μ̃^β (u) ≤ 1` and there is nothing to prove. -/
theorem exp_le_pow_of_one_lt (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    (hbig : 1 < ((M * N : ℕ) : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))) :
    Real.exp (β * ((N : ℝ) - 1)) ≤ ((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1) := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hcast : ((M * N : ℕ) : ℝ) = ((N * M : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.mul_comm M N)
  have hlt : Real.exp (β / ((M : ℝ) - 1)) < ((N * M : ℕ) : ℝ) := by
    rw [← hcast]
    have hpos : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ hpos, one_mul] at hbig
    linarith
  set k := (M - 1) * (N - 1) with hk
  have hkcast : ((k : ℕ) : ℝ) * (β / ((M : ℝ) - 1)) = β * ((N : ℝ) - 1) := by
    have h1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      have : (1 : ℕ) ≤ M := by omega
      push_cast [Nat.cast_sub this]
      ring
    have h2 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have : (1 : ℕ) ≤ N := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hk, Nat.cast_mul, h1, h2]
    field_simp
  have hkle : k ≤ (M + 1) * N + 1 := by
    have h1 : (M - 1) * (N - 1) ≤ M * N := Nat.mul_le_mul (Nat.sub_le M 1) (Nat.sub_le N 1)
    have h2 : M * N ≤ (M + 1) * N := Nat.mul_le_mul_right N (by omega)
    omega
  calc Real.exp (β * ((N : ℝ) - 1))
      = Real.exp (β / ((M : ℝ) - 1)) ^ k := by rw [← hkcast, Real.exp_nat_mul]
    _ ≤ ((N * M : ℕ) : ℝ) ^ k :=
        pow_le_pow_left₀ (Real.exp_pos _).le hlt.le k
    _ ≤ ((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1) := by
        refine pow_le_pow_right₀ ?_ hkle
        have h6 : 6 ≤ N * M := le_trans (by norm_num) (Nat.mul_le_mul hN hM)
        have h6' : (6 : ℝ) ≤ ((N * M : ℕ) : ℝ) := by exact_mod_cast h6
        linarith

omit [NeZero N] [NeZero M] in
/-- `η < 1`: the denominator of `η` exceeds its numerator by `1 + MN`. -/
theorem eta_lt_one (hN : 1 ≤ N) (β : ℝ) : eta N M β < 1 := by
  have hden : (∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ)))
      = 1 + ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) :=
    sum_range_eq_one_add_sum_Ico hN β
  have hA : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  have hMN : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [eta, hden, div_lt_one (by linarith)]
  linarith

omit [NeZero N] [NeZero M] in
/-- `1/ζ_β ≤ 2` in the regime `MN e^{-β/(M-1)} ≤ 1`. -/
theorem one_div_zeta_le (_hM : 2 ≤ M) {β : ℝ}
    (hsmall : ((M * N : ℕ) : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))) ≤ 1) :
    1 / zeta N M β ≤ 2 := by
  have hx : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have hcast : ((M * N : ℕ) : ℝ) = (M : ℝ) * (N : ℝ) := by push_cast; ring
  rw [hcast, Real.exp_neg, ← div_eq_mul_inv, div_le_one hx] at hsmall
  rw [zeta, one_div, inv_div, div_le_iff₀ hx]
  linarith

/-- **Proposition 9.**  For any `β > 0` and any state `u ∉ L̂`, the invariant measure of the
skeleton satisfies `μ̃^β (u) ≤ C' e^{-β(N-1)}`, with `C' = (NM)^{(M+1)N+1}`.

**Follows the paper's proof.**  Kac's lemma gives `μ̃^β (u) E [R̃^{β,u} (u)] ≤ 1`
(`SocialNetwork.kac_tsum_le`); the return time is bounded below by a greedy run to `L`
(Proposition 7) followed by positive expressions (Remark 5), whose probabilities are
`ζ_β^{(M+1)N}` and `η^m`; and the geometric series `∑_m η^m = 1/(1-η)` supplies the factor
`e^{β(N-1)}`, since `1 - η ≤ (1 + MN) e^{-β(N-1)}`.

**Departs from the paper in one place, and supplies two steps it asserts.**  The paper writes
Kac's lemma as the identity `1/μ̃^β (u) = E [R̃^{β,u} (u)]`, which needs the chain to be
irreducible and hence Theorem 1.2; only the inequality is used, and the inequality holds for
every invariant probability measure, so `SocialNetwork.kac_tsum_le` is proved outright and
Doeblin's criterion is not needed here.  The two supplied steps are the composition of
Proposition 7 with Remark 5, done on the realisation rather than through a restart
(`SocialNetwork.isSteepLadder_skeleton_of_returnStep`), and the arithmetic that reaches the
printed constant, which needs the regime `MN e^{-β/(M-1)} > 1` to be treated separately:
there the constant already exceeds `e^{β(N-1)}` and `μ̃^β (u) ≤ 1` suffices.

**Rests on** `SocialNetwork.skeleton_ne_of_greedy`, the assertion that the greedy run reaches
`L` without visiting `u`, and through Proposition 7 on Lemmas 19 and 20.

**Stated for an arbitrary invariant probability measure** of the skeleton rather than for a
named `μ̃^β`, since its existence is itself Theorem 1.2, and with `IsState u` added: the paper
works throughout in `S`, and Proposition 7 — which this proof calls — is stated there. -/
theorem measure_le_of_notMem_steepLadderSet (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {μ : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) {u : Pressure N M} (huS : IsState u)
    (hu : u ∉ steepLadderSet N M) :
    μ {u} ≤ ENNReal.ofReal
      ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1)) * Real.exp (-β * ((N : ℝ) - 1))) := by
  have := hμ
  have hneg : -β * ((N : ℝ) - 1) = -(β * ((N : ℝ) - 1)) := by ring
  by_cases hbig : 1 < ((M * N : ℕ) : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))
  · -- The constant already exceeds `e^{β(N-1)}`, and `μ̃^β` is a probability measure.
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hneg, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    exact exp_le_pow_of_one_lt hM hN hβ hbig
  · rw [not_lt] at hbig
    have hζpos : 0 < zeta N M β := zeta_pos N M β
    have hη0 : (0 : ℝ) ≤ eta N M β := eta_nonneg N M
    have hη1 : eta N M β < 1 := eta_lt_one (by omega) β
    set T := (M + 1) * N with hT
    set a := zeta N M β ^ T / (1 - eta N M β) with ha
    have hapos : 0 < a := div_pos (pow_pos hζpos T) (by linarith)
    -- Kac's inequality, with the return time bounded below by Proposition 7 and Remark 5.
    have hkac : μ {u} * ∑' n : ℕ, ∏ j ∈ Finset.range n, returnBound N M β j ≤ 1 :=
      measure_singleton_le_of_avoid (skeletonKernel β) μ hinv u _ fun n => by
        rw [lintegral_kacAvoid_skeletonKernel]
        exact returnBound_prod_le hM hN hβ.le huS hu n
    have hprodT : ∀ i : ℕ, ∏ j ∈ Finset.range (T + i), returnBound N M β j
        = ENNReal.ofReal (zeta N M β) ^ T * ENNReal.ofReal (eta N M β) ^ i := by
      intro i
      induction i with
      | zero =>
          rw [Nat.add_zero, pow_zero, mul_one,
            Finset.prod_congr rfl (fun j hj => by
              rw [returnBound, if_pos (Finset.mem_range.1 hj)]),
            Finset.prod_const, Finset.card_range]
      | succ i ih =>
          rw [show T + (i + 1) = (T + i) + 1 by ring, Finset.prod_range_succ, ih,
            returnBound, if_neg (by omega), pow_succ, mul_assoc]
    have hgeo : ENNReal.ofReal a ≤ ∑' n : ℕ, ∏ j ∈ Finset.range n, returnBound N M β j := by
      have hinj : Function.Injective fun i : ℕ => T + i := fun i j h => Nat.add_left_cancel h
      refine le_trans (le_of_eq ?_)
        (ENNReal.tsum_comp_le_tsum_of_injective hinj
          fun n => ∏ j ∈ Finset.range n, returnBound N M β j)
      simp only [hprodT]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ha,
        ENNReal.ofReal_div_of_pos (by linarith : (0 : ℝ) < 1 - eta N M β),
        ENNReal.ofReal_pow hζpos.le, ENNReal.ofReal_sub 1 hη0, ENNReal.ofReal_one,
        div_eq_mul_inv]
    have hmul : μ {u} * ENNReal.ofReal a ≤ 1 := le_trans (by gcongr) hkac
    refine le_trans (ENNReal.le_inv_iff_mul_le.2 hmul) ?_
    rw [← ENNReal.ofReal_inv_of_pos hapos]
    refine ENNReal.ofReal_le_ofReal ?_
    have hinva : a⁻¹ = (1 - eta N M β) * (1 / zeta N M β) ^ T := by
      rw [ha, inv_div, div_eq_mul_inv, one_div, inv_pow]
    have hz : 1 / zeta N M β ≤ 2 := one_div_zeta_le hM hbig
    have hz0 : (0 : ℝ) ≤ 1 / zeta N M β := by positivity
    rw [hinva, hneg]
    have hA1 : 1 - eta N M β
        ≤ (1 + ((M * N : ℕ) : ℝ)) * Real.exp (-(β * ((N : ℝ) - 1))) :=
      one_sub_eta_le hM hN hβ.le
    have hA2 : (1 / zeta N M β) ^ T ≤ 2 ^ T := pow_le_pow_left₀ hz0 hz T
    calc (1 - eta N M β) * (1 / zeta N M β) ^ T
        ≤ ((1 + ((M * N : ℕ) : ℝ)) * Real.exp (-(β * ((N : ℝ) - 1)))) * 2 ^ T :=
          mul_le_mul hA1 hA2 (by positivity) (by positivity)
      _ = ((1 + ((M * N : ℕ) : ℝ)) * 2 ^ T) * Real.exp (-(β * ((N : ℝ) - 1))) := by ring
      _ ≤ (((N * M : ℕ) : ℝ) ^ (T + 1)) * Real.exp (-(β * ((N : ℝ) - 1))) := by
          gcongr
          exact one_add_mul_two_pow_le hM hN

/-! ### Corollary 10: the zero matrix

The extra exponent of Corollary 10 rests on one observation, which the paper makes and does not
argue: the zero matrix can only be entered from a state in which one actor carries no pressure
at all, while every other carries `-1` on the expressed opinion and `1/(M-1)` on each of the
others.  `SocialNetwork.zeroPredecessor` is that state — there are `NM` of them, one per pair
`(a, o)` — and `SocialNetwork.eq_zeroPredecessor_of_express_eq_zero` is the observation.

Two things then have to be checked rather than asserted.  The first is that the observation
applies where it is used: a predecessor of `0` is pinned down only once it is known to have a
null row, and the invariant measure charges nothing else
(`SocialNetwork.measure_exists_zero_row_eq_one`), because every matrix the kernel reaches in one
step has one.  The second is the exponent itself: at a `zeroPredecessor` the pair that leads to
`0` carries the rate `e^0 = 1`, against a total that already contains the `e^{β/(M-1)}` of any
actor that is not `a` on any opinion that is not `o`, so the step into `0` costs `e^{-β/(M-1)}`
(`SocialNetwork.skeletonKernel_zeroPredecessor_le`). -/

section Predecessors

-- Nothing in this block needs the network to be non-empty: it is the arithmetic of `π^{a,o}`.
omit [NeZero N] [NeZero M]

/-- The state from which expressing `(a, o)` leads to the zero matrix: actor `a` carries no
pressure at all, and every other actor carries `-1` on `o` and `1/(M-1)` on each of the other
opinions — in the scaled coordinates of `SocialNetwork.Defs`, `1 - M` on `o` and `1` elsewhere.

**Supplies a step the paper asserts.**  The description is read off in one line in the proof of
Corollary 10; that it is the *only* such state is
`SocialNetwork.eq_zeroPredecessor_of_express_eq_zero`. -/
def zeroPredecessor (a : Actor N) (o : Opinion M) : Pressure N M :=
  fun b p => if b = a then 0 else if p = o then 1 - (M : ℤ) else 1

@[simp]
theorem zeroPredecessor_self (a : Actor N) (o p : Opinion M) :
    zeroPredecessor a o a p = 0 := by
  simp [zeroPredecessor]

theorem zeroPredecessor_of_ne {a b : Actor N} (hb : b ≠ a) (o p : Opinion M) :
    zeroPredecessor a o b p = if p = o then 1 - (M : ℤ) else 1 := by
  simp [zeroPredecessor, hb]

/-- Expressing `(a, o)` at `zeroPredecessor a o` does lead to the zero matrix: the row of `a`
is reset, the `-1` on `o` is cancelled by the gain of `M - 1`, and each `1` elsewhere by the
loss of `1`. -/
theorem express_zeroPredecessor (a : Actor N) (o : Opinion M) :
    express a o (zeroPredecessor a o) = (0 : Pressure N M) := by
  funext b p
  simp only [Pi.zero_apply]
  by_cases hb : b = a
  · subst hb; simp
  · by_cases hp : p = o
    · subst hp
      rw [express_of_ne_of_eq hb, zeroPredecessor_of_ne hb, if_pos rfl]
      ring
    · rw [express_of_ne_of_ne hb hp, zeroPredecessor_of_ne hb, if_neg hp]
      ring

/-- **The observation behind Corollary 10.**  A matrix with a null row from which one expression
reaches `0` is a `SocialNetwork.zeroPredecessor`.

The null row is what makes the description exhaustive, and it is not a restriction here: the
skeleton reaches nothing else (`SocialNetwork.measure_exists_zero_row_eq_one`).  Without it the
predecessors of `0` form an infinite family, since the row of the expressing actor is reset and
so is unconstrained. -/
theorem eq_zeroPredecessor_of_express_eq_zero (hM : 2 ≤ M) {v : Pressure N M} {a : Actor N}
    {o : Opinion M} (h : express a o v = 0) (hz : ∃ b, ∀ p, v b p = 0) :
    v = zeroPredecessor a o := by
  have hM' : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  obtain ⟨b, hb⟩ := hz
  have hrow : ∀ c, c ≠ a → ∀ p, v c p = if p = o then 1 - (M : ℤ) else 1 := by
    intro c hc p
    have hcp := congrFun (congrFun h c) p
    simp only [Pi.zero_apply] at hcp
    by_cases hp : p = o
    · subst hp
      rw [express_of_ne_of_eq hc] at hcp
      rw [if_pos rfl]
      linarith
    · rw [express_of_ne_of_ne hc hp] at hcp
      rw [if_neg hp]
      linarith
  have hba : b = a := by
    by_contra hne
    have h0 := hrow b hne o
    rw [hb o, if_pos rfl] at h0
    linarith
  have ha0 : ∀ p, v a p = 0 := hba ▸ hb
  funext c p
  by_cases hc : c = a
  · subst hc
    rw [ha0 p, zeroPredecessor_self]
  · rw [hrow c hc p, zeroPredecessor_of_ne hc]

/-- A `SocialNetwork.zeroPredecessor` is a state of `S`: the row of `a` is null, and every other
row carries `1 - M` once and `1` on each of the remaining `M - 1` opinions, hence has trust `0`. -/
theorem isState_zeroPredecessor (a : Actor N) (o : Opinion M) :
    IsState (zeroPredecessor a o) := by
  refine ⟨fun c => ?_, ⟨a, fun p => zeroPredecessor_self a o p⟩⟩
  by_cases hc : c = a
  · subst hc; simp [trust]
  · have hval : ∀ p : Opinion M,
        zeroPredecessor a o c p = 1 + (if p = o then -(M : ℤ) else 0) := by
      intro p
      rw [zeroPredecessor_of_ne hc]
      by_cases hp : p = o
      · simp [hp]; ring
      · simp [hp]
    rw [trust, Finset.sum_congr rfl fun p _ => hval p, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ o fun _ => -(M : ℤ)]
    simp

/-- A `SocialNetwork.zeroPredecessor` is not a steep ladder, so Proposition 9 bounds its mass.
With `N ≥ 3` at least two actors are not `a`, and they carry the same pressure on every opinion;
Definition 4 asks the column of the favoured opinion to be injective. -/
theorem notMem_steepLadderSet_zeroPredecessor (hN : 3 ≤ N) (a : Actor N) (o : Opinion M) :
    zeroPredecessor a o ∉ steepLadderSet N M := by
  rintro ⟨q, hq⟩
  have hcard : 1 < ({a}ᶜ : Finset (Actor N)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨b, hbmem, c, hcmem, hbc⟩ := Finset.one_lt_card.1 hcard
  have hb : b ≠ a := by simpa using hbmem
  have hc : c ≠ a := by simpa using hcmem
  have : zeroPredecessor a o b q = zeroPredecessor a o c q := by
    rw [zeroPredecessor_of_ne hb, zeroPredecessor_of_ne hc]
  exact hbc (hq.injective this)

/-- At a `SocialNetwork.zeroPredecessor`, the only expression that reaches `0` is the one it is
named for.  This is what makes the cost of the step into `0` a single jump probability rather
than a sum of them. -/
theorem eq_of_express_zeroPredecessor_eq_zero (hM : 2 ≤ M) (hN : 2 ≤ N) {a c : Actor N}
    {o q : Opinion M} (h : express c q (zeroPredecessor a o) = (0 : Pressure N M)) :
    c = a ∧ q = o := by
  have hM' : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hca : c = a := by
    by_contra hne
    have hac : a ≠ c := fun hh => hne hh.symm
    have haq := congrFun (congrFun h a) q
    simp only [Pi.zero_apply, express_of_ne_of_eq hac, zeroPredecessor_self] at haq
    linarith
  subst hca
  refine ⟨rfl, ?_⟩
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) c
  have hbq := congrFun (congrFun h b) q
  simp only [Pi.zero_apply, express_of_ne_of_eq hb, zeroPredecessor_of_ne hb] at hbq
  by_contra hq
  rw [if_neg hq] at hbq
  linarith

end Predecessors

/-- **The exponent of Corollary 10.**  One step from a `SocialNetwork.zeroPredecessor` lands on
the zero matrix with probability at most `e^{-β/(M-1)}`.

The pair `(a, o)` is the only one that reaches `0`, and it carries the rate `e^{β · 0} = 1`,
while the normalisation already contains the rate `e^{β/(M-1)}` of any other actor on any other
opinion.  The other `NM - 1` rates in the normalisation are discarded, which is why this is a
bound and not the exact probability. -/
theorem skeletonKernel_zeroPredecessor_le (hM : 2 ≤ M) (hN : 2 ≤ N) (β : ℝ) (a : Actor N)
    (o : Opinion M) :
    skeletonKernel β (zeroPredecessor a o) {(0 : Pressure N M)}
      ≤ ENNReal.ofReal (Real.exp (-β * (1 / ((M : ℝ) - 1)))) := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  set v : Pressure N M := zeroPredecessor a o with hv
  -- The only pair that reaches `0` is `(a, o)`.
  have hone : skeletonKernel β v {(0 : Pressure N M)} = jumpPMF β v (a, o) := by
    rw [skeletonKernel_apply, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
      PMF.map_apply]
    refine tsum_eq_single (a, o) ?_ |>.trans ?_
    · intro p hp
      refine if_neg fun hcontra => hp ?_
      obtain ⟨h1, h2⟩ := eq_of_express_zeroPredecessor_eq_zero hM hN hcontra.symm
      exact Prod.ext h1 h2
    · exact if_pos (express_zeroPredecessor a o).symm
  -- Its rate is `1`, and the total is at least the rate of some `(b, q)` with `b ≠ a`, `q ≠ o`.
  have hweight : jumpWeight β v (a, o) = 1 := by
    rw [jumpWeight, jumpRate, hv, zeroPredecessor_self]
    norm_num
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) a
  obtain ⟨q, hq⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) o
  have hlow : ENNReal.ofReal (Real.exp (β * (1 / ((M : ℝ) - 1))))
      ≤ ∑' p : Jump N M, jumpWeight β v p := by
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (b, q))
    rw [jumpWeight, jumpRate, hv, zeroPredecessor_of_ne hb, if_neg hq]
    norm_num [div_eq_mul_inv]
  rw [hone, jumpPMF_apply, hweight, one_mul]
  calc (∑' p : Jump N M, jumpWeight β v p)⁻¹
      ≤ (ENNReal.ofReal (Real.exp (β * (1 / ((M : ℝ) - 1)))))⁻¹ := ENNReal.inv_le_inv.2 hlow
    _ = ENNReal.ofReal (Real.exp (-β * (1 / ((M : ℝ) - 1)))) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
        ring_nf

/-- The invariant measure of the skeleton charges only the matrices with a null row.

Nothing is needed beyond the shape of `π^{a,o}`: every matrix the kernel reaches has the row of
the expressing actor reset, so the set of matrices with a null row has full mass under
`κ v` for every `v`, and invariance carries that to `μ`.

**No counterpart in the paper**, which works throughout in `S`; the proof of Corollary 10 needs
only the second half of the definition of `S`, and gets it for free. -/
theorem measure_exists_zero_row_eq_one (β : ℝ) {μ : Measure (Pressure N M)}
    [IsProbabilityMeasure μ] (hinv : Kernel.Invariant (skeletonKernel β) μ) :
    μ {v : Pressure N M | ∃ b, ∀ p, v b p = 0} = 1 := by
  set Z : Set (Pressure N M) := {v | ∃ b, ∀ p, v b p = 0} with hZ
  have hker : ∀ v : Pressure N M, skeletonKernel β v Z = 1 := by
    intro v
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = skeletonKernel β v {w | ∃ a o, w = express a o v} :=
          (skeletonKernel_reachable β v).symm
      _ ≤ skeletonKernel β v Z := by
          refine measure_mono ?_
          rintro w ⟨c, q, rfl⟩
          exact ⟨c, fun p => express_self c q p v⟩
  calc μ Z = (μ.bind (skeletonKernel β)) Z := by rw [hinv.def]
    _ = ∫⁻ v, skeletonKernel β v Z ∂μ :=
        Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)
    _ = 1 := by simp [hker]

/-- **Corollary 10.**  `μ̃^β (0) ≤ C'' e^{-β(N-1+1/(M-1))}` with `C'' = (NM) C'`.

**Follows the paper's proof.**  Invariance writes `μ̃^β (0)` as `∑_v μ̃^β (v) P (Ũ_1^{β,v} = 0)`;
only the `NM` states `SocialNetwork.zeroPredecessor a o` contribute, since the invariant
measure charges only matrices with a null row and those are the only predecessors of `0` with
one; each is bounded by Proposition 9, since none of them is a steep ladder; and each step
into `0` costs `e^{-β/(M-1)}`, which is the extra exponent.

**Rests on** Proposition 9, and through it on `SocialNetwork.skeleton_ne_of_greedy` and
Lemmas 19 and 20. -/
theorem measure_zero_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {μ : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) :
    μ {(0 : Pressure N M)} ≤ ENNReal.ofReal
      ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 2)) *
        Real.exp (-β * ((N : ℝ) - 1 + 1 / ((M : ℝ) - 1)))) := by
  have := hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β * (1 / ((M : ℝ) - 1)))) with hc
  set P : Set (Pressure N M) := {w | ∃ a o, w = zeroPredecessor a o} with hP
  set C : ℝ :=
    ((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1) * Real.exp (-β * ((N : ℝ) - 1)) with hC
  -- Invariance, at the singleton `{0}`.
  have hbind : μ {(0 : Pressure N M)}
      = ∫⁻ v, skeletonKernel β v {(0 : Pressure N M)} ∂μ := by
    conv_lhs => rw [← hinv.def]
    exact Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)
  -- Only the `NM` predecessors contribute, and each contributes at most `c`.
  have hpt : ∀ v : Pressure N M, (∃ b, ∀ p, v b p = 0) →
      skeletonKernel β v {(0 : Pressure N M)} ≤ Set.indicator P (fun _ => c) v := by
    intro v hz
    by_cases hvP : v ∈ P
    · rw [Set.indicator_of_mem hvP]
      obtain ⟨a, o, rfl⟩ := hvP
      exact skeletonKernel_zeroPredecessor_le hM (by omega) β a o
    · rw [Set.indicator_of_notMem hvP]
      have h0R : (0 : Pressure N M) ∉ {w : Pressure N M | ∃ a o, w = express a o v} := by
        rintro ⟨a, o, ha⟩
        exact hvP ⟨a, o, eq_zeroPredecessor_of_express_eq_zero hM ha.symm hz⟩
      calc skeletonKernel β v {(0 : Pressure N M)}
          ≤ skeletonKernel β v {w : Pressure N M | ∃ a o, w = express a o v}ᶜ :=
            measure_mono (Set.singleton_subset_iff.2 h0R)
        _ = 0 := (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2
              (skeletonKernel_reachable β v)
  have hZ : ∀ᵐ v ∂μ, ∃ b, ∀ p, v b p = 0 := by
    rw [MeasureTheory.ae_iff]
    exact (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2
      (measure_exists_zero_row_eq_one β hinv)
  have hint : ∫⁻ v, skeletonKernel β v {(0 : Pressure N M)} ∂μ ≤ c * μ P := by
    calc ∫⁻ v, skeletonKernel β v {(0 : Pressure N M)} ∂μ
        ≤ ∫⁻ v, Set.indicator P (fun _ => c) v ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hZ] with v hv using hpt v hv
      _ = c * μ P := by
          rw [lintegral_indicator MeasurableSet.of_discrete, setLIntegral_const]
  -- The `NM` predecessors are states off `L̂`, so Proposition 9 bounds each of them.
  have hPle : μ P ≤ ((N * M : ℕ) : ℝ≥0∞) * ENNReal.ofReal C := by
    have hcover : P = ⋃ p : Jump N M, {zeroPredecessor p.1 p.2} := by
      ext w
      simp [hP, Prod.exists, eq_comm]
    have hterm : ∀ p : Jump N M, μ {zeroPredecessor p.1 p.2} ≤ ENNReal.ofReal C := fun p =>
      measure_le_of_notMem_steepLadderSet hM hN hβ hμ hinv (isState_zeroPredecessor p.1 p.2)
        (notMem_steepLadderSet_zeroPredecessor hN p.1 p.2)
    calc μ P ≤ ∑' p : Jump N M, μ {zeroPredecessor p.1 p.2} := by
          rw [hcover]; exact measure_iUnion_le _
      _ = ∑ p : Jump N M, μ {zeroPredecessor p.1 p.2} := tsum_fintype _
      _ ≤ ∑ _p : Jump N M, ENNReal.ofReal C := Finset.sum_le_sum fun p _ => hterm p
      _ = ((N * M : ℕ) : ℝ≥0∞) * ENNReal.ofReal C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          congr 2
          simp [Jump]
  -- The arithmetic: `e^{-β/(M-1)} · NM · C' e^{-β(N-1)} = C'' e^{-β(N-1+1/(M-1))}`.
  have harith : c * (((N * M : ℕ) : ℝ≥0∞) * ENNReal.ofReal C)
      = ENNReal.ofReal ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 2)) *
        Real.exp (-β * ((N : ℝ) - 1 + 1 / ((M : ℝ) - 1)))) := by
    rw [hc, ← ENNReal.ofReal_natCast (N * M), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [hC, show (-β * ((N : ℝ) - 1 + 1 / ((M : ℝ) - 1)))
        = (-β * ((N : ℝ) - 1)) + (-β * (1 / ((M : ℝ) - 1))) by ring, Real.exp_add,
      show (M + 1) * N + 2 = ((M + 1) * N + 1) + 1 from rfl, pow_succ]
    ring
  calc μ {(0 : Pressure N M)} = ∫⁻ v, skeletonKernel β v {(0 : Pressure N M)} ∂μ := hbind
    _ ≤ c * μ P := hint
    _ ≤ c * (((N * M : ℕ) : ℝ≥0∞) * ENNReal.ofReal C) := by gcongr
    _ = _ := harith

end Proposition9

end SocialNetwork
