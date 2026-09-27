/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.JumpHold

/-!
# Theorem 1.1: the process does not explode

`SocialNetwork.nonExplosion` is Theorem 1.1 of arXiv:2607.19651: from any state of `S`, the
jump times `Tₙ` are almost surely unbounded, so the process is defined for every `t ≥ 0`.

## The paper's proof, and what this file supplies

The proof at p. 16 splits the expressions into those coming from an actor carrying pressure
below `N` and the others, and sandwiches the first between two Poisson processes, of rates
`MN` and `λ = NMe^{βN}`.  Only the upper bound is used, and only through its consequence.
This file supplies the two halves of it:

* `SocialNetwork.lowRate_le_clockBound` — the low-pressure pairs carry total rate at most
  `λ = NMe^{βN}`, whatever the rest of the matrix does.  This is the content of (11): there
  are at most `NM` such pairs, and the scaled coordinates turn `‖u (a, ·)‖_∞ < N` into a rate
  at most `e^{βN}`.
* `SocialNetwork.exists_isLowAt_block` — Proposition 5, applied at every block of `N` steps
  rather than only at the first, which the paper does silently.

`SocialNetwork.measure_explosionTime_eq_one` then carries the domination across the jumps,
where the state and so the rates change; that is the step the paper asserts and does not
construct, and `SocialNetwork.JumpHold` says exactly what it proves instead.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ}

/-! ### The low-pressure family and the bound `λ` of equation (11) -/

/-- The pairs whose actor carries social pressure below `N`, in the scaled coordinates of
`SocialNetwork.Defs`.  This is the family whose clocks equation (11) bounds. -/
def lowFinset (v : Pressure N M) : Finset (Jump N M) :=
  {p | rowSup v p.1 < N * (M - 1)}

theorem mem_lowFinset {v : Pressure N M} {p : Jump N M} :
    p ∈ lowFinset v ↔ rowSup v p.1 < N * (M - 1) := by
  simp [lowFinset]

/-- The total rate carried by the low-pressure family. -/
noncomputable def lowRate (β : ℝ) (v : Pressure N M) : ℝ :=
  ∑ p ∈ lowFinset v, jumpRate β v p.1 p.2

theorem lowRate_nonneg (β : ℝ) (v : Pressure N M) : 0 ≤ lowRate β v :=
  Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le

/-- The constant `λ = NMe^{βN}` of equation (11). -/
noncomputable def clockBound (N M : ℕ) (β : ℝ) : ℝ := ((N * M : ℕ) : ℝ) * Real.exp (β * (N : ℝ))

theorem clockBound_pos (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ) : 0 < clockBound N M β := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hNM : (0 : ℝ) < ((N * M : ℕ) : ℝ) := by positivity
  unfold clockBound
  positivity

/-- **The upper bound of equation (11).**  Whatever the rest of the matrix does, the pairs
whose actor carries pressure below `N` have total rate at most `λ = NMe^{βN}`: there are at
most `NM` of them and each carries rate at most `e^{βN}`. -/
theorem lowRate_le_clockBound (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    lowRate β v ≤ clockBound N M β := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hterm : ∀ p ∈ lowFinset v, jumpRate β v p.1 p.2 ≤ Real.exp (β * (N : ℝ)) := by
    intro p hp
    have hrow : rowSup v p.1 < N * (M - 1) := mem_lowFinset.1 hp
    have habs : (v p.1 p.2).natAbs < N * (M - 1) := lt_of_le_of_lt (le_rowSup v p.1 p.2) hrow
    have hint : (v p.1 p.2) ≤ ((N * (M - 1) : ℕ) : ℤ) := by omega
    have hcast : (((N * (M - 1) : ℕ) : ℤ) : ℝ) = (N : ℝ) * ((M : ℝ) - 1) := by
      have h1 : 1 ≤ M := le_trans one_le_two hM
      push_cast [Nat.cast_sub h1]
      ring
    have hreal : (v p.1 p.2 : ℝ) ≤ (N : ℝ) * ((M : ℝ) - 1) := by
      rw [← hcast]; exact_mod_cast hint
    rw [jumpRate]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ hM1]
    nlinarith
  calc lowRate β v ≤ ∑ _p ∈ lowFinset v, Real.exp (β * (N : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (lowFinset v).card * Real.exp (β * (N : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ clockBound N M β := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have hcard : (lowFinset v).card ≤ N * M := by
          calc (lowFinset v).card ≤ (Finset.univ : Finset (Jump N M)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = N * M := by simp [Finset.card_univ, Fintype.card_prod]
        exact_mod_cast hcard

theorem lowRate_le_totalRate (β : ℝ) (v : Pressure N M) : lowRate β v ≤ totalRate β v :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (jumpRate_pos β v p.1 p.2).le

variable [NeZero N] [NeZero M]

/-! ### The Gibbs mass carried by a family of pairs -/

/-- The Gibbs law of equation (3) gives a family of pairs the fraction of the total rate that
it carries. -/
theorem jumpPMF_toMeasure_finset (β : ℝ) (v : Pressure N M) (s : Finset (Jump N M)) :
    (jumpPMF β v).toMeasure ↑s
      = ENNReal.ofReal ((∑ p ∈ s, jumpRate β v p.1 p.2) / totalRate β v) := by
  have hw : ∀ t : Finset (Jump N M),
      (∑ p ∈ t, jumpWeight β v p) = ENNReal.ofReal (∑ p ∈ t, jumpRate β v p.1 p.2) := by
    intro t
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le]
    rfl
  have htsum : (∑' q : Jump N M, jumpWeight β v q) = ENNReal.ofReal (totalRate β v) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp, hw Finset.univ]
    rfl
  rw [PMF.toMeasure_apply_finset]
  simp only [jumpPMF_apply]
  rw [← Finset.sum_mul, hw s, htsum, ← ENNReal.ofReal_inv_of_pos (totalRate_pos β v),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le),
    ← div_eq_mul_inv]

/-! ### The one-step estimate -/

/-- **One step of the process, discounted.**  Weighting a step by `e^{-θH}`, and by the extra
factor `(λ + θ) / λ` when the pair expressed comes from the low-pressure family, gives total
mass at most `1`.

This is all of the paper's (11) that Theorem 1.1 uses: the low family carries rate at most `λ`
whatever the rest of the matrix does, so discounting its jumps at the rate `λ` costs nothing. -/
theorem lintegral_stepLaw_stepWeight_le_one (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {θ : ℝ}
    (hθ : 0 < θ) (v : Pressure N M) :
    ∫⁻ z, stepWeight (ENNReal.ofReal ((clockBound N M β + θ) / clockBound N M β)) θ
      (lowFinset v) z ∂(stepLaw β v) ≤ 1 := by
  have hmassc : (jumpPMF β v).toMeasure ((↑(lowFinset v) : Set (Jump N M))ᶜ)
      = ENNReal.ofReal ((totalRate β v - lowRate β v) / totalRate β v) := by
    rw [← Finset.coe_compl, jumpPMF_toMeasure_finset β v]
    congr 1
    have hsplit := Finset.sum_compl_add_sum (lowFinset v)
      fun p : Jump N M => jumpRate β v p.1 p.2
    rw [lowRate, totalRate]
    rw [show (∑ p ∈ (lowFinset v)ᶜ, jumpRate β v p.1 p.2)
        = (∑ p : Jump N M, jumpRate β v p.1 p.2)
          - ∑ p ∈ lowFinset v, jumpRate β v p.1 p.2 by rw [← hsplit]; ring]
  exact lintegral_stepWeight_le_one (totalRate_pos β v) (clockBound_pos N M β) hθ
    (lowRate_nonneg β v) (lowRate_le_totalRate β v) (lowRate_le_clockBound hM hβ v)
    (jumpPMF_toMeasure_finset β v _) hmassc

/-! ### Proposition 5 at every block -/

/-- Step `k` of a realisation is *low* when the pair expressed at it comes from the
low-pressure family of the matrix reached at that step. -/
def IsLowAt (u : Pressure N M) (k : ℕ) (j : ℕ → Jump N M) : Prop :=
  j k ∈ lowFinset ((Trajectory.ofPath j).state u k)

instance decidableIsLowAt (u : Pressure N M) (k : ℕ) (j : ℕ → Jump N M) :
    Decidable (IsLowAt u k j) := inferInstanceAs (Decidable (_ ∈ _))

omit [NeZero N] [NeZero M] in
/-- Whether step `k` is low is read off the first `k + 1` expressed pairs. -/
theorem isLowAt_congr (u : Pressure N M) (k : ℕ) (j j' : ℕ → Jump N M)
    (h : ∀ i ≤ k, j i = j' i) : IsLowAt u k j ↔ IsLowAt u k j' := by
  have hst : (Trajectory.ofPath j).state u k = (Trajectory.ofPath j').state u k :=
    Trajectory.state_congr u k
      (fun i hi => by show (j i).1 = (j' i).1; rw [h i hi.le])
      (fun i hi => by show (j i).2 = (j' i).2; rw [h i hi.le])
  rw [IsLowAt, IsLowAt, hst, h k le_rfl]

omit [NeZero N] [NeZero M] in
/-- **Proposition 5, read at the `m`-th block of `N` steps.**  Among any `N` consecutive
expressions at least one comes from an actor carrying pressure below `N`: the matrix reached
after `mN` expressions is still a state of `S`, and Proposition 5 applies to the realisation
read from there. -/
theorem exists_isLowAt_block (hM : 2 ≤ M) {u : Pressure N M} (hu : IsState u)
    (j : ℕ → Jump N M) (m : ℕ) :
    ∃ k, m * N ≤ k ∧ k < m * N + N ∧ IsLowAt u k j := by
  set T := Trajectory.ofPath j with hT
  obtain ⟨i, hiN, hi⟩ :=
    exists_rowSup_actor_lt (T.shift (m * N)) hM (T.isState_state hu (m * N))
  refine ⟨m * N + i, by omega, by omega, ?_⟩
  rw [IsLowAt, mem_lowFinset]
  rw [Trajectory.shift_actor, ← Trajectory.state_add] at hi
  exact hi

omit [NeZero N] [NeZero M] in
/-- At least one step in every `N` is low, so after `m` blocks at least `m` steps are. -/
theorem le_lowCountOf (hM : 2 ≤ M) {u : Pressure N M} (hu : IsState u) (j : ℕ → Jump N M)
    (m : ℕ) : m ≤ lowCountOf (IsLowAt u) (m * N) j := by
  induction m with
  | zero => simp [lowCountOf]
  | succ m ih =>
      obtain ⟨k, hk1, hk2, hk3⟩ := exists_isLowAt_block hM hu j m
      have hsub : {i ∈ Finset.range (m * N) | IsLowAt u i j}
          ⊆ {i ∈ Finset.range ((m + 1) * N) | IsLowAt u i j} := by
        have hrange : Finset.range (m * N) ⊆ Finset.range ((m + 1) * N) := by
          have hsucc : (m + 1) * N = m * N + N := by ring
          rw [hsucc]
          exact Finset.range_subset.2 fun x hx => Finset.mem_range.2 (by omega)
        exact Finset.filter_subset_filter _ hrange
      have hmem : k ∈ {i ∈ Finset.range ((m + 1) * N) | IsLowAt u i j} := by
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hk3⟩
        have hsucc : (m + 1) * N = m * N + N := by ring
        rw [hsucc]
        omega
      have hnot : k ∉ {i ∈ Finset.range (m * N) | IsLowAt u i j} := by
        intro hcon
        exact absurd (Finset.mem_range.1 (Finset.mem_filter.1 hcon).1) (by omega)
      have hlt : lowCountOf (IsLowAt u) (m * N) j < lowCountOf (IsLowAt u) ((m + 1) * N) j :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨k, hmem, hnot⟩)
      omega

/-! ### Theorem 1.1 -/

theorem one_lt_discountRatio {β θ : ℝ} (hθ : 0 < θ) :
    1 < ENNReal.ofReal ((clockBound N M β + θ) / clockBound N M β) := by
  have hL : 0 < clockBound N M β := clockBound_pos N M β
  refine ENNReal.one_lt_ofReal.2 ?_
  rw [lt_div_iff₀ hL]
  linarith

/-- **Theorem 1.1.**  For any `β ≥ 0` and any starting matrix `u ∈ S`, the jump times satisfy
`P (sup {Tₘ : m ≥ 1} = ∞) = 1`: the process does not explode.

**Follows the paper's proof**, whose sandwich (11) it supplies.  Proposition 5 gives one
expression from an actor carrying pressure below `N` in every `N`, and those expressions carry
total rate at most `λ = NMe^{βN}` whatever the rest of the matrix does; so the jump times
dominate the points of a Poisson process of rate `λ`, which are unbounded.  The domination is
carried across the jumps by `SocialNetwork.measure_explosionTime_eq_one`, in the form the
conclusion needs: the weight `e^{-θTₙ}d^{Kₙ}` is a supermartingale, where `Kₙ` counts the low
expressions and `d = (λ + θ)/λ`. -/
theorem nonExplosion (hM : 2 ≤ M) (_hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) :
    ctsPathMeasure β u {ω | explosionTime ω = ⊤} = 1 := by
  have hmeas : ctsPathMeasure β u
      = jumpHoldMeasure (ctsDrivingKernel β u) (stepLaw β u) := rfl
  rw [hmeas]
  refine measure_explosionTime_eq_one (low := IsLowAt u) (D := ENNReal.ofReal
      ((clockBound N M β + 1) / clockBound N M β)) (θ := 1) _ _ (isLowAt_congr u)
    (fun n h => lowFinset ((Trajectory.ofStepHistory h).state u (n + 1))) (lowFinset u)
    ?_ ?_ ?_ ?_ one_pos (one_lt_discountRatio one_pos) (b := N) ?_
  · -- the first step
    intro z
    rw [IsLowAt, Trajectory.state_zero]
  · -- a later step
    intro n h x hx
    have hjx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n)
        (fun i => (x i).1) = fun i => (h i).1 := by
      funext i
      exact congrArg (fun y : (i : Finset.Iic n) → Step N M => (y i).1) hx
    have hstate : (Trajectory.ofPath (jumpExtend fun i => (x i).1)).state u (n + 1)
        = (Trajectory.ofStepHistory h).state u (n + 1) := ofHistory_state_eq hjx u le_rfl
    rw [IsLowAt, jumps_stepExtend, hstate, stepExtend_apply _ (le_refl (n + 1))]
  · exact lintegral_stepLaw_stepWeight_le_one hM hβ one_pos u
  · intro n h
    rw [ctsDrivingKernel_apply]
    exact lintegral_stepLaw_stepWeight_le_one hM hβ one_pos _
  · exact fun j q => le_lowCountOf hM hu j q

end SocialNetwork
