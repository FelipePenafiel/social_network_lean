/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedResults
import SocialNetwork.NonExplosion

/-!
# Theorem 16: the biased process does not explode

`SocialNetwork.Bias.biasedNonExplosion` is Theorem 16 of arXiv:2607.19651, the twin of
Theorem 1.1 for the biased model.

Appendix C says the proof is that of Theorem 1 with Proposition 21 in place of Proposition 5,
and that is what this file is: the low-pressure family of a profile carries total rate at most
`λ = NMe^{βN}` (`SocialNetwork.Bias.lowRate_le_clockBound`), Proposition 21 puts one of its
pairs in every `N` expressions (`SocialNetwork.Bias.exists_isLowAt_block`), and
`SocialNetwork.measure_explosionTime_eq_one` — which is stated for a jump-hold chain, not for
either model — does the rest.  The two models share every step but these two.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

namespace Bias

variable {N M : ℕ}

/-! ### The low-pressure family of a profile -/

/-- The pairs carrying social pressure below `N` at the profile `P`.  This is the family whose
clocks equation (11) bounds, in the biased model. -/
noncomputable def lowFinset (γ : ℝ) (P : Profile N M) : Finset (Jump N M) :=
  {p | P.pressure γ p.1 p.2 < (N : ℝ)}

theorem mem_lowFinset {γ : ℝ} {P : Profile N M} {p : Jump N M} :
    p ∈ lowFinset γ P ↔ P.pressure γ p.1 p.2 < (N : ℝ) := by
  simp [lowFinset]

/-- The total rate carried by the low-pressure family. -/
noncomputable def lowRate (γ β : ℝ) (P : Profile N M) : ℝ :=
  ∑ p ∈ lowFinset γ P, biasedJumpRate γ β P p.1 p.2

theorem lowRate_nonneg (γ β : ℝ) (P : Profile N M) : 0 ≤ lowRate γ β P :=
  Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le

theorem lowRate_le_biasedTotalRate (γ β : ℝ) (P : Profile N M) :
    lowRate γ β P ≤ biasedTotalRate γ β P :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (biasedJumpRate_pos γ β P p.1 p.2).le

/-- **The upper bound of equation (11)**, in the biased model: whatever the rest of the profile
does, the pairs carrying pressure below `N` have total rate at most `λ = NMe^{βN}`. -/
theorem lowRate_le_clockBound {β : ℝ} (hβ : 0 ≤ β) (γ : ℝ) (P : Profile N M) :
    lowRate γ β P ≤ clockBound N M β := by
  have hterm : ∀ p ∈ lowFinset γ P,
      biasedJumpRate γ β P p.1 p.2 ≤ Real.exp (β * (N : ℝ)) := by
    intro p hp
    rw [biasedJumpRate]
    exact Real.exp_le_exp.2 (by nlinarith [mem_lowFinset.1 hp])
  calc lowRate γ β P ≤ ∑ _p ∈ lowFinset γ P, Real.exp (β * (N : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (lowFinset γ P).card * Real.exp (β * (N : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ clockBound N M β := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have hcard : (lowFinset γ P).card ≤ N * M := by
          calc (lowFinset γ P).card ≤ (Finset.univ : Finset (Jump N M)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = N * M := by simp [Finset.card_univ, Fintype.card_prod]
        exact_mod_cast hcard

variable [NeZero N] [NeZero M]

/-- The Gibbs law of equation (7) gives a family of pairs the fraction of the total rate that
it carries. -/
theorem biasedJumpPMF_toMeasure_finset (γ β : ℝ) (P : Profile N M) (s : Finset (Jump N M)) :
    (biasedJumpPMF γ β P).toMeasure ↑s
      = ENNReal.ofReal ((∑ p ∈ s, biasedJumpRate γ β P p.1 p.2) / biasedTotalRate γ β P) := by
  have hw : ∀ t : Finset (Jump N M),
      (∑ p ∈ t, biasedJumpWeight γ β P p)
        = ENNReal.ofReal (∑ p ∈ t, biasedJumpRate γ β P p.1 p.2) := by
    intro t
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le]
    rfl
  have htsum : (∑' q : Jump N M, biasedJumpWeight γ β P q)
      = ENNReal.ofReal (biasedTotalRate γ β P) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp, hw Finset.univ]
    rfl
  rw [PMF.toMeasure_apply_finset]
  simp only [biasedJumpPMF_apply]
  rw [← Finset.sum_mul, hw s, htsum,
    ← ENNReal.ofReal_inv_of_pos (biasedTotalRate_pos γ β P),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le),
    ← div_eq_mul_inv]

/-- **One step of the biased process, discounted**: the estimate of
`SocialNetwork.lintegral_stepLaw_stepWeight_le_one` at a profile. -/
theorem lintegral_biasedStepLaw_stepWeight_le_one {β : ℝ} (hβ : 0 ≤ β) {θ : ℝ} (hθ : 0 < θ)
    (γ : ℝ) (P : Profile N M) :
    ∫⁻ z, stepWeight (ENNReal.ofReal ((clockBound N M β + θ) / clockBound N M β)) θ
      (lowFinset γ P) z ∂(biasedStepLaw γ β P) ≤ 1 := by
  have hmassc : (biasedJumpPMF γ β P).toMeasure ((↑(lowFinset γ P) : Set (Jump N M))ᶜ)
      = ENNReal.ofReal ((biasedTotalRate γ β P - lowRate γ β P) / biasedTotalRate γ β P) := by
    rw [← Finset.coe_compl, biasedJumpPMF_toMeasure_finset γ β P]
    congr 1
    have hsplit := Finset.sum_compl_add_sum (lowFinset γ P)
      fun p : Jump N M => biasedJumpRate γ β P p.1 p.2
    rw [lowRate, biasedTotalRate]
    rw [show (∑ p ∈ (lowFinset γ P)ᶜ, biasedJumpRate γ β P p.1 p.2)
        = (∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2)
          - ∑ p ∈ lowFinset γ P, biasedJumpRate γ β P p.1 p.2 by rw [← hsplit]; ring]
  exact lintegral_stepWeight_le_one (biasedTotalRate_pos γ β P) (clockBound_pos N M β) hθ
    (lowRate_nonneg γ β P) (lowRate_le_biasedTotalRate γ β P) (lowRate_le_clockBound hβ γ P)
    (biasedJumpPMF_toMeasure_finset γ β P _) hmassc

/-! ### Proposition 21 at every block -/

/-- Step `k` of a realisation is *low* when the pair expressed at it carries pressure below `N`
at the profile reached at that step. -/
noncomputable def IsLowAt (γ : ℝ) (u : Profile N M) (k : ℕ) (j : ℕ → Jump N M) : Prop :=
  j k ∈ lowFinset γ (stateAfter u j k)

noncomputable instance decidableIsLowAt (γ : ℝ) (u : Profile N M) (k : ℕ) (j : ℕ → Jump N M) :
    Decidable (IsLowAt γ u k j) := inferInstanceAs (Decidable (_ ∈ _))

omit [NeZero N] [NeZero M] in
/-- Whether step `k` is low is read off the first `k + 1` expressed pairs. -/
theorem isLowAt_congr (γ : ℝ) (u : Profile N M) (k : ℕ) (j j' : ℕ → Jump N M)
    (h : ∀ i ≤ k, j i = j' i) : IsLowAt γ u k j ↔ IsLowAt γ u k j' := by
  rw [IsLowAt, IsLowAt, stateAfter_congr u k fun i hi => h i hi.le, h k le_rfl]

omit [NeZero N] [NeZero M] in
/-- **Proposition 21, read at the `m`-th block of `N` steps.**  The profile reached after `mN`
expressions is still a state of `S^α`, so Proposition 21 applies to the realisation read from
there. -/
theorem exists_isLowAt_block (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) {u : Profile N M}
    (hu : IsBiasedState u) (j : ℕ → Jump N M) (m : ℕ) :
    ∃ k, m * N ≤ k ∧ k < m * N + N ∧ IsLowAt γ u k j := by
  obtain ⟨i, hiN, hi⟩ := exists_pressure_lt hM hN hγ
    (isBiasedState_stateAfter hu j (m * N)) (shiftPath (m * N) j)
  refine ⟨m * N + i, by omega, by omega, ?_⟩
  rw [IsLowAt, mem_lowFinset, stateAfter_add]
  exact hi _

omit [NeZero N] [NeZero M] in
/-- At least one step in every `N` is low, so after `m` blocks at least `m` steps are. -/
theorem le_lowCountOf (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) {u : Profile N M}
    (hu : IsBiasedState u) (j : ℕ → Jump N M) (m : ℕ) :
    m ≤ lowCountOf (IsLowAt γ u) (m * N) j := by
  induction m with
  | zero => simp [lowCountOf]
  | succ m ih =>
      obtain ⟨k, hk1, hk2, hk3⟩ := exists_isLowAt_block hM hN hγ hu j m
      have hsub : {i ∈ Finset.range (m * N) | IsLowAt γ u i j}
          ⊆ {i ∈ Finset.range ((m + 1) * N) | IsLowAt γ u i j} := by
        have hrange : Finset.range (m * N) ⊆ Finset.range ((m + 1) * N) := by
          have hsucc : (m + 1) * N = m * N + N := by ring
          rw [hsucc]
          exact Finset.range_subset.2 fun x hx => Finset.mem_range.2 (by omega)
        exact Finset.filter_subset_filter _ hrange
      have hmem : k ∈ {i ∈ Finset.range ((m + 1) * N) | IsLowAt γ u i j} := by
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hk3⟩
        have hsucc : (m + 1) * N = m * N + N := by ring
        rw [hsucc]
        omega
      have hnot : k ∉ {i ∈ Finset.range (m * N) | IsLowAt γ u i j} := by
        intro hcon
        exact absurd (Finset.mem_range.1 (Finset.mem_filter.1 hcon).1) (by omega)
      have hlt : lowCountOf (IsLowAt γ u) (m * N) j
          < lowCountOf (IsLowAt γ u) ((m + 1) * N) j :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨k, hmem, hnot⟩)
      omega

/-! ### Theorem 16 -/

/-- **Theorem 16.**  For any `β ≥ 0`, any `α < 0` and any starting profile `u ∈ S^α`, the jump
times of the biased process satisfy `P (sup {Tₘ : m ≥ 1} = ∞) = 1`.

**Follows the paper's proof of Theorem 1**, once Proposition 21 replaces Proposition 5, which
is what Appendix C prescribes.  The two models share everything else:
`SocialNetwork.measure_explosionTime_eq_one` carries the domination across the jumps here as
it does there. -/
theorem biasedNonExplosion (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    biasedCtsPathMeasure γ β u {ω | explosionTime ω = ⊤} = 1 := by
  have hγ0 : (0 : ℝ) < γ := by
    refine lt_trans (one_div_pos.2 ?_) hγ
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hmeas : biasedCtsPathMeasure γ β u
      = jumpHoldMeasure (biasedCtsDrivingKernel γ β u) (biasedStepLaw γ β u) := rfl
  rw [hmeas]
  refine measure_explosionTime_eq_one (low := IsLowAt γ u) (D := ENNReal.ofReal
      ((clockBound N M β + 1) / clockBound N M β)) (θ := 1) _ _ (isLowAt_congr γ u)
    (fun n h => lowFinset γ (stateAfterStepHistory u h (n + 1))) (lowFinset γ u)
    ?_ ?_ ?_ ?_ one_pos (one_lt_discountRatio one_pos) (b := N) ?_
  · intro z
    rw [IsLowAt, stateAfter_zero]
  · intro n h x hx
    have hjx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n)
        (fun i => (x i).1) = fun i => (h i).1 := by
      funext i
      exact congrArg (fun y : (i : Finset.Iic n) → Step N M => (y i).1) hx
    have hstate : stateAfter u (jumpExtend fun i => (x i).1) (n + 1)
        = stateAfterStepHistory u h (n + 1) := stateAfter_ofHistoryPath_eq hjx u le_rfl
    rw [IsLowAt, jumps_stepExtend, hstate, stepExtend_apply _ (le_refl (n + 1))]
  · exact lintegral_biasedStepLaw_stepWeight_le_one hβ one_pos γ u
  · intro n h
    rw [biasedCtsDrivingKernel_apply]
    exact lintegral_biasedStepLaw_stepWeight_le_one hβ one_pos γ _
  · exact fun j q => le_lowCountOf hM hN hγ0 hu j q

end Bias

end SocialNetwork
