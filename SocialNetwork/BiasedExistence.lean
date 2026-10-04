/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedNonExplosion
import SocialNetwork.BiasedTransfer
import SocialNetwork.Existence

/-!
# Theorem 25.2: the invariant measure of the biased process

Theorem 25 of arXiv:2607.19651 says that for `0 < α < 1/(M-1)` the biased process has a unique
invariant probability measure `μ_{β,α}`, and that "the proof of Theorem 25 follows exactly as
the proof of Theorem 1".  Uniqueness is `SocialNetwork.Bias.eq_of_biasedInvariantCts`, from
equation (13).  This file proves existence, by transposing `SocialNetwork.Existence`: the
right-hand side of equation (13), built from the skeleton's `μ̃_{α,β}`, is invariant for the
process.

## The argument

Unchanged from the unbiased one.  For `μ` with `(q · μ) K ≤ q · μ`, decompose `P_t` along the
number of expressions made by time `t`; this needs the process not to explode, which is
Theorem 25.1 (`SocialNetwork.Bias.biasedNonExplosion_of_pos`).  The first-step and last-step
operators commute by Tonelli and agree on `P^{(0)}`, so `P^{(n+1)}` decomposes along its last
expression, and an induction on the number of expressions gives `μ P_t ≤ μ`, hence equality.

What changes is the state: the profile of `SocialNetwork.BiasedModel`, the replay
`SocialNetwork.Bias.stateAfter`, and the rate of equation (7).  The operators are written again
for profiles; the lemmas that know nothing about the model — the jump times, the explosion
time, the measures on a countable space — are those of `SocialNetwork.Existence` and
`SocialNetwork.Transfer`.

## Main statements

* `SocialNetwork.Bias.IsBiasedState.le_biasedTotalRate` — `q ≥ M` on `S^α`.
* `SocialNetwork.Bias.biasedNJump_succ_eq_lastStep` — `P^{(n+1)} = 𝓛 P^{(n)}`.
* `SocialNetwork.Bias.biasedTransitionKernel_le_tsum_nJump` — the decomposition, from
  Theorem 25.1.
* `SocialNetwork.Bias.isBiasedInvariantCts_iff` — the correspondence of p. 18 for the biased
  process, both directions.
* `SocialNetwork.Bias.existsUnique_biasedInvariantCts` — **Theorem 25.2**.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

namespace Bias

variable {N M : ℕ}

/-! ### The rate floor on `S^α` -/

section RateFloor

/-- On `S^α` the total jump rate is at least `M`: the actor that has heard nothing carries a
null row, and its `M` pairs each have rate `e^0 = 1`.

The bound equation (13) uses in the unbiased model (`SocialNetwork.IsState.le_totalRate`),
which Appendix C transports with the rest of the proof of Theorem 1. -/
theorem IsBiasedState.le_biasedTotalRate (γ β : ℝ) {P : Profile N M} (hP : IsBiasedState P) :
    (M : ℝ) ≤ biasedTotalRate γ β P := by
  obtain ⟨a, ha⟩ := hP.exists_zero_row
  have hrow : ∑ o : Opinion M, biasedJumpRate γ β P a o = (M : ℝ) := by
    have h : ∀ o : Opinion M, biasedJumpRate γ β P a o = 1 := fun o => by
      rw [biasedJumpRate, Profile.pressure_eq_zero_of_heard_eq_zero γ ha o, mul_zero,
        Real.exp_zero]
    rw [Finset.sum_congr rfl fun o _ => h o]
    simp
  have hsum : biasedTotalRate γ β P = ∑ b : Actor N, ∑ o : Opinion M, biasedJumpRate γ β P b o := by
    rw [biasedTotalRate]
    exact Fintype.sum_prod_type _
  rw [hsum, ← hrow]
  exact Finset.single_le_sum
    (fun b _ => Finset.sum_nonneg fun o _ => (biasedJumpRate_pos γ β P b o).le)
    (Finset.mem_univ a)

/-- The normalising sum of equation (13) is at most `1/M`, hence finite. -/
theorem tsum_div_biasedTotalRate_le (γ β : ℝ) (μ : Measure (Profile N M))
    [IsProbabilityMeasure μ] (hμ : IsCarriedByBiasedState μ) :
    ∑' v : Profile N M, μ {v} / ENNReal.ofReal (biasedTotalRate γ β v) ≤ 1 / (M : ℝ≥0∞) := by
  have hterm : ∀ v : Profile N M,
      μ {v} / ENNReal.ofReal (biasedTotalRate γ β v) ≤ μ {v} / (M : ℝ≥0∞) := by
    intro v
    by_cases hv : IsBiasedState v
    · refine ENNReal.div_le_div_left ?_ _
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (hv.le_biasedTotalRate γ β)
    · have hzero : μ {v} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.2 hv) hμ
      simp [hzero]
  have hsum : ∑' v : Profile N M, μ {v} / (M : ℝ≥0∞) = 1 / (M : ℝ≥0∞) := by
    rw [tsum_congr fun v => div_eq_mul_inv (μ {v}) ((M : ℝ≥0∞)), ENNReal.tsum_mul_right,
      tsum_measure_singleton μ, ← div_eq_mul_inv]
  calc ∑' v : Profile N M, μ {v} / ENNReal.ofReal (biasedTotalRate γ β v)
      ≤ ∑' v : Profile N M, μ {v} / (M : ℝ≥0∞) := ENNReal.tsum_le_tsum hterm
    _ = 1 / (M : ℝ≥0∞) := hsum

end RateFloor

variable [NeZero N] [NeZero M]

/-! ### The holding time, as a survival function -/

section Survival

/-- `e^{-q(v) t}` for `t ≥ 0`, and `0` before time `0`. -/
noncomputable def biasedSurvival (γ β : ℝ) (v : Profile N M) (t : ℝ) : ℝ≥0∞ :=
  Set.indicator (Set.Ici 0)
    (fun s => ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β v * s)))) t

omit [NeZero N] [NeZero M] in
theorem measurable_biasedSurvival (γ β : ℝ) (v : Profile N M) :
    Measurable (biasedSurvival γ β v) := by
  refine Measurable.indicator ?_ measurableSet_Ici
  fun_prop

omit [NeZero N] [NeZero M] in
/-- The exponential density is the rate times the survival function. -/
theorem exponentialPDF_biasedTotalRate (γ β : ℝ) (v : Profile N M) (s : ℝ) :
    exponentialPDF (biasedTotalRate γ β v) s
      = ENNReal.ofReal (biasedTotalRate γ β v) * biasedSurvival γ β v s := by
  have hq : 0 ≤ biasedTotalRate γ β v :=
    Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β v p.1 p.2).le
  rw [exponentialPDF_eq, biasedSurvival]
  by_cases hs : 0 ≤ s
  · rw [if_pos hs, Set.indicator_of_mem (Set.mem_Ici.2 hs), ENNReal.ofReal_mul hq]
  · have hs' : s ∉ Set.Ici (0 : ℝ) := by simpa using hs
    rw [if_neg hs, Set.indicator_of_notMem hs', ENNReal.ofReal_zero, mul_zero]

omit [NeZero N] [NeZero M] in
/-- Integrating against the exponential law is integrating against its density. -/
theorem lintegral_expMeasure_biasedTotalRate (γ β : ℝ) (v : Profile N M) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ s, f s ∂(expMeasure (biasedTotalRate γ β v))
      = ENNReal.ofReal (biasedTotalRate γ β v) * ∫⁻ s, biasedSurvival γ β v s * f s := by
  have hsf : Measurable fun s => biasedSurvival γ β v s * f s :=
    (measurable_biasedSurvival γ β v).mul hf
  have hd : Measurable (exponentialPDF (biasedTotalRate γ β v)) :=
    (measurable_exponentialPDFReal (biasedTotalRate γ β v)).ennreal_ofReal
  rw [show expMeasure (biasedTotalRate γ β v)
      = volume.withDensity (exponentialPDF (biasedTotalRate γ β v)) from rfl,
    lintegral_withDensity_eq_lintegral_mul _ hd hf, ← lintegral_const_mul _ hsf]
  refine lintegral_congr fun s => ?_
  rw [Pi.mul_apply, exponentialPDF_biasedTotalRate, mul_assoc]

/-- **No mass is lost by time `t`**: `e^{-q t} + q ∫_0^t e^{-q r} dr = 1` for `t ≥ 0`. -/
theorem biasedSurvival_add_lintegral (γ β : ℝ) (w : Profile N M) (t : ℝ) :
    biasedSurvival γ β w t + ENNReal.ofReal (biasedTotalRate γ β w)
        * ∫⁻ r, biasedSurvival γ β w r * Set.indicator (Set.Ici 0) 1 (t - r)
      = Set.indicator (Set.Ici 0) 1 t := by
  have hq := biasedTotalRate_pos γ β w
  have hind : Measurable fun r : ℝ => Set.indicator (Set.Ici (0 : ℝ)) (1 : ℝ → ℝ≥0∞) (t - r) :=
    (measurable_one.indicator measurableSet_Ici).comp (measurable_const.sub measurable_id)
  have hE : ENNReal.ofReal (biasedTotalRate γ β w)
        * ∫⁻ r, biasedSurvival γ β w r * Set.indicator (Set.Ici 0) 1 (t - r)
      = expMeasure (biasedTotalRate γ β w) (Set.Iic t) := by
    rw [← lintegral_expMeasure_biasedTotalRate γ β w hind,
      ← lintegral_indicator_one measurableSet_Iic]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ≤ t
    · have h1 : t - r ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici]; linarith
      have h2 : r ∈ Set.Iic t := hr
      simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
    · have h1 : t - r ∉ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici, not_le]; linarith
      have h2 : r ∉ Set.Iic t := hr
      simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  rw [hE]
  by_cases ht : 0 ≤ t
  · have h1 : Real.exp (-(biasedTotalRate γ β w * t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    rw [biasedSurvival, Set.indicator_of_mem (Set.mem_Ici.2 ht),
      Set.indicator_of_mem (Set.mem_Ici.2 ht), expMeasure_Iic_of_nonneg hq ht, Pi.one_apply,
      ← ENNReal.ofReal_add (Real.exp_pos _).le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  · have hnull : expMeasure (biasedTotalRate γ β w) (Set.Iic t) = 0 :=
      measure_mono_null (Set.Iic_subset_Iic.2 (le_of_not_ge ht)) (expMeasure_Iic_zero hq)
    have ht' : t ∉ Set.Ici (0 : ℝ) := by simpa using ht
    rw [biasedSurvival, Set.indicator_of_notMem ht', Set.indicator_of_notMem ht', hnull,
      zero_add]

end Survival

/-! ### Exactly `n` expressions by time `t` -/

section Count

/-- The realisations that have made exactly `n` expressions by time `t` and sit at `w`. -/
def biasedNJumpSet (v w : Profile N M) (n : ℕ) (t : ℝ) : Set (ℕ → Step N M) :=
  {ω | jumpTime n ω ≤ t ∧ t < jumpTime (n + 1) ω ∧ stateAfter v (fun k => (ω k).1) n = w}

/-- The same events, at all times at once. -/
def biasedNJumpGraph (v w : Profile N M) (n : ℕ) : Set (ℝ × (ℕ → Step N M)) :=
  {x | x.2 ∈ biasedNJumpSet v w n x.1}

omit [NeZero N] [NeZero M] in
theorem measurableSet_biasedNJumpGraph (v w : Profile N M) (n : ℕ) :
    MeasurableSet (biasedNJumpGraph v w n) := by
  have h1 : Measurable fun x : ℝ × (ℕ → Step N M) => jumpTime n x.2 :=
    (measurable_jumpTime n).comp measurable_snd
  have h2 : Measurable fun x : ℝ × (ℕ → Step N M) => jumpTime (n + 1) x.2 :=
    (measurable_jumpTime (n + 1)).comp measurable_snd
  have h3 : Measurable fun x : ℝ × (ℕ → Step N M) => stateAfter v (fun k => (x.2 k).1) n :=
    (measurable_stateAfter_ofStepPath v n).comp measurable_snd
  have hset : biasedNJumpGraph v w n
      = {x : ℝ × (ℕ → Step N M) | jumpTime n x.2 ≤ x.1}
        ∩ ({x | x.1 < jumpTime (n + 1) x.2}
          ∩ ((fun x : ℝ × (ℕ → Step N M) => stateAfter v (fun k => (x.2 k).1) n) ⁻¹' {w})) :=
    rfl
  rw [hset]
  exact (measurableSet_le h1 measurable_fst).inter
    ((measurableSet_lt measurable_fst h2).inter (h3 (measurableSet_singleton w)))

omit [NeZero N] [NeZero M] in
theorem measurableSet_biasedNJumpSet (v w : Profile N M) (n : ℕ) (t : ℝ) :
    MeasurableSet (biasedNJumpSet v w n t) := by
  show MeasurableSet (Prod.mk t ⁻¹' biasedNJumpGraph v w n)
  exact measurable_prodMk_left (measurableSet_biasedNJumpGraph v w n)

/-- `P^{(n)}_t (v, w)`: the chance, from `v`, of having made exactly `n` expressions by time `t`
and sitting at `w`. -/
noncomputable def biasedNJump (γ β : ℝ) (v w : Profile N M) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  biasedCtsPathMeasure γ β v (biasedNJumpSet v w n t)

theorem measurable_biasedNJump (γ β : ℝ) (v w : Profile N M) (n : ℕ) :
    Measurable (biasedNJump γ β v w n) :=
  measurable_measure_prodMk_left (measurableSet_biasedNJumpGraph v w n)

open Classical in
/-- **No expression by time `t`.** -/
theorem biasedNJump_zero (γ β : ℝ) (v w : Profile N M) (t : ℝ) :
    biasedNJump γ β v w 0 t = if v = w then biasedSurvival γ β v t else 0 := by
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl]
    by_cases ht : 0 ≤ t
    · have hset : biasedNJumpSet v v 0 t = {ω | t < holdingTime 0 ω} := by
        ext ω
        simp [biasedNJumpSet, ht, jumpTime_one]
      rw [biasedNJump, hset, biasedCtsPathMeasure_lt_holdingTime γ β v ht, biasedSurvival,
        Set.indicator_of_mem (Set.mem_Ici.2 ht)]
    · have hset : biasedNJumpSet v v 0 t = ∅ := by
        ext ω
        simp [biasedNJumpSet, ht]
      have ht' : t ∉ Set.Ici (0 : ℝ) := by simpa using ht
      rw [biasedNJump, hset, measure_empty, biasedSurvival, Set.indicator_of_notMem ht']
  · rw [if_neg hvw]
    have hset : biasedNJumpSet v w 0 t = ∅ := by
      ext ω
      simp [biasedNJumpSet, hvw]
    rw [biasedNJump, hset, measure_empty]

end Count

/-! ### Restarting at the first expression -/

section Restart

omit [NeZero N] [NeZero M] in
/-- The profile after `n + 1` expressions is the one the rest of the realisation reaches in `n`
expressions from the profile the first pair produced. -/
theorem stateAfter_succ_eq_shiftStepPath (v : Profile N M) (n : ℕ) (ω : ℕ → Step N M) :
    stateAfter v (fun k => (ω k).1) (n + 1)
      = stateAfter (Profile.express (ω 0).1.1 (ω 0).1.2 v)
          (fun k => (shiftStepPath ω k).1) n := by
  rw [show n + 1 = 1 + n by omega, stateAfter_add]
  rfl

/-- The event of `biasedNJumpSet v w (n + 1) t`, read on the first step and the rest. -/
def biasedNJumpPairs (v w : Profile N M) (n : ℕ) (t : ℝ) :
    Set (Step N M × (ℕ → Step N M)) :=
  {x | x.2 ∈ biasedNJumpSet (Profile.express x.1.1.1 x.1.1.2 v) w n (t - x.1.2)}

omit [NeZero N] [NeZero M] in
theorem biasedNJumpSet_succ_eq_preimage (v w : Profile N M) (n : ℕ) (t : ℝ) :
    biasedNJumpSet v w (n + 1) t = {ω | (ω 0, shiftStepPath ω) ∈ biasedNJumpPairs v w n t} := by
  ext ω
  have e1 := jumpTime_succ_eq_shift n ω
  have e2 := jumpTime_succ_eq_shift (n + 1) ω
  have e3 := stateAfter_succ_eq_shiftStepPath v n ω
  simp only [holdingTime] at e1 e2
  simp only [biasedNJumpSet, biasedNJumpPairs, Set.mem_ofPred_eq, e3]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, h3⟩

omit [NeZero N] [NeZero M] in
theorem measurableSet_biasedNJumpPairs (v w : Profile N M) (n : ℕ) (t : ℝ) :
    MeasurableSet (biasedNJumpPairs v w n t) := by
  have hset : biasedNJumpPairs v w n t = ⋃ p : Jump N M,
      ((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹' {p})
        ∩ ((fun x : Step N M × (ℕ → Step N M) => (t - x.1.2, x.2)) ⁻¹'
            biasedNJumpGraph (Profile.express p.1 p.2 v) w n) := by
    ext x
    simp only [biasedNJumpPairs, biasedNJumpGraph, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨x.1.1, rfl, h⟩
    · rintro ⟨p, rfl, h⟩
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun p => ?_
  refine ((measurable_fst.comp measurable_fst) (measurableSet_singleton p)).inter ?_
  exact ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    (measurableSet_biasedNJumpGraph _ w n)

/-- **Restarting at the first expression**, on the step itself. -/
theorem biasedNJump_succ (γ β : ℝ) (v w : Profile N M) (n : ℕ) (t : ℝ) :
    biasedNJump γ β v w (n + 1) t
      = ∫⁻ z, biasedNJump γ β (Profile.express z.1.1 z.1.2 v) w n (t - z.2)
          ∂(biasedStepLaw γ β v) := by
  rw [biasedNJump, biasedNJumpSet_succ_eq_preimage,
    biasedCtsPathMeasure_firstStep_apply γ β v (measurableSet_biasedNJumpPairs v w n t)]
  exact lintegral_congr fun z => rfl

/-- The first-step operator `𝓑`. -/
noncomputable def biasedFirstStep (γ β : ℝ) (F : Profile N M → Profile N M → ℝ → ℝ≥0∞)
    (v w : Profile N M) (t : ℝ) : ℝ≥0∞ :=
  ∑' u, biasedSkeletonKernel γ β v {u}
    * ∫⁻ s, F u w (t - s) ∂(expMeasure (biasedTotalRate γ β v))

/-- **`P^{(n+1)} = 𝓑 P^{(n)}`.** -/
theorem biasedNJump_succ_eq_firstStep (γ β : ℝ) (v w : Profile N M) (n : ℕ) (t : ℝ) :
    biasedNJump γ β v w (n + 1) t
      = biasedFirstStep γ β (fun u x s => biasedNJump γ β u x n s) v w t := by
  have hE : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β v)) :=
    isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β v)
  have hmeas : Measurable fun z : Jump N M × ℝ =>
      biasedNJump γ β (Profile.express z.1.1 z.1.2 v) w n (t - z.2) := by
    refine measurable_from_prod_countable_right fun p => ?_
    exact (measurable_biasedNJump γ β (Profile.express p.1 p.2 v) w n).comp
      (measurable_const.sub measurable_id)
  have hg : Measurable fun u : Profile N M =>
      ∫⁻ s, biasedNJump γ β u w n (t - s) ∂(expMeasure (biasedTotalRate γ β v)) :=
    measurable_of_countable _
  have hmap : biasedSkeletonKernel γ β v
      = (biasedJumpPMF γ β v).toMeasure.map (fun p : Jump N M => Profile.express p.1 p.2 v) := by
    rw [biasedSkeletonKernel_apply, PMF.toMeasure_map _ _ (measurable_of_countable _)]
  have hstep : ∫⁻ z, biasedNJump γ β (Profile.express z.1.1 z.1.2 v) w n (t - z.2)
        ∂(biasedStepLaw γ β v)
      = ∫⁻ u, ∫⁻ s, biasedNJump γ β u w n (t - s) ∂(expMeasure (biasedTotalRate γ β v))
          ∂(biasedSkeletonKernel γ β v) := by
    rw [biasedStepLaw, lintegral_prod _ hmeas.aemeasurable, hmap,
      lintegral_map hg (measurable_of_countable _)]
  rw [biasedNJump_succ, hstep, lintegral_countable', biasedFirstStep]
  exact tsum_congr fun u => mul_comm _ _

end Restart

/-! ### The last-step operator, and why it agrees with the first -/

section LastStep

/-- The last-step operator `𝓛`. -/
noncomputable def biasedLastStep (γ β : ℝ) (F : Profile N M → Profile N M → ℝ → ℝ≥0∞)
    (v w : Profile N M) (t : ℝ) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
    * ∫⁻ r, biasedSurvival γ β w r * F v x (t - r)

/-- **`𝓑` and `𝓛` commute**, by Tonelli. -/
theorem biasedFirstStep_lastStep (γ β : ℝ) {F : Profile N M → Profile N M → ℝ → ℝ≥0∞}
    (hF : ∀ u x, Measurable (F u x)) (v w : Profile N M) (t : ℝ) :
    biasedFirstStep γ β (biasedLastStep γ β F) v w t
      = biasedLastStep γ β (biasedFirstStep γ β F) v w t := by
  set E := expMeasure (biasedTotalRate γ β v) with hEdef
  have hE : IsProbabilityMeasure E := isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β v)
  have hjoint : ∀ u x, Measurable fun p : ℝ × ℝ =>
      biasedSurvival γ β w p.2 * F u x (t - p.1 - p.2) :=
    fun u x => ((measurable_biasedSurvival γ β w).comp measurable_snd).mul
      ((hF u x).comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  have hjoint' : ∀ u x, Measurable fun p : ℝ × ℝ =>
      biasedSurvival γ β w p.1 * F u x (t - p.1 - p.2) :=
    fun u x => ((measurable_biasedSurvival γ β w).comp measurable_fst).mul
      ((hF u x).comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  -- the two time integrals, in either order
  have hswap : ∀ u x, ∫⁻ s, ∫⁻ r, biasedSurvival γ β w r * F u x (t - s - r) ∂volume ∂E
      = ∫⁻ r, ∫⁻ s, biasedSurvival γ β w r * F u x (t - r - s) ∂E ∂volume := by
    intro u x
    rw [lintegral_lintegral_swap (f := fun s r => biasedSurvival γ β w r * F u x (t - s - r))
      (hjoint u x).aemeasurable]
    refine lintegral_congr fun r => lintegral_congr fun s => ?_
    rw [sub_sub, sub_sub, add_comm s r]
  have hL : ∀ u, ∫⁻ s, biasedLastStep γ β F u w (t - s) ∂E
      = ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
          * ∫⁻ s, ∫⁻ r, biasedSurvival γ β w r * F u x (t - s - r) ∂volume ∂E := by
    intro u
    have hm : ∀ x, Measurable fun s => ∫⁻ r, biasedSurvival γ β w r * F u x (t - s - r) :=
      fun x => Measurable.lintegral_prod_right
        (f := fun s r : ℝ => biasedSurvival γ β w r * F u x (t - s - r)) (hjoint u x)
    simp only [biasedLastStep]
    rw [lintegral_tsum fun x => ((hm x).const_mul _).aemeasurable]
    exact tsum_congr fun x => lintegral_const_mul _ (hm x)
  have hR : ∀ x, ∫⁻ r, biasedSurvival γ β w r * biasedFirstStep γ β F v x (t - r)
      = ∑' u, biasedSkeletonKernel γ β v {u}
          * ∫⁻ r, ∫⁻ s, biasedSurvival γ β w r * F u x (t - r - s) ∂E ∂volume := by
    intro x
    have hJ : ∀ u, Measurable fun r => ∫⁻ s, F u x (t - r - s) ∂E := fun u =>
      Measurable.lintegral_prod_right (f := fun r s : ℝ => F u x (t - r - s))
        ((hF u x).comp ((measurable_const.sub measurable_fst).sub measurable_snd))
    have hK : ∀ u, Measurable fun r => ∫⁻ s, biasedSurvival γ β w r * F u x (t - r - s) ∂E :=
      fun u => Measurable.lintegral_prod_right
        (f := fun r s : ℝ => biasedSurvival γ β w r * F u x (t - r - s)) (hjoint' u x)
    have hT : ∀ u, Measurable fun r =>
        biasedSurvival γ β w r * (biasedSkeletonKernel γ β v {u} * ∫⁻ s, F u x (t - r - s) ∂E) :=
      fun u => (measurable_biasedSurvival γ β w).mul ((hJ u).const_mul _)
    simp only [biasedFirstStep]
    rw [← hEdef]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum fun u => (hT u).aemeasurable]
    refine tsum_congr fun u => ?_
    have hpt : ∀ r, biasedSurvival γ β w r
          * (biasedSkeletonKernel γ β v {u} * ∫⁻ s, F u x (t - r - s) ∂E)
        = biasedSkeletonKernel γ β v {u}
          * ∫⁻ s, biasedSurvival γ β w r * F u x (t - r - s) ∂E := by
      intro r
      have hm : Measurable fun s => F u x (t - r - s) :=
        (hF u x).comp (measurable_const.sub measurable_id)
      rw [lintegral_const_mul _ hm]
      ring
    rw [lintegral_congr hpt, lintegral_const_mul _ (hK u)]
  calc biasedFirstStep γ β (biasedLastStep γ β F) v w t
      = ∑' u, biasedSkeletonKernel γ β v {u} * ∫⁻ s, biasedLastStep γ β F u w (t - s) ∂E := rfl
    _ = ∑' u, ∑' x, biasedSkeletonKernel γ β v {u} * (ENNReal.ofReal (biasedTotalRate γ β x)
          * biasedSkeletonKernel γ β x {w}
          * ∫⁻ s, ∫⁻ r, biasedSurvival γ β w r * F u x (t - s - r) ∂volume ∂E) :=
        tsum_congr fun u => by rw [hL u, ENNReal.tsum_mul_left]
    _ = ∑' x, ∑' u, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
          * (biasedSkeletonKernel γ β v {u}
            * ∫⁻ r, ∫⁻ s, biasedSurvival γ β w r * F u x (t - r - s) ∂E ∂volume) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun x => tsum_congr fun u => ?_
        rw [hswap u x]
        ring
    _ = biasedLastStep γ β (biasedFirstStep γ β F) v w t := by
        simp only [biasedLastStep]
        exact tsum_congr fun x => by rw [hR x, ENNReal.tsum_mul_left]

/-- **`𝓑` and `𝓛` agree on `P^{(0)}`**, by the reflection `r ↦ t - r`. -/
theorem biasedFirstStep_nJump_zero (γ β : ℝ) (v w : Profile N M) (t : ℝ) :
    biasedFirstStep γ β (fun u x s => biasedNJump γ β u x 0 s) v w t
      = biasedLastStep γ β (fun u x s => biasedNJump γ β u x 0 s) v w t := by
  classical
  have hL : biasedFirstStep γ β (fun u x s => biasedNJump γ β u x 0 s) v w t
      = biasedSkeletonKernel γ β v {w}
        * ∫⁻ s, biasedSurvival γ β w (t - s) ∂(expMeasure (biasedTotalRate γ β v)) := by
    simp only [biasedFirstStep, biasedNJump_zero]
    rw [tsum_eq_single w fun u hu => by simp [hu]]
    simp
  have hR : biasedLastStep γ β (fun u x s => biasedNJump γ β u x 0 s) v w t
      = ENNReal.ofReal (biasedTotalRate γ β v) * biasedSkeletonKernel γ β v {w}
          * ∫⁻ r, biasedSurvival γ β w r * biasedSurvival γ β v (t - r) := by
    simp only [biasedLastStep, biasedNJump_zero]
    rw [tsum_eq_single v fun x hx => by simp [Ne.symm hx]]
    simp
  have hreflect : ∫⁻ s, biasedSurvival γ β v s * biasedSurvival γ β w (t - s)
      = ∫⁻ r, biasedSurvival γ β w r * biasedSurvival γ β v (t - r) := by
    have h := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun r => biasedSurvival γ β w r * biasedSurvival γ β v (t - r)) t
    simp only [sub_sub_cancel] at h
    rw [← h]
    exact lintegral_congr fun s => mul_comm _ _
  have hf : Measurable fun s => biasedSurvival γ β w (t - s) :=
    (measurable_biasedSurvival γ β w).comp (measurable_const.sub measurable_id)
  rw [hL, hR, lintegral_expMeasure_biasedTotalRate γ β v hf, hreflect]
  ring

/-- **`P^{(n+1)} = 𝓛 P^{(n)}`**: the decomposition along the last expression before `t`. -/
theorem biasedNJump_succ_eq_lastStep (γ β : ℝ) (n : ℕ) :
    (fun (v w : Profile N M) t => biasedNJump γ β v w (n + 1) t)
      = biasedLastStep γ β (fun v w t => biasedNJump γ β v w n t) := by
  induction n with
  | zero =>
      funext v w t
      rw [biasedNJump_succ_eq_firstStep, biasedFirstStep_nJump_zero]
  | succ n ih =>
      funext v w t
      have hfirst : (fun (u x : Profile N M) s => biasedNJump γ β u x (n + 1) s)
          = biasedFirstStep γ β (fun u x s => biasedNJump γ β u x n s) := by
        funext u x s
        exact biasedNJump_succ_eq_firstStep γ β u x n s
      show biasedNJump γ β v w (n + 1 + 1) t
        = biasedLastStep γ β (fun u x s => biasedNJump γ β u x (n + 1) s) v w t
      rw [biasedNJump_succ_eq_firstStep, ih,
        biasedFirstStep_lastStep γ β (fun u x => measurable_biasedNJump γ β u x n), ← hfirst, ih]

end LastStep

/-! ### Starting from a measure -/

section Mix

/-- `∑_v μ (v) P^{(n)}_t (v, w)`. -/
noncomputable def biasedMixJump (γ β : ℝ) (μ : Measure (Profile N M)) (w : Profile N M)
    (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∑' v, μ {v} * biasedNJump γ β v w n t

theorem measurable_biasedMixJump (γ β : ℝ) (μ : Measure (Profile N M)) (w : Profile N M)
    (n : ℕ) : Measurable (biasedMixJump γ β μ w n) := by
  have h : biasedMixJump γ β μ w n
      = fun t => ⨆ s : Finset (Profile N M), ∑ v ∈ s, μ {v} * biasedNJump γ β v w n t := by
    funext t
    exact ENNReal.tsum_eq_iSup_sum
  rw [h]
  exact Measurable.iSup fun s =>
    Finset.measurable_sum s fun v _ => (measurable_biasedNJump γ β v w n).const_mul _

theorem biasedMixJump_zero (γ β : ℝ) (μ : Measure (Profile N M)) (w : Profile N M) (t : ℝ) :
    biasedMixJump γ β μ w 0 t = μ {w} * biasedSurvival γ β w t := by
  classical
  rw [biasedMixJump, tsum_eq_single w fun v hv => by rw [biasedNJump_zero, if_neg hv, mul_zero],
    biasedNJump_zero, if_pos rfl]

theorem biasedMixJump_succ (γ β : ℝ) (μ : Measure (Profile N M)) (w : Profile N M) (n : ℕ)
    (t : ℝ) :
    biasedMixJump γ β μ w (n + 1) t
      = ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
          * ∫⁻ r, biasedSurvival γ β w r * biasedMixJump γ β μ x n (t - r) := by
  have hpt : ∀ v, biasedNJump γ β v w (n + 1) t
      = ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
          * ∫⁻ r, biasedSurvival γ β w r * biasedNJump γ β v x n (t - r) :=
    fun v => congrFun (congrFun (congrFun (biasedNJump_succ_eq_lastStep γ β n) v) w) t
  have hinner : ∀ x, ∫⁻ r, biasedSurvival γ β w r * biasedMixJump γ β μ x n (t - r)
      = ∑' v, μ {v} * ∫⁻ r, biasedSurvival γ β w r * biasedNJump γ β v x n (t - r) := by
    intro x
    have hm : ∀ v, Measurable fun r => biasedSurvival γ β w r * biasedNJump γ β v x n (t - r) :=
      fun v => (measurable_biasedSurvival γ β w).mul
        ((measurable_biasedNJump γ β v x n).comp (measurable_const.sub measurable_id))
    simp only [biasedMixJump]
    simp_rw [← ENNReal.tsum_mul_left]
    have hm' : ∀ v, Measurable fun r =>
        biasedSurvival γ β w r * (μ {v} * biasedNJump γ β v x n (t - r)) :=
      fun v => (measurable_biasedSurvival γ β w).mul
        (((measurable_biasedNJump γ β v x n).comp
          (measurable_const.sub measurable_id)).const_mul _)
    rw [lintegral_tsum fun v => (hm' v).aemeasurable]
    refine tsum_congr fun v => ?_
    rw [← lintegral_const_mul _ (hm v)]
    exact lintegral_congr fun r => by ring
  calc biasedMixJump γ β μ w (n + 1) t
      = ∑' v, ∑' x, μ {v} * (ENNReal.ofReal (biasedTotalRate γ β x)
          * biasedSkeletonKernel γ β x {w}
          * ∫⁻ r, biasedSurvival γ β w r * biasedNJump γ β v x n (t - r)) :=
        tsum_congr fun v => by rw [hpt v, ENNReal.tsum_mul_left]
    _ = ∑' x, ∑' v, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
          * (μ {v} * ∫⁻ r, biasedSurvival γ β w r * biasedNJump γ β v x n (t - r)) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun x => tsum_congr fun v => by ring
    _ = ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
          * ∫⁻ r, biasedSurvival γ β w r * biasedMixJump γ β μ x n (t - r) :=
        tsum_congr fun x => by rw [hinner x, ENNReal.tsum_mul_left]

/-- **The induction on the number of expressions.** -/
theorem sum_biasedMixJump_le (γ β : ℝ) {μ : Measure (Profile N M)}
    (hinv : ∀ w, ∑' x, biasedSkeletonKernel γ β x {w}
        * (ENNReal.ofReal (biasedTotalRate γ β x) * μ {x})
      ≤ ENNReal.ofReal (biasedTotalRate γ β w) * μ {w}) (K : ℕ) :
    ∀ w t, ∑ n ∈ Finset.range K, biasedMixJump γ β μ w n t
      ≤ μ {w} * Set.indicator (Set.Ici 0) 1 t := by
  induction K with
  | zero => intro w t; simp
  | succ K ih =>
      intro w t
      set I : ℝ≥0∞ := ∫⁻ r, biasedSurvival γ β w r * Set.indicator (Set.Ici 0) 1 (t - r)
        with hI
      have hmix : ∀ x n, Measurable fun r =>
          biasedSurvival γ β w r * biasedMixJump γ β μ x n (t - r) :=
        fun x n => (measurable_biasedSurvival γ β w).mul
          ((measurable_biasedMixJump γ β μ x n).comp (measurable_const.sub measurable_id))
      have hswap : ∑ n ∈ Finset.range K, biasedMixJump γ β μ w (n + 1) t
          = ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
              * ∫⁻ r, biasedSurvival γ β w r
                  * ∑ n ∈ Finset.range K, biasedMixJump γ β μ x n (t - r) := by
        simp_rw [biasedMixJump_succ]
        rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine tsum_congr fun x => ?_
        rw [← Finset.mul_sum, ← lintegral_finsetSum _ fun n _ => hmix x n]
        simp_rw [Finset.mul_sum]
      have hstep : ∑ n ∈ Finset.range K, biasedMixJump γ β μ w (n + 1) t
          ≤ ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} * I := by
        rw [hswap]
        calc ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
              * ∫⁻ r, biasedSurvival γ β w r
                  * ∑ n ∈ Finset.range K, biasedMixJump γ β μ x n (t - r)
            ≤ ∑' x, ENNReal.ofReal (biasedTotalRate γ β x) * biasedSkeletonKernel γ β x {w}
              * ∫⁻ r, biasedSurvival γ β w r
                  * (μ {x} * Set.indicator (Set.Ici 0) 1 (t - r)) :=
              ENNReal.tsum_le_tsum fun x => by
                have h : ∫⁻ r, biasedSurvival γ β w r
                      * ∑ n ∈ Finset.range K, biasedMixJump γ β μ x n (t - r)
                    ≤ ∫⁻ r, biasedSurvival γ β w r
                      * (μ {x} * Set.indicator (Set.Ici 0) 1 (t - r)) :=
                  lintegral_mono fun r => by gcongr; exact ih x (t - r)
                gcongr
          _ = ∑' x, biasedSkeletonKernel γ β x {w}
                * (ENNReal.ofReal (biasedTotalRate γ β x) * μ {x}) * I := by
              refine tsum_congr fun x => ?_
              have hpt : ∀ r, biasedSurvival γ β w r
                    * (μ {x} * Set.indicator (Set.Ici 0) 1 (t - r))
                  = μ {x} * (biasedSurvival γ β w r * Set.indicator (Set.Ici 0) 1 (t - r)) :=
                fun r => by ring
              have hmI : Measurable fun r =>
                  biasedSurvival γ β w r
                    * Set.indicator (Set.Ici (0 : ℝ)) (1 : ℝ → ℝ≥0∞) (t - r) :=
                (measurable_biasedSurvival γ β w).mul
                  ((measurable_one.indicator measurableSet_Ici).comp
                    (measurable_const.sub measurable_id))
              rw [lintegral_congr hpt, lintegral_const_mul _ hmI]
              ring
          _ = (∑' x, biasedSkeletonKernel γ β x {w}
                * (ENNReal.ofReal (biasedTotalRate γ β x) * μ {x})) * I :=
              ENNReal.tsum_mul_right
          _ ≤ ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} * I := by gcongr; exact hinv w
      rw [Finset.sum_range_succ', biasedMixJump_zero]
      calc ∑ n ∈ Finset.range K, biasedMixJump γ β μ w (n + 1) t
            + μ {w} * biasedSurvival γ β w t
          ≤ ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} * I
            + μ {w} * biasedSurvival γ β w t :=
            add_le_add hstep le_rfl
        _ = μ {w} * (biasedSurvival γ β w t + ENNReal.ofReal (biasedTotalRate γ β w) * I) := by
            ring
        _ = μ {w} * Set.indicator (Set.Ici 0) 1 t := by rw [hI, biasedSurvival_add_lintegral]

end Mix

/-! ### The decomposition, from Theorem 25.1 -/

section Decomposition

omit [NeZero N] [NeZero M] in
/-- Below the explosion time the jump counter names the event the realisation lies in. -/
theorem mem_biasedNJumpSet_jumpCount (v : Profile N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) (hexp : explosionTime ω = ⊤) {t : ℝ} (ht : 0 ≤ t) :
    ω ∈ biasedNJumpSet v (biasedProcess v t ω) (jumpCount ω t) t := by
  have hb := bddAbove_of_explosionTime_eq_top hpos hexp t
  have hne : {n : ℕ | jumpTime n ω ≤ t}.Nonempty := ⟨0, by simpa using ht⟩
  refine ⟨Nat.sSup_mem hne hb, ?_, rfl⟩
  by_contra hle
  have : jumpCount ω t + 1 ≤ jumpCount ω t := le_csSup hb (not_lt.1 hle)
  omega

/-- **`P_t ≤ ∑_n P^{(n)}_t`.**  This is where Theorem 25.1 is used. -/
theorem biasedTransitionKernel_le_tsum_nJump (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 0 < γ) (hβ : 0 ≤ β) {v : Profile N M} (hv : IsBiasedState v) (w : Profile N M)
    {t : ℝ} (ht : 0 ≤ t) :
    biasedTransitionKernel γ β t v {w} ≤ ∑' n, biasedNJump γ β v w n t := by
  set A : Set (ℕ → Step N M) := {ω | ∀ n, 0 < holdingTime n ω}ᶜ with hAdef
  set B : Set (ℕ → Step N M) := {ω | explosionTime ω = ⊤}ᶜ with hBdef
  have hA : biasedCtsPathMeasure γ β v A = 0 := biasedCtsPathMeasure_holdingTime_pos_compl γ β v
  have hB : biasedCtsPathMeasure γ β v B = 0 :=
    (prob_compl_eq_zero_iff (measurable_explosionTime (measurableSet_singleton ⊤))).2
      (biasedNonExplosion_of_pos hM hN hγ hβ hv)
  have hsub : biasedProcess v t ⁻¹' {w}
      ⊆ (⋃ n, biasedNJumpSet v w n t) ∪ (A ∪ B) := by
    intro ω hω
    by_cases hpos : ∀ n, 0 < holdingTime n ω
    · by_cases hexp : explosionTime ω = ⊤
      · left
        refine Set.mem_iUnion.2 ⟨jumpCount ω t, ?_⟩
        have h := mem_biasedNJumpSet_jumpCount v hpos hexp ht
        rwa [show biasedProcess v t ω = w from hω] at h
      · exact Or.inr (Or.inr hexp)
    · exact Or.inr (Or.inl hpos)
  rw [biasedTransitionKernel_apply,
    Measure.map_apply (measurable_biasedProcess v t) (measurableSet_singleton w)]
  calc biasedCtsPathMeasure γ β v (biasedProcess v t ⁻¹' {w})
      ≤ biasedCtsPathMeasure γ β v ((⋃ n, biasedNJumpSet v w n t) ∪ (A ∪ B)) :=
        measure_mono hsub
    _ ≤ biasedCtsPathMeasure γ β v (⋃ n, biasedNJumpSet v w n t)
          + (biasedCtsPathMeasure γ β v A + biasedCtsPathMeasure γ β v B) :=
        le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_union_le _ _))
    _ = biasedCtsPathMeasure γ β v (⋃ n, biasedNJumpSet v w n t) := by
        rw [hA, hB, add_zero, add_zero]
    _ ≤ ∑' n, biasedNJump γ β v w n t := measure_iUnion_le _

end Decomposition

/-! ### The converse, and Theorem 25.2 -/

section Existence

/-- **The converse of `SocialNetwork.Bias.invariant_biasedRateMeasure`.**  If the biased
skeleton sends `q · μ` below itself, then `μ` is invariant for the biased process.  It uses
Theorem 25.1. -/
theorem biasedInvariantCts_of_bind_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hβ : 0 ≤ β) {μ : Measure (Profile N M)} [IsProbabilityMeasure μ]
    (hμS : IsCarriedByBiasedState μ)
    (hle : (biasedRateMeasure γ β μ).bind (biasedSkeletonKernel γ β) ≤ biasedRateMeasure γ β μ) :
    IsBiasedInvariantCts γ β μ := by
  have hinv : ∀ w, ∑' x, biasedSkeletonKernel γ β x {w}
        * (ENNReal.ofReal (biasedTotalRate γ β x) * μ {x})
      ≤ ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} := by
    intro w
    simpa only [bind_apply_singleton, biasedRateMeasure_singleton] using
      Measure.le_iff'.1 hle {w}
  intro t ht
  have hbound : ∀ w, (μ.bind (biasedTransitionKernel γ β t)) {w} ≤ μ {w} := by
    intro w
    rw [bind_apply_singleton]
    have hterm : ∀ v, biasedTransitionKernel γ β t v {w} * μ {v}
        ≤ μ {v} * ∑' n, biasedNJump γ β v w n t := by
      intro v
      by_cases hv : IsBiasedState v
      · rw [mul_comm]
        gcongr
        exact biasedTransitionKernel_le_tsum_nJump hM hN hγ hβ hv w ht
      · have hzero : μ {v} = 0 := measure_mono_null (Set.singleton_subset_iff.2 hv) hμS
        simp [hzero]
    calc ∑' v, biasedTransitionKernel γ β t v {w} * μ {v}
        ≤ ∑' v, μ {v} * ∑' n, biasedNJump γ β v w n t := ENNReal.tsum_le_tsum hterm
      _ = ∑' n, biasedMixJump γ β μ w n t := by
          simp_rw [← ENNReal.tsum_mul_left]
          exact ENNReal.tsum_comm
      _ = ⨆ K, ∑ n ∈ Finset.range K, biasedMixJump γ β μ w n t := ENNReal.tsum_eq_iSup_nat
      _ ≤ μ {w} * Set.indicator (Set.Ici 0) 1 t :=
          iSup_le fun K => sum_biasedMixJump_le γ β hinv K w t
      _ = μ {w} := by rw [Set.indicator_of_mem (Set.mem_Ici.2 ht), Pi.one_apply, mul_one]
  have huniv : (μ.bind (biasedTransitionKernel γ β t)) Set.univ = μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp
  exact eq_of_le_of_univ_eq (le_of_forall_singleton_le hbound) huniv (measure_ne_top μ _)

/-- **The correspondence of p. 18 for the biased process**, in both directions: a probability
measure carried by `S^α` is invariant for the biased process exactly when its product with the
jump rate is invariant for the biased skeleton. -/
theorem isBiasedInvariantCts_iff (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {μ : Measure (Profile N M)}
    [IsProbabilityMeasure μ] (hμS : IsCarriedByBiasedState μ) :
    IsBiasedInvariantCts γ β μ ↔ IsBiasedInvariant γ β (biasedRateMeasure γ β μ) :=
  ⟨invariant_biasedRateMeasure hM hN hγ hγ' hβ hμS,
    fun h => biasedInvariantCts_of_bind_le hM hN hγ hβ hμS (le_of_eq h)⟩

/-- The right-hand side of equation (13), as a measure: `μ̃ / q`, normalised. -/
noncomputable def biasedCtsOfSkeleton (γ β : ℝ) (μ : Measure (Profile N M)) :
    Measure (Profile N M) :=
  (∑' v, μ {v} / ENNReal.ofReal (biasedTotalRate γ β v))⁻¹
    • μ.withDensity fun v => (ENNReal.ofReal (biasedTotalRate γ β v))⁻¹

omit [NeZero N] [NeZero M] in
theorem biasedCtsOfSkeleton_singleton (γ β : ℝ) (μ : Measure (Profile N M)) (w : Profile N M) :
    biasedCtsOfSkeleton γ β μ {w}
      = (∑' v, μ {v} / ENNReal.ofReal (biasedTotalRate γ β v))⁻¹
          * (μ {w} / ENNReal.ofReal (biasedTotalRate γ β w)) := by
  rw [biasedCtsOfSkeleton, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton w), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, div_eq_mul_inv]

/-- **Existence for Theorem 25.2.**  The right-hand side of equation (13) is an invariant
probability measure of the biased process, carried by `S^α`. -/
theorem biasedCtsOfSkeleton_spec (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hβ : 0 ≤ β) {μskel : Measure (Profile N M)} [IsProbabilityMeasure μskel]
    (hsS : IsCarriedByBiasedState μskel) (hsinv : IsBiasedInvariant γ β μskel) :
    IsProbabilityMeasure (biasedCtsOfSkeleton γ β μskel)
      ∧ IsCarriedByBiasedState (biasedCtsOfSkeleton γ β μskel)
      ∧ IsBiasedInvariantCts γ β (biasedCtsOfSkeleton γ β μskel) := by
  set Z := ∑' v, μskel {v} / ENNReal.ofReal (biasedTotalRate γ β v) with hZ
  have hq0 : ∀ w : Profile N M, ENNReal.ofReal (biasedTotalRate γ β w) ≠ 0 :=
    fun w => (ENNReal.ofReal_pos.2 (biasedTotalRate_pos γ β w)).ne'
  have hZtop : Z ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_div_biasedTotalRate_le γ β μskel hsS)
    exact ENNReal.div_ne_top ENNReal.one_ne_top (by exact_mod_cast NeZero.ne M)
  have hZ0 : Z ≠ 0 := by
    intro h0
    have hall : ∀ w : Profile N M, μskel {w} = 0 := by
      intro w
      have hle : μskel {w} / ENNReal.ofReal (biasedTotalRate γ β w) ≤ Z :=
        ENNReal.le_tsum (f := fun v => μskel {v} / ENNReal.ofReal (biasedTotalRate γ β v)) w
      rw [h0, le_zero_iff, ENNReal.div_eq_zero_iff] at hle
      exact hle.resolve_right ENNReal.ofReal_ne_top
    have hone := tsum_measure_singleton μskel
    rw [tsum_congr hall] at hone
    simp at hone
  have hsing : ∀ w, biasedCtsOfSkeleton γ β μskel {w}
      = Z⁻¹ * (μskel {w} / ENNReal.ofReal (biasedTotalRate γ β w)) :=
    biasedCtsOfSkeleton_singleton γ β μskel
  have hprob : IsProbabilityMeasure (biasedCtsOfSkeleton γ β μskel) := by
    refine ⟨?_⟩
    have h := lintegral_countable' (μ := biasedCtsOfSkeleton γ β μskel) (fun _ => (1 : ℝ≥0∞))
    simp only [lintegral_const, one_mul] at h
    rw [h, tsum_congr hsing, ENNReal.tsum_mul_left, ← hZ, ENNReal.inv_mul_cancel hZ0 hZtop]
  have hS : IsCarriedByBiasedState (biasedCtsOfSkeleton γ β μskel) := by
    show biasedCtsOfSkeleton γ β μskel (biasedStateSet N M)ᶜ = 0
    rw [biasedCtsOfSkeleton, Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ (measurableSet_profile _), Measure.restrict_eq_zero.2 hsS,
      lintegral_zero_measure, mul_zero]
  refine ⟨hprob, hS, biasedInvariantCts_of_bind_le hM hN hγ hβ hS ?_⟩
  -- `q · (μ̃ / q) / Z = μ̃ / Z`, which the skeleton keeps
  have hrate : ∀ w, biasedRateMeasure γ β (biasedCtsOfSkeleton γ β μskel) {w}
      = Z⁻¹ * μskel {w} := by
    intro w
    rw [biasedRateMeasure_singleton, hsing, div_eq_mul_inv, ← mul_assoc, mul_comm _ Z⁻¹,
      mul_assoc, mul_comm (μskel {w}), ← mul_assoc (ENNReal.ofReal _),
      ENNReal.mul_inv_cancel (hq0 w) ENNReal.ofReal_ne_top, one_mul]
  refine le_of_forall_singleton_le fun w => le_of_eq ?_
  rw [bind_apply_singleton]
  simp only [hrate]
  have hfix : ∑' x, biasedSkeletonKernel γ β x {w} * μskel {x} = μskel {w} := by
    rw [← bind_apply_singleton, hsinv]
  calc ∑' x, biasedSkeletonKernel γ β x {w} * (Z⁻¹ * μskel {x})
      = Z⁻¹ * ∑' x, biasedSkeletonKernel γ β x {w} * μskel {x} := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by ring
    _ = Z⁻¹ * μskel {w} := by rw [hfix]

/-- **Theorem 25.2.**  For `β > 0` and `0 < α < 1/(M-1)`, the biased process has a unique
invariant probability measure `μ_{β,α}` carried by `S^α`.

**Follows the paper's proof**, which is "exactly the proof of Theorem 1": the biased skeleton
has a unique invariant measure (`SocialNetwork.Bias.existsUnique_biasedInvariant`), and the
correspondence of p. 18 (`SocialNetwork.Bias.isBiasedInvariantCts_iff`) transfers it, the
existence half through Theorem 25.1. -/
theorem existsUnique_biasedInvariantCts (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β) :
    ∃! μ : Measure (Profile N M),
      IsProbabilityMeasure μ ∧ IsCarriedByBiasedState μ ∧ IsBiasedInvariantCts γ β μ := by
  obtain ⟨μskel, ⟨hsprob, hsS, hsinv⟩, -⟩ := existsUnique_biasedInvariant hM hN hγ hγ' hβ
  refine ⟨biasedCtsOfSkeleton γ β μskel, biasedCtsOfSkeleton_spec hM hN hγ hβ.le hsS hsinv, ?_⟩
  rintro ν ⟨hν, hνS, hνinv⟩
  obtain ⟨hprob, hS, hinv⟩ := biasedCtsOfSkeleton_spec hM hN hγ hβ.le hsS hsinv
  exact eq_of_biasedInvariantCts hM hN hγ hγ' hβ hν hνS hνinv hprob hS hinv

end Existence

end Bias

end SocialNetwork
