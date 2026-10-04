/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedConsensusExit
import SocialNetwork.Transfer

/-!
# Equation (13) for the biased process

Theorem 25 of arXiv:2607.19651 says that the biased process has a unique invariant probability
measure `μ_{α,β}`, and that its proof "follows exactly as the proof of Theorem 1".  The proof
of Theorem 1.2 goes through equation (13), which writes the invariant measure of the process in
terms of that of the skeleton, `μ = (μ̃ / q) / ∑ μ̃ / q`, and Theorem 27.1 is proved through the
same display.  This file transposes `SocialNetwork.Transfer`, which proves (13) for the
unbiased process, to the biased one.

The argument is unchanged, and so is its shape: a lower bound on `P_t` read off the first two
holding times, which gives `νK ≤ ν` for `ν = q · μ`; the minorisation of the biased skeleton
(`SocialNetwork.Bias.minorisation_iterateKernel`), which makes `ν` finite and turns the
inequality into an equality; and the uniqueness of the skeleton's invariant measure, which
identifies `ν` normalised with `μ̃_{α,β}`.  What changes is the state: the memory profile of
`SocialNetwork.BiasedModel` in place of the matrix, `SocialNetwork.Bias.stateAfter` in place of
`SocialNetwork.Trajectory.state`, and the rate `e^{β u(a, o)}` of equation (7).  The lemmas of
`SocialNetwork.Transfer` that know nothing about either model — the jump counter, the measures
on a countable space — are used as they stand.

Like the unbiased one, the argument does not use non-explosion: both events it reads are
decided by the first two holding times.

## Main definitions

* `SocialNetwork.Bias.biasedTransitionKernel` — the semigroup `P_t` of the biased process.
* `SocialNetwork.Bias.IsBiasedInvariantCts` — invariance for the biased process.
* `SocialNetwork.Bias.biasedRateMeasure` — `q · μ`.

## Main statements

* `SocialNetwork.Bias.le_biasedTransitionKernel_singleton` — the lower bound on `P_t`.
* `SocialNetwork.Bias.invariant_biasedRateMeasure` — `q · μ` is invariant for the biased
  skeleton: the half of the correspondence of p. 18 that equation (13) needs.
* `SocialNetwork.Bias.biasedInvariantCts_eq` — **equation (13)** for the biased process.
* `SocialNetwork.Bias.eq_of_biasedInvariantCts` — **Theorem 25.2, the uniqueness half**.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

namespace Bias

variable {N M : ℕ}

/-! ### The semigroup, and invariance -/

section Semigroup

/-- The biased process is a measurable function of the realisation: the jump counter is, and
the profile after a fixed number of expressions is. -/
theorem measurable_biasedProcess (u : Profile N M) (t : ℝ) :
    Measurable (biasedProcess (N := N) (M := M) u t) := by
  have hpair : Measurable
      fun p : ℕ × (ℕ → Step N M) => stateAfter u (fun n => (p.2 n).1) p.1 :=
    measurable_from_prod_countable_right fun k => measurable_stateAfter_ofStepPath u k
  have h : biasedProcess (N := N) (M := M) u t
      = (fun p : ℕ × (ℕ → Step N M) => stateAfter u (fun n => (p.2 n).1) p.1) ∘
        fun ω : ℕ → Step N M => (jumpCount ω t, ω) := rfl
  rw [h]
  exact hpair.comp ((measurable_jumpCount t).prodMk measurable_id)

variable [NeZero N] [NeZero M]

/-- The transition semigroup `P_t (P, ·)` of the biased process: the law of `U_t^{α,β,P}`. -/
noncomputable def biasedTransitionKernel (γ β t : ℝ) : Kernel (Profile N M) (Profile N M) :=
  Kernel.ofFunOfCountable fun P => (biasedCtsPathMeasure γ β P).map (biasedProcess P t)

theorem biasedTransitionKernel_apply (γ β t : ℝ) (P : Profile N M) :
    biasedTransitionKernel γ β t P = (biasedCtsPathMeasure γ β P).map (biasedProcess P t) := rfl

instance isMarkovKernel_biasedTransitionKernel (γ β t : ℝ) :
    IsMarkovKernel (biasedTransitionKernel (N := N) (M := M) γ β t) := by
  refine ⟨fun P => ?_⟩
  rw [biasedTransitionKernel_apply]
  exact Measure.isProbabilityMeasure_map (measurable_biasedProcess P t).aemeasurable

/-- Invariance for the biased process in continuous time: invariance under every `P_t`,
`t ≥ 0`.  The paper's `μ_{α,β}` of Theorem 25 is the invariant probability measure in this
sense, and `SocialNetwork.Bias.IsBiasedInvariant` is invariance for the skeleton. -/
def IsBiasedInvariantCts (γ β : ℝ) (μ : Measure (Profile N M)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → Kernel.Invariant (biasedTransitionKernel γ β t) μ

end Semigroup

/-! ### Reading the biased process off the first two holding times

With no jump by time `t` the process is where it started
(`SocialNetwork.Bias.biasedProcess_eq_of_lt_holdingTime`); with exactly one, it is where the
first expression took it. -/

section Counter

/-- **Exactly one jump by time `t`.**  The process sits at the profile that the first expressed
pair reaches. -/
theorem biasedProcess_eq_of_one_jump (v : Profile N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) {t : ℝ} (h0 : holdingTime 0 ω ≤ t)
    (h1 : t < holdingTime 0 ω + holdingTime 1 ω) :
    biasedProcess v t ω = Profile.express (ω 0).1.1 (ω 0).1.2 v := by
  have hcount : jumpCount ω t = 1 := by
    refine (jumpCount_eq_iff t ω one_ne_zero).2 ⟨by rwa [jumpTime_one], fun m hm => ?_⟩
    by_contra hlt
    have h2 : 2 ≤ m := by omega
    have hle : jumpTime 2 ω ≤ jumpTime m ω := jumpTime_mono hpos h2
    rw [jumpTime_two] at hle
    exact absurd (le_trans hle hm) (not_le.2 h1)
  show stateAfter v (fun n => (ω n).1) (jumpCount ω t) = _
  rw [hcount, stateAfter_succ, stateAfter_zero]

end Counter

/-! ### The transition kernel from below -/

section Bound

variable [NeZero N] [NeZero M]

/-- One step of the biased skeleton, read as a mass on pairs. -/
theorem biasedSkeletonKernel_singleton (γ β : ℝ) (v w : Profile N M) :
    biasedSkeletonKernel γ β v {w}
      = (biasedJumpPMF γ β v).toMeasure {p : Jump N M | Profile.express p.1 p.2 v = w} := by
  rw [biasedSkeletonKernel_apply,
    PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (measurableSet_profile _)]
  rfl

/-- The realisations whose first expression takes `v` to `w` and has happened by time `t`,
with the second not yet. -/
def biasedOneJumpSet (v w : Profile N M) (t : ℝ) : Set (ℕ → Step N M) :=
  {ω | holdingTime 0 ω ≤ t ∧ Profile.express (ω 0).1.1 (ω 0).1.2 v = w ∧
    t < holdingTime 0 ω + holdingTime 1 ω}

/-- The same event, read on the first step and the rest of the realisation separately. -/
def biasedOneJumpPairs (v w : Profile N M) (t : ℝ) : Set (Step N M × (ℕ → Step N M)) :=
  {x | x.1.2 ≤ t ∧ Profile.express x.1.1.1 x.1.1.2 v = w ∧ t < x.1.2 + holdingTime 0 x.2}

omit [NeZero N] [NeZero M] in
theorem biasedOneJumpSet_eq_preimage (v w : Profile N M) (t : ℝ) :
    biasedOneJumpSet v w t = {ω | (ω 0, shiftStepPath ω) ∈ biasedOneJumpPairs v w t} := by
  rfl

omit [NeZero N] [NeZero M] in
theorem measurableSet_biasedOneJumpPairs (v w : Profile N M) (t : ℝ) :
    MeasurableSet (biasedOneJumpPairs v w t) := by
  have h1 : Measurable fun x : Step N M × (ℕ → Step N M) => x.1.2 :=
    measurable_snd.comp measurable_fst
  have h2 : Measurable fun x : Step N M × (ℕ → Step N M) => x.1.1 :=
    measurable_fst.comp measurable_fst
  have h3 : Measurable fun x : Step N M × (ℕ → Step N M) => holdingTime 0 x.2 :=
    (measurable_holdingTime 0).comp measurable_snd
  have h4 : Measurable fun x : Step N M × (ℕ → Step N M) => x.1.2 + holdingTime 0 x.2 :=
    h1.add h3
  have hset : biasedOneJumpPairs v w t
      = ((fun x : Step N M × (ℕ → Step N M) => x.1.2) ⁻¹' Set.Iic t)
        ∩ (((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹'
              {p : Jump N M | Profile.express p.1 p.2 v = w})
          ∩ ((fun x : Step N M × (ℕ → Step N M) => x.1.2 + holdingTime 0 x.2) ⁻¹'
              Set.Ioi t)) := rfl
  rw [hset]
  exact (h1 measurableSet_Iic).inter
    ((h2 (DiscreteMeasurableSpace.forall_measurableSet _)).inter (h4 measurableSet_Ioi))

/-- **Exactly one jump, from below**: `K (v, w) e^{-q(w)t} (1 - e^{-q(v)t})`. -/
theorem le_biasedCtsPathMeasure_oneJumpSet (γ β : ℝ) (v w : Profile N M) {t : ℝ}
    (ht : 0 ≤ t) :
    biasedSkeletonKernel γ β v {w} * ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t)))
        * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t)))
      ≤ biasedCtsPathMeasure γ β v (biasedOneJumpSet v w t) := by
  set P : Set (Jump N M) := {p : Jump N M | Profile.express p.1 p.2 v = w} with hP
  set R : Set (Step N M) := P ×ˢ Set.Icc 0 t with hR
  have hRmeas : MeasurableSet R :=
    (DiscreteMeasurableSpace.forall_measurableSet P).prod measurableSet_Icc
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t))) with hc
  have hstep : biasedStepLaw γ β v R
      = (biasedJumpPMF γ β v).toMeasure P
        * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t))) := by
    have : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β v)) :=
      isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β v)
    rw [hR, biasedStepLaw, Measure.prod_prod,
      expMeasure_Icc_zero (biasedTotalRate_pos γ β v) ht]
  have hpt : ∀ z : Step N M, Set.indicator R (fun _ => c) z
      ≤ biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 v)
          {ω' | (z, ω') ∈ biasedOneJumpPairs v w t} := by
    intro z
    by_cases hz : z ∈ R
    · obtain ⟨hzP, hz0, hzt⟩ : z.1 ∈ P ∧ 0 ≤ z.2 ∧ z.2 ≤ t := ⟨hz.1, hz.2.1, hz.2.2⟩
      have hexp : Profile.express z.1.1 z.1.2 v = w := hzP
      have hslice : {ω' : ℕ → Step N M | (z, ω') ∈ biasedOneJumpPairs v w t}
          = {ω' | t - z.2 < holdingTime 0 ω'} := by
        ext ω'
        simp only [biasedOneJumpPairs, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨-, -, h⟩; linarith
        · intro h; exact ⟨hzt, hexp, by linarith⟩
      rw [Set.indicator_of_mem hz, hslice, hexp,
        biasedCtsPathMeasure_lt_holdingTime γ β w (by linarith)]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have := biasedTotalRate_pos γ β w
      nlinarith
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  calc biasedSkeletonKernel γ β v {w} * c
        * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t)))
      = c * biasedStepLaw γ β v R := by
        rw [hstep, biasedSkeletonKernel_singleton]
        ring
    _ = ∫⁻ z, Set.indicator R (fun _ => c) z ∂(biasedStepLaw γ β v) :=
        (lintegral_indicator_const hRmeas c).symm
    _ ≤ ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 v)
          {ω' | (z, ω') ∈ biasedOneJumpPairs v w t} ∂(biasedStepLaw γ β v) :=
        lintegral_mono hpt
    _ = biasedCtsPathMeasure γ β v (biasedOneJumpSet v w t) := by
        rw [biasedOneJumpSet_eq_preimage,
          biasedCtsPathMeasure_firstStep_apply γ β v (measurableSet_biasedOneJumpPairs v w t)]

open Classical in
/-- **The transition kernel from below.**  By time `t` either nothing has happened, or exactly
one expression has and it took `v` to `w`; the two events are disjoint. -/
theorem le_biasedTransitionKernel_singleton (γ β : ℝ) (v w : Profile N M) {t : ℝ}
    (ht : 0 ≤ t) :
    (if v = w then ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β v * t))) else 0)
        + biasedSkeletonKernel γ β v {w}
          * ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t)))
          * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t)))
      ≤ biasedTransitionKernel γ β t v {w} := by
  classical
  set G : Set (ℕ → Step N M) := {ω | ∀ n, 0 < holdingTime n ω} with hGdef
  have hGmeas : MeasurableSet G := by
    rw [hGdef, show {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}
        = ⋂ n, {ω | 0 < holdingTime n ω} from by ext ω; simp]
    exact MeasurableSet.iInter fun n => (measurable_holdingTime n) measurableSet_Ioi
  have hGnull : biasedCtsPathMeasure γ β v Gᶜ = 0 :=
    biasedCtsPathMeasure_holdingTime_pos_compl γ β v
  have hconull : ∀ S : Set (ℕ → Step N M),
      biasedCtsPathMeasure γ β v (S ∩ G) = biasedCtsPathMeasure γ β v S := by
    intro S
    have h := measure_inter_add_sdiff (μ := biasedCtsPathMeasure γ β v) S hGmeas
    rwa [measure_mono_null (Set.sdiff_subset_compl S G) hGnull, add_zero] at h
  have hpre : biasedTransitionKernel γ β t v {w}
      = biasedCtsPathMeasure γ β v (biasedProcess v t ⁻¹' {w}) := by
    rw [biasedTransitionKernel_apply,
      Measure.map_apply (measurable_biasedProcess v t) (measurableSet_profile _)]
  have hBsub : biasedOneJumpSet v w t ∩ G ⊆ biasedProcess v t ⁻¹' {w} := by
    rintro ω ⟨⟨h0, hexp, h1⟩, hG⟩
    show biasedProcess v t ω = w
    rw [biasedProcess_eq_of_one_jump v hG h0 h1]
    exact hexp
  have hmeasB : MeasurableSet (biasedOneJumpSet v w t ∩ G) := by
    rw [biasedOneJumpSet_eq_preimage]
    exact (((measurable_pi_apply 0).prodMk measurable_shiftStepPath)
      (measurableSet_biasedOneJumpPairs v w t)).inter hGmeas
  have hBle : biasedCtsPathMeasure γ β v (biasedOneJumpSet v w t)
      ≤ biasedTransitionKernel γ β t v {w} := by
    rw [hpre, ← hconull (biasedOneJumpSet v w t)]
    exact measure_mono hBsub
  by_cases hvw : v = w
  · subst hvw
    have hdisj : Disjoint ({ω : ℕ → Step N M | t < holdingTime 0 ω} ∩ G)
        (biasedOneJumpSet v v t ∩ G) := by
      rw [Set.disjoint_left]
      rintro ω ⟨hA, -⟩ ⟨⟨h0, -, -⟩, -⟩
      exact absurd h0 (not_le.2 hA)
    have hunion : ({ω : ℕ → Step N M | t < holdingTime 0 ω} ∩ G)
        ∪ (biasedOneJumpSet v v t ∩ G) ⊆ biasedProcess v t ⁻¹' {v} := by
      refine Set.union_subset (fun ω hω => ?_) hBsub
      show biasedProcess v t ω = v
      exact biasedProcess_eq_of_lt_holdingTime v hω.2 ht hω.1
    rw [if_pos rfl, hpre]
    refine le_trans (add_le_add le_rfl (le_biasedCtsPathMeasure_oneJumpSet γ β v v ht)) ?_
    rw [← biasedCtsPathMeasure_lt_holdingTime γ β v ht,
      ← hconull {ω | t < holdingTime 0 ω}, ← hconull (biasedOneJumpSet v v t),
      ← measure_union hdisj hmeasB]
    exact measure_mono hunion
  · rw [if_neg hvw, zero_add]
    exact le_trans (le_biasedCtsPathMeasure_oneJumpSet γ β v w ht) hBle

end Bound

/-! ### From the process to the skeleton -/

section Transfer

variable [NeZero N] [NeZero M]

/-- **The invariance equation, truncated**: only the paths with no jump, or exactly one and
into `w`, and only finitely many starting profiles. -/
theorem finsetSum_le_of_biasedInvariantCts (γ β : ℝ) {μ : Measure (Profile N M)}
    (hμ : IsBiasedInvariantCts γ β μ) (w : Profile N M) (F : Finset (Profile N M)) {t : ℝ}
    (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t))) * μ {w}
        + ∑ v ∈ F, biasedSkeletonKernel γ β v {w}
            * ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t)))
            * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t))) * μ {v}
      ≤ μ {w} := by
  classical
  have hterm : ∀ v : Profile N M,
      (if v = w then ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β v * t))) else 0) * μ {v}
          + biasedSkeletonKernel γ β v {w}
            * ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t)))
            * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t))) * μ {v}
        ≤ biasedTransitionKernel γ β t v {w} * μ {v} := by
    intro v
    rw [← add_mul]
    exact mul_le_mul_left (le_biasedTransitionKernel_singleton γ β v w ht) _
  have hfirst : ∑' v : Profile N M,
      (if v = w then ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β v * t))) else 0) * μ {v}
        = ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β w * t))) * μ {w} := by
    refine tsum_eq_single w (fun v hv => by rw [if_neg hv, zero_mul]) |>.trans ?_
    rw [if_pos rfl]
  conv_rhs => rw [measure_singleton_of_invariant (biasedTransitionKernel γ β t) (hμ t ht) w]
  refine le_trans ?_ (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_add, hfirst]
  exact add_le_add le_rfl (ENNReal.sum_le_tsum F)

/-- **`νK ≤ ν` at one point**, for `ν = q · μ` with `μ` invariant for the biased process. -/
theorem finsetSum_biasedRate_le (γ β : ℝ) {μ : Measure (Profile N M)} [IsProbabilityMeasure μ]
    (hμ : IsBiasedInvariantCts γ β μ) (w : Profile N M) (F : Finset (Profile N M)) :
    ∑ v ∈ F, ENNReal.ofReal (biasedTotalRate γ β v) * biasedSkeletonKernel γ β v {w} * μ {v}
      ≤ ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} := by
  classical
  set a : ℝ := biasedTotalRate γ β w with ha
  set ρ : ℝ := ∑ u ∈ F, biasedTotalRate γ β u with hρ
  set m : Profile N M → ℝ := fun v => (μ {v}).toReal with hm
  set k : Profile N M → ℝ := fun v => (biasedSkeletonKernel γ β v {w}).toReal with hk
  set S₀ : ℝ := ∑ v ∈ F, biasedTotalRate γ β v * k v * m v with hS₀
  have hmnn : ∀ v, 0 ≤ m v := fun v => ENNReal.toReal_nonneg
  have hknn : ∀ v, 0 ≤ k v := fun v => ENNReal.toReal_nonneg
  have hρle : ∀ v ∈ F, biasedTotalRate γ β v ≤ ρ := by
    intro v hv
    rw [hρ]
    exact Finset.single_le_sum (fun u _ => (biasedTotalRate_pos γ β u).le) hv
  -- the real form of the truncated invariance equation
  have hreal : ∀ t : ℝ, 0 ≤ t →
      Real.exp (-(a * t)) * m w
          + ∑ v ∈ F, k v * Real.exp (-(a * t))
              * (1 - Real.exp (-(biasedTotalRate γ β v * t))) * m v
        ≤ m w := by
    intro t ht
    have h := finsetSum_le_of_biasedInvariantCts γ β hμ w F ht
    have hfin : ∀ v : Profile N M, biasedSkeletonKernel γ β v {w}
        * ENNReal.ofReal (Real.exp (-(a * t)))
        * ENNReal.ofReal (1 - Real.exp (-(biasedTotalRate γ β v * t))) * μ {v} ≠ ∞ := by
      intro v
      refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_) ?_ <;>
        simp [measure_ne_top]
    have hle := (ENNReal.toReal_le_toReal
      (by
        refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (measure_ne_top _ _), ?_⟩
        exact (ENNReal.sum_ne_top).2 fun v _ => hfin v)
      (measure_ne_top μ {w})).2 h
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
      ((ENNReal.sum_ne_top).2 fun v _ => hfin v),
      ENNReal.toReal_sum fun v _ => hfin v] at hle
    refine le_trans (le_of_eq ?_) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (by
        have : Real.exp (-(biasedTotalRate γ β v * t)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [biasedTotalRate_pos γ β v])
        linarith)]
  -- divide by `t` and read off the rates
  have key : ∀ t : ℝ, 0 < t → Real.exp (-((a + ρ) * t)) * S₀ ≤ a * m w := by
    intro t ht
    have h := hreal t ht.le
    have hupper : ∑ v ∈ F,
        k v * Real.exp (-(a * t)) * (1 - Real.exp (-(biasedTotalRate γ β v * t))) * m v
          ≤ m w * (a * t) := by
      have h1 : 1 - Real.exp (-(a * t)) ≤ a * t := one_sub_exp_neg_le _
      nlinarith [hmnn w]
    have hlower : Real.exp (-((a + ρ) * t)) * S₀ * t
        ≤ ∑ v ∈ F, k v * Real.exp (-(a * t))
            * (1 - Real.exp (-(biasedTotalRate γ β v * t))) * m v := by
      rw [hS₀, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v hv => ?_
      have hrv : (0 : ℝ) < biasedTotalRate γ β v := biasedTotalRate_pos γ β v
      have hexp : Real.exp (-(ρ * t)) ≤ Real.exp (-(biasedTotalRate γ β v * t)) :=
        Real.exp_le_exp.2 (by nlinarith [hρle v hv])
      have hstep : biasedTotalRate γ β v * t * Real.exp (-(biasedTotalRate γ β v * t))
          ≤ 1 - Real.exp (-(biasedTotalRate γ β v * t)) := by
        have := mul_exp_neg_le_one_sub_exp_neg (biasedTotalRate γ β v * t)
        simpa using this
      have hsplit : Real.exp (-((a + ρ) * t))
          = Real.exp (-(a * t)) * Real.exp (-(ρ * t)) := by
        rw [← Real.exp_add]; ring_nf
      have hkm : 0 ≤ k v * m v := mul_nonneg (hknn v) (hmnn v)
      have hpe : (0 : ℝ) < Real.exp (-(a * t)) := Real.exp_pos _
      have hinner : biasedTotalRate γ β v * t * Real.exp (-(ρ * t))
          ≤ 1 - Real.exp (-(biasedTotalRate γ β v * t)) := by
        have h1 : biasedTotalRate γ β v * t * Real.exp (-(ρ * t))
            ≤ biasedTotalRate γ β v * t * Real.exp (-(biasedTotalRate γ β v * t)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hrv.le ht.le)
        linarith [hstep]
      have hfac : 0 ≤ Real.exp (-(a * t)) * (k v * m v) := mul_nonneg hpe.le hkm
      rw [hsplit]
      calc Real.exp (-(a * t)) * Real.exp (-(ρ * t)) * (biasedTotalRate γ β v * k v * m v) * t
          = Real.exp (-(a * t)) * (k v * m v)
              * (biasedTotalRate γ β v * t * Real.exp (-(ρ * t))) := by ring
        _ ≤ Real.exp (-(a * t)) * (k v * m v)
              * (1 - Real.exp (-(biasedTotalRate γ β v * t))) :=
            mul_le_mul_of_nonneg_left hinner hfac
        _ = k v * Real.exp (-(a * t)) * (1 - Real.exp (-(biasedTotalRate γ β v * t))) * m v := by
            ring
    have hcomb : Real.exp (-((a + ρ) * t)) * S₀ * t ≤ a * m w * t :=
      le_trans hlower (le_trans hupper (le_of_eq (by ring)))
    exact le_of_mul_le_mul_right hcomb ht
  -- let `t → 0`
  have hS₀le : S₀ ≤ a * m w := by
    have hcont : Filter.Tendsto (fun t : ℝ => Real.exp (-((a + ρ) * t)) * S₀)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds S₀) := by
      have : Filter.Tendsto (fun t : ℝ => Real.exp (-((a + ρ) * t)) * S₀)
          (nhds 0) (nhds (Real.exp (-((a + ρ) * 0)) * S₀)) :=
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
          continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun t ht => key t ht)
  -- back to `ℝ≥0∞`
  have hfinL : ∑ v ∈ F, ENNReal.ofReal (biasedTotalRate γ β v)
      * biasedSkeletonKernel γ β v {w} * μ {v} ≠ ∞ :=
    (ENNReal.sum_ne_top).2 fun v _ =>
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (measure_ne_top _ _)
  have hfinR : ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  refine (ENNReal.toReal_le_toReal hfinL hfinR).1 ?_
  rw [ENNReal.toReal_sum fun v _ =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (measure_ne_top _ _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (biasedTotalRate_pos γ β w).le]
  refine le_trans (le_of_eq ?_) hS₀le
  rw [hS₀]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (biasedTotalRate_pos γ β v).le]

/-- The measure `ν = q · μ` that equation (13) inverts. -/
noncomputable def biasedRateMeasure (γ β : ℝ) (μ : Measure (Profile N M)) :
    Measure (Profile N M) :=
  μ.withDensity fun v => ENNReal.ofReal (biasedTotalRate γ β v)

omit [NeZero N] [NeZero M] in
@[simp]
theorem biasedRateMeasure_singleton (γ β : ℝ) (μ : Measure (Profile N M)) (w : Profile N M) :
    biasedRateMeasure γ β μ {w} = ENNReal.ofReal (biasedTotalRate γ β w) * μ {w} := by
  rw [biasedRateMeasure, withDensity_apply _ (measurableSet_singleton w),
    Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac, smul_eq_mul, mul_comm]

omit [NeZero N] [NeZero M] in
theorem biasedRateMeasure_compl_biasedStateSet (γ β : ℝ) {μ : Measure (Profile N M)}
    (hμ : IsCarriedByBiasedState μ) : biasedRateMeasure γ β μ (biasedStateSet N M)ᶜ = 0 := by
  rw [biasedRateMeasure, withDensity_apply _ (measurableSet_profile _),
    Measure.restrict_eq_zero.2 hμ, lintegral_zero_measure]

/-- **`νK ≤ ν`**: the biased skeleton sends `ν = q · μ` to at most itself. -/
theorem bind_biasedSkeletonKernel_le_biasedRateMeasure (γ β : ℝ) {μ : Measure (Profile N M)}
    [IsProbabilityMeasure μ] (hμ : IsBiasedInvariantCts γ β μ) :
    (biasedRateMeasure γ β μ).bind (biasedSkeletonKernel γ β) ≤ biasedRateMeasure γ β μ := by
  refine le_of_forall_singleton_le fun w => ?_
  rw [bind_apply_singleton, biasedRateMeasure_singleton, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  refine le_trans (le_of_eq ?_) (finsetSum_biasedRate_le γ β hμ w F)
  exact Finset.sum_congr rfl fun v _ => by rw [biasedRateMeasure_singleton]; ring

/-- **`ν = q · μ` has finite total mass**, by the minorisation of the biased skeleton: iterating
`νK ≤ ν` gives `ν {l} ≥ c · ν (S^α)`, and the left side is finite. -/
theorem biasedRateMeasure_univ_ne_top (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {μ : Measure (Profile N M)}
    [IsProbabilityMeasure μ] (hμS : IsCarriedByBiasedState μ) (hμ : IsBiasedInvariantCts γ β μ) :
    biasedRateMeasure γ β μ Set.univ ≠ ∞ := by
  classical
  set ν := biasedRateMeasure γ β μ with hν
  set o : Opinion M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ with ho
  set c : ℝ≥0∞ := ENNReal.ofReal (biasedZeta N M γ β) ^ N
    * ENNReal.ofReal (biasedStepFloor N M β
        (biasedGreedyBound N M + (N : ℝ) * (1 + γ))) ^ N with hc
  have hcpos : 0 < c := by
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · exact (ENNReal.ofReal_pos.2 (biasedZeta_pos N M γ β)).ne'
    · exact (ENNReal.ofReal_pos.2 (biasedStepFloor_pos N M β _)).ne'
  have hiter := bind_iterateKernel_le (bind_biasedSkeletonKernel_le_biasedRateMeasure γ β hμ)
    (N + N)
  have hS : ν Set.univ = ν (biasedStateSet N M) := by
    have h := measure_add_measure_compl (μ := ν) (measurableSet_profile (biasedStateSet N M))
    rw [hν, biasedRateMeasure_compl_biasedStateSet γ β hμS, add_zero] at h
    exact h.symm
  have hle : c * ν Set.univ ≤ ν {biasedLadderOf N o} := by
    refine le_trans ?_ (Measure.le_iff'.1 hiter {biasedLadderOf N o})
    rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
    calc c * ν Set.univ = ∫⁻ _ in biasedStateSet N M, c ∂ν := by rw [setLIntegral_const, hS]
      _ ≤ ∫⁻ v in biasedStateSet N M,
            iterateKernel (biasedSkeletonKernel γ β) (N + N) v {biasedLadderOf N o} ∂ν :=
          setLIntegral_mono (Kernel.measurable_coe _ (measurableSet_singleton _))
            (fun v hv => minorisation_iterateKernel hM hN hγ hγ' hβ o hv)
      _ ≤ ∫⁻ v, iterateKernel (biasedSkeletonKernel γ β) (N + N) v {biasedLadderOf N o} ∂ν :=
          setLIntegral_le_lintegral _ _
  have hfin : ν {biasedLadderOf N o} ≠ ∞ := by
    rw [hν, biasedRateMeasure_singleton]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  intro htop
  rw [htop, ENNReal.mul_top hcpos.ne'] at hle
  exact hfin (top_le_iff.1 hle)

/-- **`q · μ` is invariant for the biased skeleton**: the half of the correspondence of p. 18
that equation (13) needs, for the biased process. -/
theorem invariant_biasedRateMeasure (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {μ : Measure (Profile N M)}
    [IsProbabilityMeasure μ] (hμS : IsCarriedByBiasedState μ) (hμ : IsBiasedInvariantCts γ β μ) :
    IsBiasedInvariant γ β (biasedRateMeasure γ β μ) := by
  have huniv : ((biasedRateMeasure γ β μ).bind (biasedSkeletonKernel γ β)) Set.univ
      = biasedRateMeasure γ β μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp
  exact eq_of_le_of_univ_eq (bind_biasedSkeletonKernel_le_biasedRateMeasure γ β hμ) huniv
    (biasedRateMeasure_univ_ne_top hM hN hγ hγ' hβ hμS hμ)

/-- **Uniqueness for the biased skeleton**, in the form this file consumes: two invariant
probability measures carried by `S^α` agree.  This is the uniqueness half of
`SocialNetwork.Bias.existsUnique_biasedInvariant`, which holds for every `β ≥ 0`. -/
theorem eq_of_biasedInvariant (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {μ ν : Measure (Profile N M)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμS : IsCarriedByBiasedState μ) (hνS : IsCarriedByBiasedState ν)
    (hμ : IsBiasedInvariant γ β μ) (hν : IsBiasedInvariant γ β ν) : μ = ν := by
  have hpos : 0 < ENNReal.ofReal (biasedZeta N M γ β) ^ N
      * ENNReal.ofReal (biasedStepFloor N M β
          (biasedGreedyBound N M + (N : ℝ) * (1 + γ))) ^ N := by
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · exact (ENNReal.ofReal_pos.2 (biasedZeta_pos N M γ β)).ne'
    · exact (ENNReal.ofReal_pos.2 (biasedStepFloor_pos N M β _)).ne'
  exact eq_of_invariant_of_iterate_minorisation (biasedSkeletonKernel γ β) (N + N) hpos
    (fun Q hQ => minorisation_iterateKernel hM hN hγ hγ' hβ
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ hQ)
    hμS hνS hμ hν

/-! ### Equation (13) -/

/-- **Equation (13)** for the biased process.  For every profile `u`,

```
μ_{α,β} (u) = (μ̃_{α,β} (u) / q (u)) / ∑_{v} μ̃_{α,β} (v) / q (v).
```

**Follows the proof of equation (13)** (`SocialNetwork.invariantCts_eq_of_invariantSkeleton`),
as Appendix C prescribes for Theorem 25: `q · μ` is a finite invariant measure of the biased
skeleton, and normalising it identifies it with `μ̃_{α,β}` by uniqueness.  It does not use
non-explosion. -/
theorem biasedInvariantCts_eq (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {μ μskel : Measure (Profile N M)}
    (hμ : IsProbabilityMeasure μ) (hμS : IsCarriedByBiasedState μ)
    (hμinv : IsBiasedInvariantCts γ β μ) (hs : IsProbabilityMeasure μskel)
    (hsS : IsCarriedByBiasedState μskel) (hsinv : IsBiasedInvariant γ β μskel)
    (v : Profile N M) :
    μ {v} = (μskel {v} / ENNReal.ofReal (biasedTotalRate γ β v)) /
      ∑' w : Profile N M, μskel {w} / ENNReal.ofReal (biasedTotalRate γ β w) := by
  classical
  have hμprob : IsProbabilityMeasure μ := hμ
  have hsprob : IsProbabilityMeasure μskel := hs
  have hq0 : ∀ w : Profile N M, ENNReal.ofReal (biasedTotalRate γ β w) ≠ 0 :=
    fun w => (ENNReal.ofReal_pos.2 (biasedTotalRate_pos γ β w)).ne'
  set ν := biasedRateMeasure γ β μ with hν
  set Z := ν Set.univ with hZ
  have hZtop : Z ≠ ∞ := biasedRateMeasure_univ_ne_top hM hN hγ hγ' hβ hμS hμinv
  have hZ0 : Z ≠ 0 := by
    intro h0
    have hall : ∀ w : Profile N M, μ {w} = 0 := by
      intro w
      have hle : ν {w} ≤ Z := measure_mono (Set.subset_univ _)
      rw [h0, le_zero_iff, hν, biasedRateMeasure_singleton] at hle
      rcases mul_eq_zero.1 hle with h | h
      · exact absurd h (hq0 w)
      · exact h
    have hone := tsum_measure_singleton μ
    rw [tsum_congr hall] at hone
    simp at hone
  set ν' := Z⁻¹ • ν with hν'
  have hν'apply : ∀ w : Profile N M, ν' {w} = Z⁻¹ * ν {w} := by
    intro w
    rw [hν', Measure.smul_apply, smul_eq_mul]
  have : IsProbabilityMeasure ν' := by
    refine ⟨?_⟩
    rw [hν', Measure.smul_apply, smul_eq_mul, ← hZ, ENNReal.inv_mul_cancel hZ0 hZtop]
  have hν'S : IsCarriedByBiasedState ν' := by
    show ν' (biasedStateSet N M)ᶜ = 0
    rw [hν', Measure.smul_apply, smul_eq_mul, hν,
      biasedRateMeasure_compl_biasedStateSet γ β hμS, mul_zero]
  have hbase : ν.bind (biasedSkeletonKernel γ β) = ν :=
    invariant_biasedRateMeasure hM hN hγ hγ' hβ hμS hμinv
  have hν'inv : IsBiasedInvariant γ β ν' := by
    have hsing : ∀ y : Profile N M, (ν'.bind (biasedSkeletonKernel γ β)) {y} = ν' {y} := by
      intro y
      rw [bind_apply_singleton]
      have hcong : ∀ x : Profile N M, biasedSkeletonKernel γ β x {y} * ν' {x}
          = Z⁻¹ * (biasedSkeletonKernel γ β x {y} * ν {x}) := by
        intro x
        rw [hν'apply x, ← mul_assoc, ← mul_assoc, mul_comm (biasedSkeletonKernel γ β x {y}) Z⁻¹]
      rw [tsum_congr hcong, ENNReal.tsum_mul_left, ← bind_apply_singleton, hbase, hν'apply y]
    show ν'.bind (biasedSkeletonKernel γ β) = ν'
    exact ext_of_forall_singleton hsing
  have heq : ν' = μskel := eq_of_biasedInvariant hM hN hγ hγ' hβ hν'S hsS hν'inv hsinv
  have hskel : ∀ w : Profile N M,
      μskel {w} = Z⁻¹ * μ {w} * ENNReal.ofReal (biasedTotalRate γ β w) := by
    intro w
    rw [← heq, hν'apply w, hν, biasedRateMeasure_singleton]
    ring
  have hdiv : ∀ w : Profile N M,
      μskel {w} / ENNReal.ofReal (biasedTotalRate γ β w) = Z⁻¹ * μ {w} := by
    intro w
    rw [hskel w, div_eq_mul_inv, mul_assoc,
      ENNReal.mul_inv_cancel (hq0 w) ENNReal.ofReal_ne_top, mul_one]
  have htsum : ∑' w : Profile N M, μskel {w} / ENNReal.ofReal (biasedTotalRate γ β w) = Z⁻¹ := by
    rw [tsum_congr hdiv, ENNReal.tsum_mul_left, tsum_measure_singleton μ, mul_one]
  rw [hdiv v, htsum, div_eq_mul_inv, inv_inv, mul_comm Z⁻¹ (μ {v}), mul_assoc,
    ENNReal.inv_mul_cancel hZ0 hZtop, mul_one]

/-- **Theorem 25.2, the uniqueness half.**  The biased process has at most one invariant
probability measure carried by `S^α`: equation (13) writes both in terms of `μ̃_{α,β}`. -/
theorem eq_of_biasedInvariantCts (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β) {μ ν : Measure (Profile N M)}
    (hμ : IsProbabilityMeasure μ) (hμS : IsCarriedByBiasedState μ)
    (hμinv : IsBiasedInvariantCts γ β μ) (hν : IsProbabilityMeasure ν)
    (hνS : IsCarriedByBiasedState ν) (hνinv : IsBiasedInvariantCts γ β ν) : μ = ν := by
  obtain ⟨μskel, ⟨hsprob, hsS, hsinv⟩, -⟩ := existsUnique_biasedInvariant hM hN hγ hγ' hβ
  refine ext_of_forall_singleton fun v => ?_
  rw [biasedInvariantCts_eq hM hN hγ hγ' hβ.le hμ hμS hμinv hsprob hsS hsinv v,
    biasedInvariantCts_eq hM hN hγ hγ' hβ.le hν hνS hνinv hsprob hsS hsinv v]

end Transfer

end Bias

end SocialNetwork
