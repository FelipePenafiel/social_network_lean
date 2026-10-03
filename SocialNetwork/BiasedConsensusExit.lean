/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedResults
import SocialNetwork.JumpHold

/-!
# Lemma 29: leaving a biased consensus set

Draft.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The biased process restarted at its first jump

The biased path measure is `SocialNetwork.drivenMeasure` of `Profile.express` and the biased step
law, so the joint law of the first step and the rest is `SocialNetwork.map_drivenMeasure_firstRest`.
Everything after that is the argument of `SocialNetwork.ConsensusExit`, with
`SocialNetwork.Bias.stateAfter` in place of `SocialNetwork.Trajectory.state`. -/

section Restart

variable [NeZero N] [NeZero M]

/-- The biased path measure is the driven measure of its step law. -/
theorem biasedCtsPathMeasure_eq_drivenMeasure (γ β : ℝ) (u : Profile N M) :
    biasedCtsPathMeasure γ β u
      = drivenMeasure (fun (P : Profile N M) (p : Jump N M) => Profile.express p.1 p.2 P)
          (biasedStepLaw γ β) u := by
  have hstate : ∀ (j : ℕ → Jump N M) (n : ℕ),
      stateAfterJumps (fun (P : Profile N M) (p : Jump N M) => Profile.express p.1 p.2 P) u j n
        = stateAfter u j n := by
    intro j n
    induction n with
    | zero => rfl
    | succ n ih => rw [stateAfterJumps_succ, ih, stateAfter_succ]
  have hker : drivenKernel (fun (P : Profile N M) (p : Jump N M) => Profile.express p.1 p.2 P)
      (biasedStepLaw γ β) u = biasedCtsDrivingKernel γ β u := by
    funext n
    ext h : 1
    rw [drivenKernel_apply, biasedCtsDrivingKernel_apply]
    exact congrArg _ (hstate _ (n + 1))
  rw [drivenMeasure, jumpHoldMeasure, biasedCtsPathMeasure]
  simp only [hker]
  rfl

/-- **The restart at the first jump, on an arbitrary event**, for the biased process. -/
theorem biasedCtsPathMeasure_firstStep_apply (γ β : ℝ) (u : Profile N M)
    {S : Set (Step N M × (ℕ → Step N M))} (hS : MeasurableSet S) :
    biasedCtsPathMeasure γ β u {ω | (ω 0, shiftStepPath ω) ∈ S}
      = ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u) {ω' | (z, ω') ∈ S}
          ∂(biasedStepLaw γ β u) := by
  have hmeas : Measurable (fun ω : ℕ → Step N M => (ω 0, shiftHold ω)) :=
    (measurable_pi_apply 0).prodMk measurable_shiftHold
  have hset : {ω : ℕ → Step N M | (ω 0, shiftStepPath ω) ∈ S}
      = (fun ω : ℕ → Step N M => (ω 0, shiftHold ω)) ⁻¹' S := rfl
  rw [hset, biasedCtsPathMeasure_eq_drivenMeasure, ← Measure.map_apply hmeas hS,
    map_drivenMeasure_firstRest, Measure.compProd_apply hS]
  refine lintegral_congr fun z => ?_
  rw [restartKernel_apply, biasedCtsPathMeasure_eq_drivenMeasure]
  rfl

/-- The chance that the first holding time exceeds `t`. -/
theorem biasedCtsPathMeasure_lt_holdingTime (γ β : ℝ) (u : Profile N M) {t : ℝ} (ht : 0 ≤ t) :
    biasedCtsPathMeasure γ β u {ω | t < holdingTime 0 ω}
      = ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t))) := by
  have hq := biasedTotalRate_pos γ β u
  have hE : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β u)) :=
    isProbabilityMeasure_expMeasure hq
  have hS : MeasurableSet {x : Step N M × (ℕ → Step N M) | t < x.1.2} :=
    measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)
  have h := biasedCtsPathMeasure_firstStep_apply γ β u hS
  have hset : {ω : ℕ → Step N M | t < holdingTime 0 ω}
      = {ω | (ω 0, shiftStepPath ω) ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}} := rfl
  rw [hset, h]
  have hpt : ∀ z : Step N M, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
      {ω' | (z, ω') ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}}
      = (Set.univ ×ˢ Set.Ioi t : Set (Step N M)).indicator 1 z := by
    rintro ⟨p, s⟩
    by_cases hs : t < s
    · have hmem : ((p, s) : Step N M) ∈ (Set.univ ×ˢ Set.Ioi t : Set (Step N M)) :=
        ⟨Set.mem_univ _, hs⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      have : {ω' : ℕ → Step N M | ((p, s), ω') ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}}
          = Set.univ := by ext; simp [hs]
      rw [this, measure_univ]
    · have hmem : ((p, s) : Step N M) ∉ (Set.univ ×ˢ Set.Ioi t : Set (Step N M)) :=
        fun h => hs h.2
      rw [Set.indicator_of_notMem hmem]
      have : {ω' : ℕ → Step N M | ((p, s), ω') ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}}
          = ∅ := by ext; simp [hs]
      rw [this, measure_empty]
  rw [lintegral_congr hpt, lintegral_indicator_one (MeasurableSet.univ.prod measurableSet_Ioi),
    biasedStepLaw, Measure.prod_prod, measure_univ, one_mul,
    expMeasure_Ioi_of_nonneg hq ht]

/-- Every holding time is almost surely positive. -/
theorem biasedCtsPathMeasure_holdingTime_nonpos (γ β : ℝ) (n : ℕ) :
    ∀ u : Profile N M, biasedCtsPathMeasure γ β u {ω | holdingTime n ω ≤ 0} = 0 := by
  induction n with
  | zero =>
      intro u
      have hq := biasedTotalRate_pos γ β u
      have hle : biasedCtsPathMeasure γ β u {ω | holdingTime 0 ω ≤ 0}
          ≤ biasedCtsPathMeasure γ β u {ω | 0 < holdingTime 0 ω}ᶜ :=
        measure_mono fun ω hω => by simpa using hω
      have hc := prob_compl_eq_one_sub (μ := biasedCtsPathMeasure γ β u)
        (s := {ω : ℕ → Step N M | 0 < holdingTime 0 ω})
        (measurableSet_lt measurable_const (measurable_holdingTime 0))
      rw [biasedCtsPathMeasure_lt_holdingTime γ β u le_rfl, mul_zero, neg_zero, Real.exp_zero,
        ENNReal.ofReal_one, tsub_self] at hc
      exact le_antisymm (hc ▸ hle) zero_le
  | succ n ih =>
      intro u
      have hS : MeasurableSet {x : Step N M × (ℕ → Step N M) | holdingTime n x.2 ≤ 0} :=
        measurableSet_le ((measurable_holdingTime n).comp measurable_snd) measurable_const
      have hset : {ω : ℕ → Step N M | holdingTime (n + 1) ω ≤ 0}
          = {ω | (ω 0, shiftStepPath ω) ∈
              {x : Step N M × (ℕ → Step N M) | holdingTime n x.2 ≤ 0}} := by
        ext ω
        simp only [Set.mem_ofPred_eq, holdingTime_shiftStepPath]
      rw [hset, biasedCtsPathMeasure_firstStep_apply γ β u hS]
      exact lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun z => ih _) |>.trans
        (by simp)

/-- The realisations whose holding times are all positive carry all the mass. -/
theorem biasedCtsPathMeasure_holdingTime_pos_compl (γ β : ℝ) (u : Profile N M) :
    biasedCtsPathMeasure γ β u {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}ᶜ = 0 := by
  rw [show {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}ᶜ
      = ⋃ n, {ω : ℕ → Step N M | holdingTime n ω ≤ 0} from by
    ext ω; simp [not_forall, not_lt]]
  exact measure_iUnion_null fun n => biasedCtsPathMeasure_holdingTime_nonpos γ β n u

end Restart

/-! ### Reading the biased process off the jump times -/

section Shift

/-- No jump by time `t`: the biased process is still where it started. -/
theorem biasedProcess_eq_of_lt_holdingTime (u : Profile N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) {t : ℝ} (ht : 0 ≤ t) (h : t < holdingTime 0 ω) :
    biasedProcess u t ω = u := by
  have hset : {n : ℕ | jumpTime n ω ≤ t} = {0} := by
    refine Set.Subset.antisymm (fun n hn => ?_) (by simpa using ht)
    by_contra hne
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by simpa using hne)
    have hle : jumpTime 1 ω ≤ jumpTime n ω := jumpTime_mono hpos h1
    rw [jumpTime_one] at hle
    exact absurd (le_trans hle hn) (not_le.2 h)
  have hcount : jumpCount ω t = 0 := by
    rw [jumpCount, hset, csSup_singleton]
  show stateAfter u (fun n => (ω n).1) (jumpCount ω t) = u
  rw [hcount, stateAfter_zero]

/-- The profile after `n + 1` expressions is the one the rest reaches after `n`, from the profile
the first expression produced. -/
theorem stateAfter_succ_shift (u : Profile N M) (ω : ℕ → Step N M) (n : ℕ) :
    stateAfter u (fun k => (ω k).1) (n + 1)
      = stateAfter (Profile.express (ω 0).1.1 (ω 0).1.2 u)
          (fun k => (shiftStepPath ω k).1) n := by
  rw [Nat.add_comm, stateAfter_add]
  rfl

/-- **The biased hitting time after the first jump, from below.** -/
theorem le_biasedHittingTimeCts_shift (u : Profile N M) {θ : Set (Profile N M)} (hu : u ∉ θ)
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) :
    ENNReal.ofReal (holdingTime 0 ω)
        + biasedHittingTimeCts (Profile.express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
      ≤ biasedHittingTimeCts u θ ω := by
  set S₀ := holdingTime 0 ω with hS₀
  have hS₀pos : 0 < S₀ := hpos 0
  conv_rhs => unfold biasedHittingTimeCts
  refine le_sInf ?_
  rintro _ ⟨s, ⟨hs0, hsθ⟩, rfl⟩
  have hS₀s : S₀ ≤ s := by
    by_contra hlt
    exact hu (by rwa [biasedProcess_eq_of_lt_holdingTime u hpos hs0 (not_le.1 hlt)] at hsθ)
  by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ s}
  · have hb' : BddAbove {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s - S₀} := by
      obtain ⟨B, hB⟩ := hb
      refine ⟨B, fun m hm => ?_⟩
      have : jumpTime (m + 1) ω ≤ s := by
        rw [jumpTime_succ_shiftStepPath]
        have : jumpTime m (shiftStepPath ω) ≤ s - S₀ := hm
        linarith
      have := hB this
      omega
    have hne : {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s - S₀}.Nonempty :=
      ⟨0, by simp; linarith⟩
    set m := jumpCount (shiftStepPath ω) (s - S₀) with hm
    have hmem : jumpTime m (shiftStepPath ω) ≤ s - S₀ := Nat.sSup_mem hne hb'
    have hcount : jumpCount ω s = m + 1 := by
      refine (jumpCount_eq_iff s ω (Nat.succ_ne_zero m)).2 ⟨?_, fun k hk => ?_⟩
      · rw [jumpTime_succ_shiftStepPath]; linarith
      · cases k with
        | zero => omega
        | succ j =>
            rw [jumpTime_succ_shiftStepPath] at hk
            have hj : jumpTime j (shiftStepPath ω) ≤ s - S₀ := by linarith
            have h' : j ≤ jumpCount (shiftStepPath ω) (s - S₀) := le_csSup hb' hj
            omega
    have hproc : biasedProcess (Profile.express (ω 0).1.1 (ω 0).1.2 u) (s - S₀) (shiftStepPath ω)
        = biasedProcess u s ω := by
      show stateAfter _ (fun k => (shiftStepPath ω k).1) (jumpCount (shiftStepPath ω) (s - S₀))
        = stateAfter u (fun k => (ω k).1) (jumpCount ω s)
      rw [hcount, ← hm, stateAfter_succ_shift]
    calc ENNReal.ofReal S₀
          + biasedHittingTimeCts (Profile.express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
        ≤ ENNReal.ofReal S₀ + ENNReal.ofReal (s - S₀) := by
          refine add_le_add le_rfl (sInf_le ⟨s - S₀, ⟨by linarith, ?_⟩, rfl⟩)
          rw [hproc]; exact hsθ
      _ = ENNReal.ofReal s := by
          rw [← ENNReal.ofReal_add hS₀pos.le (by linarith)]
          congr 1; ring
  · exfalso
    have h0 : jumpCount ω s = 0 := Nat.sSup_of_not_bddAbove hb
    apply hu
    have : biasedProcess u s ω = u := by
      show stateAfter u (fun k => (ω k).1) (jumpCount ω s) = u
      rw [h0, stateAfter_zero]
    rwa [this] at hsθ

end Shift

/-! ### Not reaching the target before `min (t, T_n)`, for the biased process -/

section Avoid

/-- The realisations on which `θ` has not been reached before `min (t, T_n)`. -/
def biasedAvoidBefore (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ) (t : ℝ) :
    Set (ℕ → Step N M) :=
  {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω ∨
    ENNReal.ofReal (jumpTime n ω) ≤ biasedHittingTimeCts u θ ω}

/-- The same events, at all times at once. -/
def biasedAvoidBeforeGraph (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ) :
    Set (ℝ × (ℕ → Step N M)) :=
  {x | x.2 ∈ biasedAvoidBefore u θ n x.1}

theorem measurableSet_biasedAvoidBeforeGraph (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ) :
    MeasurableSet (biasedAvoidBeforeGraph u θ n) := by
  have h1 : Measurable fun x : ℝ × (ℕ → Step N M) => biasedHittingTimeCts u θ x.2 :=
    (measurable_biasedHittingTimeCts u θ).comp measurable_snd
  have h2 : Measurable fun x : ℝ × (ℕ → Step N M) => ENNReal.ofReal x.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have h3 : Measurable fun x : ℝ × (ℕ → Step N M) => ENNReal.ofReal (jumpTime n x.2) :=
    ENNReal.measurable_ofReal.comp ((measurable_jumpTime n).comp measurable_snd)
  have hset : biasedAvoidBeforeGraph u θ n
      = {x : ℝ × (ℕ → Step N M) | ENNReal.ofReal x.1 < biasedHittingTimeCts u θ x.2}
        ∪ {x | ENNReal.ofReal (jumpTime n x.2) ≤ biasedHittingTimeCts u θ x.2} := rfl
  rw [hset]
  exact (measurableSet_lt h2 h1).union (measurableSet_le h3 h1)

theorem measurableSet_biasedAvoidBefore (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ)
    (t : ℝ) : MeasurableSet (biasedAvoidBefore u θ n t) := by
  show MeasurableSet (Prod.mk t ⁻¹' biasedAvoidBeforeGraph u θ n)
  exact measurable_prodMk_left (measurableSet_biasedAvoidBeforeGraph u θ n)

theorem biasedAvoidBefore_zero (u : Profile N M) (θ : Set (Profile N M)) (t : ℝ) :
    biasedAvoidBefore u θ 0 t = Set.univ := by
  ext ω
  simp [biasedAvoidBefore]

variable [NeZero N] [NeZero M]

/-- **The first-step inequality**, for the biased process. -/
theorem le_biasedCtsPathMeasure_avoidBefore_succ (γ β : ℝ) {u : Profile N M}
    {θ : Set (Profile N M)} (hu : u ∉ θ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t)))
        + ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
            {ω' | z.2 ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express z.1.1 z.1.2 u) θ n (t - z.2)}
            ∂(biasedStepLaw γ β u)
      ≤ biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ (n + 1) t) := by
  set G := {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} with hGdef
  set S : Set (Step N M × (ℕ → Step N M)) :=
    {x | x.1.2 ≤ t ∧ x.2 ∈ biasedAvoidBefore (Profile.express x.1.1.1 x.1.1.2 u) θ n (t - x.1.2)}
    with hSdef
  have hSmeas : MeasurableSet S := by
    have hset : S = ⋃ p : Jump N M,
        ((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹' {p})
          ∩ (((fun x : Step N M × (ℕ → Step N M) => x.1.2) ⁻¹' Set.Iic t)
            ∩ ((fun x : Step N M × (ℕ → Step N M) => (t - x.1.2, x.2)) ⁻¹'
              biasedAvoidBeforeGraph (Profile.express p.1 p.2 u) θ n)) := by
      ext x
      simp only [hSdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_Iic, biasedAvoidBeforeGraph, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨x.1.1, rfl, h1, h2⟩
      · rintro ⟨p, rfl, h1, h2⟩
        exact ⟨h1, h2⟩
    rw [hset]
    refine MeasurableSet.iUnion fun p => ?_
    refine ((measurable_fst.comp measurable_fst) (measurableSet_singleton p)).inter
      (((measurable_snd.comp measurable_fst) measurableSet_Iic).inter ?_)
    exact ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
      (measurableSet_biasedAvoidBeforeGraph _ θ n)
  set A : Set (ℕ → Step N M) := {ω | t < holdingTime 0 ω} with hAdef
  set B : Set (ℕ → Step N M) := {ω | (ω 0, shiftStepPath ω) ∈ S} with hBdef
  have hBmeas : MeasurableSet B :=
    ((measurable_pi_apply 0).prodMk measurable_shiftStepPath) hSmeas
  have hA : biasedCtsPathMeasure γ β u A
      = ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t))) :=
    biasedCtsPathMeasure_lt_holdingTime γ β u ht
  have hB : biasedCtsPathMeasure γ β u B
      = ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
          {ω' | z.2 ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express z.1.1 z.1.2 u) θ n (t - z.2)}
          ∂(biasedStepLaw γ β u) :=
    biasedCtsPathMeasure_firstStep_apply γ β u hSmeas
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ω hA ⟨hB, -⟩
    exact absurd hB (not_le.2 hA)
  have hsub : (A ∪ B) ∩ G ⊆ biasedAvoidBefore u θ (n + 1) t := by
    rintro ω ⟨hAB, hG⟩
    have hG' : ∀ n, 0 < holdingTime n ω := hG
    have hkey := le_biasedHittingTimeCts_shift u hu hG'
    set R' := biasedHittingTimeCts (Profile.express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
    have hS₀ : 0 < holdingTime 0 ω := hG' 0
    rcases hAB with hω | ⟨hle, hω⟩
    · change t < holdingTime 0 ω at hω
      left
      calc ENNReal.ofReal t < ENNReal.ofReal (holdingTime 0 ω) :=
            (ENNReal.ofReal_lt_ofReal_iff hS₀).2 hω
        _ ≤ ENNReal.ofReal (holdingTime 0 ω) + R' := le_self_add
        _ ≤ biasedHittingTimeCts u θ ω := hkey
    · change holdingTime 0 ω ≤ t at hle
      change ENNReal.ofReal (t - holdingTime 0 ω) < R'
        ∨ ENNReal.ofReal (jumpTime n (shiftStepPath ω)) ≤ R' at hω
      rcases hω with hω | hω
      · left
        calc ENNReal.ofReal t
            = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal (t - holdingTime 0 ω) := by
              rw [← ENNReal.ofReal_add hS₀.le (by linarith)]; congr 1; ring
          _ < ENNReal.ofReal (holdingTime 0 ω) + R' :=
              ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hω
          _ ≤ biasedHittingTimeCts u θ ω := hkey
      · right
        have hTn : 0 ≤ jumpTime n (shiftStepPath ω) :=
          Finset.sum_nonneg fun k _ => by
            rw [holdingTime_shiftStepPath]; exact (hG' (k + 1)).le
        calc ENNReal.ofReal (jumpTime (n + 1) ω)
            = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal (jumpTime n (shiftStepPath ω)) := by
              rw [jumpTime_succ_shiftStepPath, ENNReal.ofReal_add hS₀.le hTn]
          _ ≤ ENNReal.ofReal (holdingTime 0 ω) + R' := add_le_add le_rfl hω
          _ ≤ biasedHittingTimeCts u θ ω := hkey
  have hGnull := biasedCtsPathMeasure_holdingTime_pos_compl γ β u
  have hconull : biasedCtsPathMeasure γ β u ((A ∪ B) ∩ G)
      = biasedCtsPathMeasure γ β u (A ∪ B) := by
    have h := measure_inter_add_sdiff (μ := biasedCtsPathMeasure γ β u) (A ∪ B)
      measurableSet_holdingTime_pos
    rwa [measure_mono_null (Set.sdiff_subset_compl _ _) hGnull, add_zero] at h
  rw [← hA, ← hB, ← measure_union hdisj hBmeas, ← hconull]
  exact measure_mono hsub

/-- **Passing to the limit**, for the biased process. -/
theorem le_biasedCtsPathMeasure_lt_hittingTimeCts (γ β : ℝ) {u : Profile N M}
    {θ : Set (Profile N M)} (hu : u ∉ θ) {t : ℝ} {c : ℝ≥0∞}
    (h : ∀ n, c ≤ biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ n t)) :
    c ≤ biasedCtsPathMeasure γ β u {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω} := by
  set G := {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} with hGdef
  set s : ℕ → Set (ℕ → Step N M) := fun n => biasedAvoidBefore u θ n t ∩ G with hsdef
  have hGnull := biasedCtsPathMeasure_holdingTime_pos_compl γ β u
  have hconull : ∀ n, biasedCtsPathMeasure γ β u (s n)
      = biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ n t) := by
    intro n
    have h := measure_inter_add_sdiff (μ := biasedCtsPathMeasure γ β u)
      (biasedAvoidBefore u θ n t) measurableSet_holdingTime_pos
    rwa [measure_mono_null (Set.sdiff_subset_compl _ _) hGnull, add_zero] at h
  have hanti : Antitone s := by
    refine antitone_nat_of_succ_le fun n => ?_
    rintro ω ⟨hω, hG⟩
    refine ⟨?_, hG⟩
    rcases hω with hω | hω
    · exact Or.inl hω
    · right
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hω
      rw [jumpTime_succ]
      linarith [(hG : ∀ n, 0 < holdingTime n ω) n]
  have hinter : (⋂ n, s n) ⊆ {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω} := by
    intro ω hω
    rw [Set.mem_iInter] at hω
    have hG : ∀ n, 0 < holdingTime n ω := (hω 0).2
    by_contra hnot
    have hall : ∀ n, ENNReal.ofReal (jumpTime n ω) ≤ biasedHittingTimeCts u θ ω := fun n =>
      (hω n).1.resolve_left hnot
    apply hnot
    show ENNReal.ofReal t < biasedHittingTimeCts u θ ω
    suffices htop : biasedHittingTimeCts u θ ω = ⊤ by rw [htop]; exact ENNReal.ofReal_lt_top
    unfold biasedHittingTimeCts
    rw [sInf_eq_top]
    rintro _ ⟨r, ⟨hr0, hrθ⟩, rfl⟩
    exfalso
    by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ r}
    · have hne : {n : ℕ | jumpTime n ω ≤ r}.Nonempty := ⟨0, by simpa using hr0⟩
      set k := jumpCount ω r with hk
      have hkmem : jumpTime k ω ≤ r := Nat.sSup_mem hne hb
      have hmono := jumpTime_mono hG
      have hk0 : 0 ≤ jumpTime k ω := Finset.sum_nonneg fun i _ => (hG i).le
      have hcountk : jumpCount ω (jumpTime k ω) = k := by
        have hbk : BddAbove {n : ℕ | jumpTime n ω ≤ jumpTime k ω} :=
          hb.mono fun n hn => le_trans hn hkmem
        have hkk : k ∈ {n : ℕ | jumpTime n ω ≤ jumpTime k ω} := le_refl (jumpTime k ω)
        refine le_antisymm (csSup_le ⟨k, hkk⟩ fun n hn => ?_) (le_csSup hbk hkk)
        by_contra hlt
        have hstep : jumpTime (k + 1) ω ≤ jumpTime n ω := hmono (by omega)
        rw [jumpTime_succ] at hstep
        have : jumpTime n ω ≤ jumpTime k ω := hn
        linarith [hG k]
      have hR : biasedHittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime k ω) := by
        unfold biasedHittingTimeCts
        refine sInf_le ⟨jumpTime k ω, ⟨hk0, ?_⟩, rfl⟩
        show stateAfter u (fun n => (ω n).1) (jumpCount ω (jumpTime k ω)) ∈ θ
        rw [hcountk]
        exact hrθ
      have h1 := le_trans (hall (k + 1)) hR
      rw [ENNReal.ofReal_le_ofReal_iff hk0, jumpTime_succ] at h1
      linarith [hG k]
    · have h0 : jumpCount ω r = 0 := Nat.sSup_of_not_bddAbove hb
      apply hu
      have : biasedProcess u r ω = u := by
        show stateAfter u (fun n => (ω n).1) (jumpCount ω r) = u
        rw [h0, stateAfter_zero]
      rwa [this] at hrθ
  have hsmeas : ∀ n, MeasurableSet (s n) := fun n =>
    (measurableSet_biasedAvoidBefore u θ n t).inter measurableSet_holdingTime_pos
  have hlim : biasedCtsPathMeasure γ β u (⋂ n, s n) = ⨅ n, biasedCtsPathMeasure γ β u (s n) :=
    hanti.measure_iInter (fun n => (hsmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  calc c ≤ ⨅ n, biasedCtsPathMeasure γ β u (s n) := le_iInf fun n => by rw [hconull]; exact h n
    _ = biasedCtsPathMeasure γ β u (⋂ n, s n) := hlim.symm
    _ ≤ _ := measure_mono hinter

end Avoid

section Lemma29

variable [NeZero N] [NeZero M]

/-- **Lemma 29.1.**  From a biased ladder supporting `o`, the consensus for another opinion is
not reached before time `t` with probability at least
`exp (-2 t N³ (M+1)³ e^{-βγ/2})`. -/
theorem le_biasedProbHittingGT (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {l : Profile N M}
    (hl : IsBiasedLadder γ o l) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.exp
        (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β * γ / 2)))
      ≤ biasedProbHittingGT γ β l (biasedConsensusSetOther N γ o) (ENNReal.ofReal t) := by
  sorry

/-- **Lemma 29.2.**  From a biased consensus state for `o`, the consensus for another opinion
is reached before time `t` with probability at most
`(N² M + 2 t N³ (M+1)³) e^{-βγ/2}`. -/
theorem biasedProbHittingLE_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {u : Profile N M}
    (hu : IsBiasedConsensus γ o u) {t : ℝ} (ht : 0 < t) :
    biasedCtsPathMeasure γ β u
        {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal t}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
          Real.exp (-β * γ / 2)) := by
  sorry

end Lemma29

end Bias

end SocialNetwork
