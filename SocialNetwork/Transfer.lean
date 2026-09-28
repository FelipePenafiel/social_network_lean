/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.ContinuousTime

/-!
# Equation (13): the transfer from the skeleton to continuous time

The proof of equation (13) at p. 18 of arXiv:2607.19651 reads, in full:

> For a non-explosive process, a probability measure is invariant for `(U_t^{β,u})_t` if and
> only if its product with the jump rate is invariant for the skeleton chain.

The equivalence is cited, not proved, and Mathlib has no form of it.  This file proves the
half that equation (13) needs, for the process this repository builds.

## The argument

Only a lower bound on `P_t` is used, and it is read off two events that the jump-hold
representation makes explicit: from `v`, either no jump has occurred by time `t`, or exactly
one has and it landed on `w`.  They are disjoint, so

```
P_t (v, w)  ≥  [v = w] e^{-q(v)t}  +  K (v, w) · t · q(v) · e^{-(q(v) + q(w))t},
```

where `K` is the skeleton kernel.  Feeding that into the invariance equation
`μ {w} = ∑_v P_t (v, w) μ {v}`, subtracting the first term, dividing by `t` and letting
`t → 0` along a finite set of `v` at a time gives

```
q(w) μ {w}  ≥  ∑_v q(v) μ {v} K (v, w),
```

that is, `ν ≥ νK` for `ν = q · μ`.  The minorisation of p. 15 then closes the argument
twice over: it forces `ν` to have finite total mass — `ν {l} ≥ c · ν (S)` and the left side is
finite because `q(l) < ∞` — and finite mass turns the inequality into an equality, because
both sides then have the same total mass.  Normalising and appealing to the uniqueness of the
skeleton's invariant measure identifies `ν` with `μ̃^β`, which is equation (13).

## What this does not need

**Not Theorem 1.1.**  The paper's argument opens by invoking non-explosion, and that appeal is
discharged — but the route here does not use it.  Both events above are read off the jump
counter directly, on the almost-sure set where the holding times are positive: with no jump by
`t` the counter is `0`, and with exactly one it is `1`, whether or not the jump times
accumulate later.  Non-explosion is what makes `U_t` the process the paper means; it is not
needed to bound its law below.

**Not a Chapman–Kolmogorov identity.**  Nothing here composes `P_s` with `P_t`.

## Main statements

* `SocialNetwork.ctsPathMeasure_firstStep_apply` — the joint law of the first step and the rest
  of the realisation, on an arbitrary measurable set of pairs.
* `SocialNetwork.le_transitionKernel_singleton` — the lower bound on `P_t` displayed above.
* `SocialNetwork.skeletonKernel_rateMeasure_le` — `νK ≤ ν` for `ν = q · μ`.
* `SocialNetwork.invariantCts_eq_of_invariantSkeleton` — **equation (13)**.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### The joint law of the first step and the rest of the realisation

`SocialNetwork.ctsPathMeasure_restart` says that on a rectangle — the first step lies in `B`,
the rest of the realisation lies in `E` — the law factorises.  The events below are not
rectangles: "exactly one jump by time `t`" constrains the holding time that follows in terms
of the one that came first.  So the factorisation is upgraded here to the joint law itself. -/

section FirstStep

variable {β : ℝ} {u : Pressure N M}

/-- The law of the rest of the realisation, given the first step: the process started at the
matrix that step reaches.  It depends on the step through its pair alone. -/
noncomputable def firstStepKernel (β : ℝ) (u : Pressure N M) :
    Kernel (Step N M) (ℕ → Step N M) :=
  Kernel.comap
    (Kernel.ofFunOfCountable fun p : Jump N M => ctsPathMeasure β (express p.1 p.2 u))
    Prod.fst measurable_fst

@[simp]
theorem firstStepKernel_apply (β : ℝ) (u : Pressure N M) (z : Step N M) :
    firstStepKernel β u z = ctsPathMeasure β (express z.1.1 z.1.2 u) := rfl

instance isMarkovKernel_firstStepKernel (β : ℝ) (u : Pressure N M) :
    IsMarkovKernel (firstStepKernel β u) :=
  ⟨fun z => by rw [firstStepKernel_apply]; infer_instance⟩

/-- **The joint law of the first step and the rest.**  The first step is drawn from
`stepLaw β u`, and given it the rest of the realisation is a realisation started at the matrix
it reaches.  This is `SocialNetwork.ctsPathMeasure_restart` with the rectangles removed. -/
theorem map_ctsPathMeasure_firstStep (β : ℝ) (u : Pressure N M) :
    (ctsPathMeasure β u).map (fun ω => (ω 0, shiftStepPath ω))
      = (stepLaw β u).compProd (firstStepKernel β u) := by
  have hmeas : Measurable (fun ω : ℕ → Step N M => (ω 0, shiftStepPath ω)) :=
    (measurable_pi_apply 0).prodMk measurable_shiftStepPath
  have hprob : IsProbabilityMeasure ((ctsPathMeasure β u).map
      (fun ω : ℕ → Step N M => (ω 0, shiftStepPath ω))) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine MeasureTheory.ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) {s : Set (Step N M) | MeasurableSet s}
      {t : Set (ℕ → Step N M) | MeasurableSet t}) generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨B, (hB : MeasurableSet B), E, (hE : MeasurableSet E), rfl⟩
    rw [Measure.map_apply hmeas (hB.prod hE),
      Measure.compProd_apply_prod hB hE]
    have hpre : (fun ω : ℕ → Step N M => (ω 0, shiftStepPath ω)) ⁻¹' (B ×ˢ E)
        = {ω : ℕ → Step N M | ω 0 ∈ B} ∩ shiftStepPath ⁻¹' E := rfl
    rw [hpre, ctsPathMeasure_restart β u hB hE]
    exact setLIntegral_congr_fun hB fun z _ => rfl
  · rw [measure_univ, measure_univ]

/-- **The restart at the first jump, on an arbitrary event.**  The event may constrain the rest
of the realisation in terms of the first step, which is what the rectangles of
`SocialNetwork.ctsPathMeasure_restart` cannot do. -/
theorem ctsPathMeasure_firstStep_apply (β : ℝ) (u : Pressure N M)
    {S : Set (Step N M × (ℕ → Step N M))} (hS : MeasurableSet S) :
    ctsPathMeasure β u {ω | (ω 0, shiftStepPath ω) ∈ S}
      = ∫⁻ z, ctsPathMeasure β (express z.1.1 z.1.2 u) {ω' | (z, ω') ∈ S} ∂(stepLaw β u) := by
  have hmeas : Measurable (fun ω : ℕ → Step N M => (ω 0, shiftStepPath ω)) :=
    (measurable_pi_apply 0).prodMk measurable_shiftStepPath
  have hset : {ω : ℕ → Step N M | (ω 0, shiftStepPath ω) ∈ S}
      = (fun ω : ℕ → Step N M => (ω 0, shiftStepPath ω)) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply hmeas hS, map_ctsPathMeasure_firstStep,
    Measure.compProd_apply hS]
  exact lintegral_congr fun z => rfl

end FirstStep

/-! ### Reading the process off the first two holding times

Two events decide the matrix at time `t` without any knowledge of the rest of the
realisation: no jump has occurred, or exactly one has.  On the almost-sure set where the
holding times are positive the jump counter is `0` and `1` there, whatever the jump times do
afterwards --- in particular whether or not they accumulate, which is why nothing below needs
Theorem 1.1. -/

section Counter

omit [NeZero N] [NeZero M]

/-- The jump times increase along a realisation whose holding times are positive. -/
theorem jumpTime_mono {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) :
    Monotone fun n => jumpTime n ω := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [jumpTime_succ]
  linarith [hpos n]

theorem jumpTime_one (ω : ℕ → Step N M) : jumpTime 1 ω = holdingTime 0 ω := by
  simp [jumpTime]

theorem jumpTime_two (ω : ℕ → Step N M) :
    jumpTime 2 ω = holdingTime 0 ω + holdingTime 1 ω := by
  simp [jumpTime, Finset.sum_range_succ]

/-- **No jump by time `t`.**  The process is still at the matrix it started from. -/
theorem process_eq_of_lt_holdingTime (v : Pressure N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) {t : ℝ} (ht : 0 ≤ t) (h : t < holdingTime 0 ω) :
    process v t ω = v := by
  have hset : {n : ℕ | jumpTime n ω ≤ t} = {0} := by
    refine Set.Subset.antisymm (fun n hn => ?_) (by simpa using ht)
    by_contra hne
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by simpa using hne)
    have hle : jumpTime 1 ω ≤ jumpTime n ω := jumpTime_mono hpos h1
    rw [jumpTime_one] at hle
    exact absurd (le_trans hle hn) (not_le.2 h)
  have hcount : jumpCount ω t = 0 := by
    rw [jumpCount, hset, csSup_singleton]
  show (Trajectory.ofStepPath ω).state v (jumpCount ω t) = v
  rw [hcount, Trajectory.state_zero]

/-- **Exactly one jump by time `t`.**  The process sits at the matrix that the first expressed
pair reaches. -/
theorem process_eq_of_one_jump (v : Pressure N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) {t : ℝ} (h0 : holdingTime 0 ω ≤ t)
    (h1 : t < holdingTime 0 ω + holdingTime 1 ω) :
    process v t ω = express (ω 0).1.1 (ω 0).1.2 v := by
  have hcount : jumpCount ω t = 1 := by
    refine (jumpCount_eq_iff t ω one_ne_zero).2 ⟨by rwa [jumpTime_one], fun m hm => ?_⟩
    by_contra hlt
    have h2 : 2 ≤ m := by omega
    have hle : jumpTime 2 ω ≤ jumpTime m ω := jumpTime_mono hpos h2
    rw [jumpTime_two] at hle
    exact absurd (le_trans hle hm) (not_le.2 h1)
  show (Trajectory.ofStepPath ω).state v (jumpCount ω t) = _
  rw [hcount]
  exact state_one_ofStepPath v ω

end Counter

/-! ### The transition kernel from below

`P_t (v, w)` is bounded below by the mass of the two events above.  They are disjoint --- one
has a jump by `t`, the other does not --- and the second is computed through the joint law of
the first step and the rest. -/

section Bound

/-- The chance that no jump has occurred by time `t`. -/
theorem ctsPathMeasure_lt_holdingTime (β : ℝ) (v : Pressure N M) {t : ℝ} (ht : 0 ≤ t) :
    ctsPathMeasure β v {ω | t < holdingTime 0 ω}
      = ENNReal.ofReal (Real.exp (-(totalRate β v * t))) := by
  rw [show {ω : ℕ → Step N M | t < holdingTime 0 ω}
      = {ω | holdingTime 0 ω ∈ Set.Ioi t} from rfl,
    ctsPathMeasure_holdingTime_zero β v measurableSet_Ioi,
    expMeasure_Ioi_of_nonneg (totalRate_pos β v) ht]

omit [NeZero N] [NeZero M] in
/-- The exponential law of rate `r` puts mass `1 - e^{-rt}` on `[0, t]`: it has no mass below
zero. -/
theorem expMeasure_Icc_zero {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    expMeasure r (Set.Icc 0 t) = ENNReal.ofReal (1 - Real.exp (-(r * t))) := by
  have hnull : expMeasure r (Set.Iio 0) = 0 :=
    measure_mono_null Set.Iio_subset_Iic_self (expMeasure_Iic_zero hr)
  have hsplit : Set.Iic t = Set.Iio (0 : ℝ) ∪ Set.Icc 0 t := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_Icc]
    constructor
    · intro hx
      rcases lt_or_ge x 0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨-, h⟩)
      · exact le_trans h.le ht
      · exact h
  have hdisj : Disjoint (Set.Iio (0 : ℝ)) (Set.Icc 0 t) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨hx0, -⟩
    exact absurd hx0 (not_le.2 hx)
  have h := expMeasure_Iic_of_nonneg hr ht
  rwa [hsplit, measure_union hdisj measurableSet_Icc, hnull, zero_add] at h

/-- One step of the skeleton, read as a mass on pairs: the chance of moving from `v` to `w` is
the chance of expressing a pair that takes `v` to `w`. -/
theorem skeletonKernel_singleton (β : ℝ) (v w : Pressure N M) :
    skeletonKernel β v {w}
      = (jumpPMF β v).toMeasure {p : Jump N M | express p.1 p.2 v = w} := by
  rw [skeletonKernel_apply,
    PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (measurableSet_pressure _)]
  rfl

/-- The realisations whose first expression takes `v` to `w` and has happened by time `t`,
with the second not yet. -/
def oneJumpSet (v w : Pressure N M) (t : ℝ) : Set (ℕ → Step N M) :=
  {ω | holdingTime 0 ω ≤ t ∧ express (ω 0).1.1 (ω 0).1.2 v = w ∧
    t < holdingTime 0 ω + holdingTime 1 ω}

/-- The same event, read on the first step and the rest of the realisation separately. -/
def oneJumpPairs (v w : Pressure N M) (t : ℝ) : Set (Step N M × (ℕ → Step N M)) :=
  {x | x.1.2 ≤ t ∧ express x.1.1.1 x.1.1.2 v = w ∧ t < x.1.2 + holdingTime 0 x.2}

omit [NeZero N] [NeZero M] in
theorem oneJumpSet_eq_preimage (v w : Pressure N M) (t : ℝ) :
    oneJumpSet v w t = {ω | (ω 0, shiftStepPath ω) ∈ oneJumpPairs v w t} := by
  rfl

omit [NeZero N] [NeZero M] in
theorem measurableSet_oneJumpPairs (v w : Pressure N M) (t : ℝ) :
    MeasurableSet (oneJumpPairs v w t) := by
  have h1 : Measurable fun x : Step N M × (ℕ → Step N M) => x.1.2 :=
    measurable_snd.comp measurable_fst
  have h2 : Measurable fun x : Step N M × (ℕ → Step N M) => x.1.1 :=
    measurable_fst.comp measurable_fst
  have h3 : Measurable fun x : Step N M × (ℕ → Step N M) => holdingTime 0 x.2 :=
    (measurable_holdingTime 0).comp measurable_snd
  have h4 : Measurable fun x : Step N M × (ℕ → Step N M) => x.1.2 + holdingTime 0 x.2 :=
    h1.add h3
  have hset : oneJumpPairs v w t
      = ((fun x : Step N M × (ℕ → Step N M) => x.1.2) ⁻¹' Set.Iic t)
        ∩ (((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹'
              {p : Jump N M | express p.1 p.2 v = w})
          ∩ ((fun x : Step N M × (ℕ → Step N M) => x.1.2 + holdingTime 0 x.2) ⁻¹'
              Set.Ioi t)) := rfl
  rw [hset]
  exact (h1 measurableSet_Iic).inter
    ((h2 (DiscreteMeasurableSpace.forall_measurableSet _)).inter (h4 measurableSet_Ioi))

/-- **Exactly one jump, from below.**  The first expression takes `v` to `w` and happens by
time `t`, and the second has not happened by then; the two clocks are independent, so the mass
is at least `K (v, w) e^{-q(w)t} (1 - e^{-q(v)t})`. -/
theorem le_ctsPathMeasure_oneJumpSet (β : ℝ) (v w : Pressure N M) {t : ℝ} (ht : 0 ≤ t) :
    skeletonKernel β v {w} * ENNReal.ofReal (Real.exp (-(totalRate β w * t)))
        * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t)))
      ≤ ctsPathMeasure β v (oneJumpSet v w t) := by
  set P : Set (Jump N M) := {p : Jump N M | express p.1 p.2 v = w} with hP
  set R : Set (Step N M) := P ×ˢ Set.Icc 0 t with hR
  have hRmeas : MeasurableSet R :=
    (DiscreteMeasurableSpace.forall_measurableSet P).prod measurableSet_Icc
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(totalRate β w * t))) with hc
  have hstep : stepLaw β v R
      = (jumpPMF β v).toMeasure P * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t))) := by
    have : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
      isProbabilityMeasure_expMeasure (totalRate_pos β v)
    rw [hR, stepLaw, Measure.prod_prod, expMeasure_Icc_zero (totalRate_pos β v) ht]
  have hpt : ∀ z : Step N M, Set.indicator R (fun _ => c) z
      ≤ ctsPathMeasure β (express z.1.1 z.1.2 v) {ω' | (z, ω') ∈ oneJumpPairs v w t} := by
    intro z
    by_cases hz : z ∈ R
    · obtain ⟨hzP, hz0, hzt⟩ : z.1 ∈ P ∧ 0 ≤ z.2 ∧ z.2 ≤ t := ⟨hz.1, hz.2.1, hz.2.2⟩
      have hexp : express z.1.1 z.1.2 v = w := hzP
      have hslice : {ω' : ℕ → Step N M | (z, ω') ∈ oneJumpPairs v w t}
          = {ω' | t - z.2 < holdingTime 0 ω'} := by
        ext ω'
        simp only [oneJumpPairs, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨-, -, h⟩; linarith
        · intro h; exact ⟨hzt, hexp, by linarith⟩
      rw [Set.indicator_of_mem hz, hslice, hexp,
        ctsPathMeasure_lt_holdingTime β w (by linarith)]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have := totalRate_pos β w
      nlinarith
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  calc skeletonKernel β v {w} * c * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t)))
      = c * stepLaw β v R := by
        rw [hstep, skeletonKernel_singleton]
        ring
    _ = ∫⁻ z, Set.indicator R (fun _ => c) z ∂(stepLaw β v) :=
        (lintegral_indicator_const hRmeas c).symm
    _ ≤ ∫⁻ z, ctsPathMeasure β (express z.1.1 z.1.2 v)
          {ω' | (z, ω') ∈ oneJumpPairs v w t} ∂(stepLaw β v) := lintegral_mono hpt
    _ = ctsPathMeasure β v (oneJumpSet v w t) := by
        rw [oneJumpSet_eq_preimage,
          ctsPathMeasure_firstStep_apply β v (measurableSet_oneJumpPairs v w t)]

/-- **The transition kernel from below.**  By time `t` either nothing has happened --- which
leaves the process at `v`, and counts only when `w = v` --- or exactly one expression has and
it took `v` to `w`.  The two events are disjoint, so their masses add.

This is the only thing the argument uses about `P_t`, and it needs no identity: the jump
counter is read off the first two holding times, whatever the later ones do. -/
theorem le_transitionKernel_singleton (β : ℝ) (v w : Pressure N M) {t : ℝ} (ht : 0 ≤ t) :
    (if v = w then ENNReal.ofReal (Real.exp (-(totalRate β v * t))) else 0)
        + skeletonKernel β v {w} * ENNReal.ofReal (Real.exp (-(totalRate β w * t)))
          * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t)))
      ≤ transitionKernel β t v {w} := by
  classical
  set G : Set (ℕ → Step N M) := {ω | ∀ n, 0 < holdingTime n ω} with hGdef
  have hGmeas : MeasurableSet G := by
    rw [hGdef, show {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}
        = ⋂ n, {ω | 0 < holdingTime n ω} from by ext ω; simp]
    exact MeasurableSet.iInter fun n => (measurable_holdingTime n) measurableSet_Ioi
  have hGnull : ctsPathMeasure β v Gᶜ = 0 := by
    rw [show Gᶜ = {ω : ℕ → Step N M | ∃ n, holdingTime n ω ≤ 0} from by
      ext ω; simp [hGdef, not_forall, not_lt]]
    exact ctsPathMeasure_exists_holdingTime_nonpos β v
  have hconull : ∀ S : Set (ℕ → Step N M),
      ctsPathMeasure β v (S ∩ G) = ctsPathMeasure β v S := by
    intro S
    have h := measure_inter_add_sdiff (μ := ctsPathMeasure β v) S hGmeas
    rwa [measure_mono_null (Set.sdiff_subset_compl S G) hGnull, add_zero] at h
  have hpre : transitionKernel β t v {w} = ctsPathMeasure β v (process v t ⁻¹' {w}) := by
    rw [transitionKernel_apply,
      Measure.map_apply (measurable_process v t) (measurableSet_pressure _)]
  have hBsub : oneJumpSet v w t ∩ G ⊆ process v t ⁻¹' {w} := by
    rintro ω ⟨⟨h0, hexp, h1⟩, hG⟩
    show process v t ω = w
    rw [process_eq_of_one_jump v hG h0 h1]
    exact hexp
  have hmeasB : MeasurableSet (oneJumpSet v w t ∩ G) := by
    rw [oneJumpSet_eq_preimage]
    exact (((measurable_pi_apply 0).prodMk measurable_shiftStepPath)
      (measurableSet_oneJumpPairs v w t)).inter hGmeas
  have hBle : ctsPathMeasure β v (oneJumpSet v w t) ≤ transitionKernel β t v {w} := by
    rw [hpre, ← hconull (oneJumpSet v w t)]
    exact measure_mono hBsub
  by_cases hvw : v = w
  · subst hvw
    have hdisj : Disjoint ({ω : ℕ → Step N M | t < holdingTime 0 ω} ∩ G)
        (oneJumpSet v v t ∩ G) := by
      rw [Set.disjoint_left]
      rintro ω ⟨hA, -⟩ ⟨⟨h0, -, -⟩, -⟩
      exact absurd h0 (not_le.2 hA)
    have hunion : ({ω : ℕ → Step N M | t < holdingTime 0 ω} ∩ G) ∪ (oneJumpSet v v t ∩ G)
        ⊆ process v t ⁻¹' {v} := by
      refine Set.union_subset (fun ω hω => ?_) hBsub
      show process v t ω = v
      exact process_eq_of_lt_holdingTime v hω.2 ht hω.1
    rw [if_pos rfl, hpre]
    refine le_trans (add_le_add le_rfl (le_ctsPathMeasure_oneJumpSet β v v ht)) ?_
    rw [← ctsPathMeasure_lt_holdingTime β v ht, ← hconull {ω | t < holdingTime 0 ω},
      ← hconull (oneJumpSet v v t), ← measure_union hdisj hmeasB]
    exact measure_mono hunion
  · rw [if_neg hvw, zero_add]
    exact le_trans (le_ctsPathMeasure_oneJumpSet β v w ht) hBle

end Bound

end SocialNetwork
