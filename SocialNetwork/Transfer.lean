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
* `SocialNetwork.bind_skeletonKernel_le_rateMeasure` — `νK ≤ ν` for `ν = q · μ`.
* `SocialNetwork.invariant_rateMeasure` — the correspondence itself, in the direction
  equation (13) consumes: `q_β · μ` is a finite invariant measure of the skeleton.
* `SocialNetwork.invariantCts_eq_of_invariantSkeleton` — **equation (13)**.
* `SocialNetwork.eq_of_invariantCts` — **Theorem 1.2, the uniqueness half**, which equation
  (13) gives at once.  Existence is the converse of the correspondence and is not proved
  here.
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

/-! ### From the process to the skeleton

Feeding the bound into the invariance equation, discarding every path with two jumps or more
and keeping finitely many starting matrices at a time leaves an inequality between real
numbers.  Dividing it by `t` and letting `t → 0` turns the two exponentials into the jump
rates, which is `ν ≥ νK` for `ν = q · μ`. -/

section Transfer

/-- **The invariance equation, truncated.**  Only the paths that have made no jump, or exactly
one and into `w`, are kept, and only finitely many starting matrices. -/
theorem finsetSum_le_of_invariantCts (β : ℝ) {μ : Measure (Pressure N M)}
    (hμ : IsInvariantCts β μ) (w : Pressure N M) (F : Finset (Pressure N M)) {t : ℝ}
    (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-(totalRate β w * t))) * μ {w}
        + ∑ v ∈ F, skeletonKernel β v {w}
            * ENNReal.ofReal (Real.exp (-(totalRate β w * t)))
            * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t))) * μ {v}
      ≤ μ {w} := by
  classical
  have hterm : ∀ v : Pressure N M,
      (if v = w then ENNReal.ofReal (Real.exp (-(totalRate β v * t))) else 0) * μ {v}
          + skeletonKernel β v {w} * ENNReal.ofReal (Real.exp (-(totalRate β w * t)))
            * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t))) * μ {v}
        ≤ transitionKernel β t v {w} * μ {v} := by
    intro v
    rw [← add_mul]
    exact mul_le_mul_left (le_transitionKernel_singleton β v w ht) _
  have hfirst : ∑' v : Pressure N M,
      (if v = w then ENNReal.ofReal (Real.exp (-(totalRate β v * t))) else 0) * μ {v}
        = ENNReal.ofReal (Real.exp (-(totalRate β w * t))) * μ {w} := by
    refine tsum_eq_single w (fun v hv => by rw [if_neg hv, zero_mul]) |>.trans ?_
    rw [if_pos rfl]
  conv_rhs => rw [measure_singleton_of_invariant (transitionKernel β t) (hμ t ht) w]
  refine le_trans ?_ (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_add, hfirst]
  exact add_le_add le_rfl (ENNReal.sum_le_tsum F)

/-! #### Two elementary bounds on `1 - e^{-x}`

Both are `1 + x ≤ e^x`, which is where the jump rate comes back out of the exponential as
`t → 0`. -/

theorem one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

theorem mul_exp_neg_le_one_sub_exp_neg (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have hpos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hmul : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h hpos.le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
  nlinarith

/-- **`νK ≤ ν` at one point.**  For `ν = q · μ` with `μ` invariant for the process, the mass
`ν` gives `w` is at least what the skeleton sends there from any finite set of matrices. -/
theorem finsetSum_rate_le (β : ℝ) {μ : Measure (Pressure N M)} [IsProbabilityMeasure μ]
    (hμ : IsInvariantCts β μ) (w : Pressure N M) (F : Finset (Pressure N M)) :
    ∑ v ∈ F, ENNReal.ofReal (totalRate β v) * skeletonKernel β v {w} * μ {v}
      ≤ ENNReal.ofReal (totalRate β w) * μ {w} := by
  classical
  set a : ℝ := totalRate β w with ha
  set ρ : ℝ := ∑ u ∈ F, totalRate β u with hρ
  set m : Pressure N M → ℝ := fun v => (μ {v}).toReal with hm
  set k : Pressure N M → ℝ := fun v => (skeletonKernel β v {w}).toReal with hk
  set S₀ : ℝ := ∑ v ∈ F, totalRate β v * k v * m v with hS₀
  have hmnn : ∀ v, 0 ≤ m v := fun v => ENNReal.toReal_nonneg
  have hknn : ∀ v, 0 ≤ k v := fun v => ENNReal.toReal_nonneg
  have hρle : ∀ v ∈ F, totalRate β v ≤ ρ := by
    intro v hv
    rw [hρ]
    exact Finset.single_le_sum (fun u _ => (totalRate_pos β u).le) hv
  -- the real form of the truncated invariance equation
  have hreal : ∀ t : ℝ, 0 ≤ t →
      Real.exp (-(a * t)) * m w
          + ∑ v ∈ F, k v * Real.exp (-(a * t)) * (1 - Real.exp (-(totalRate β v * t))) * m v
        ≤ m w := by
    intro t ht
    have h := finsetSum_le_of_invariantCts β hμ w F ht
    have hfin : ∀ v : Pressure N M, skeletonKernel β v {w}
        * ENNReal.ofReal (Real.exp (-(a * t)))
        * ENNReal.ofReal (1 - Real.exp (-(totalRate β v * t))) * μ {v} ≠ ∞ := by
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
        have : Real.exp (-(totalRate β v * t)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [totalRate_pos β v])
        linarith)]
  -- divide by `t` and read off the rates
  have key : ∀ t : ℝ, 0 < t → Real.exp (-((a + ρ) * t)) * S₀ ≤ a * m w := by
    intro t ht
    have h := hreal t ht.le
    have hupper : ∑ v ∈ F,
        k v * Real.exp (-(a * t)) * (1 - Real.exp (-(totalRate β v * t))) * m v
          ≤ m w * (a * t) := by
      have h1 : 1 - Real.exp (-(a * t)) ≤ a * t := one_sub_exp_neg_le _
      nlinarith [hmnn w]
    have hlower : Real.exp (-((a + ρ) * t)) * S₀ * t
        ≤ ∑ v ∈ F, k v * Real.exp (-(a * t)) * (1 - Real.exp (-(totalRate β v * t))) * m v := by
      rw [hS₀, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun v hv => ?_
      have hrv : (0 : ℝ) < totalRate β v := totalRate_pos β v
      have hexp : Real.exp (-(ρ * t)) ≤ Real.exp (-(totalRate β v * t)) :=
        Real.exp_le_exp.2 (by nlinarith [hρle v hv])
      have hstep : totalRate β v * t * Real.exp (-(totalRate β v * t))
          ≤ 1 - Real.exp (-(totalRate β v * t)) := by
        have := mul_exp_neg_le_one_sub_exp_neg (totalRate β v * t)
        simpa using this
      have hsplit : Real.exp (-((a + ρ) * t))
          = Real.exp (-(a * t)) * Real.exp (-(ρ * t)) := by
        rw [← Real.exp_add]; ring_nf
      have hkm : 0 ≤ k v * m v := mul_nonneg (hknn v) (hmnn v)
      have hpe : (0 : ℝ) < Real.exp (-(a * t)) := Real.exp_pos _
      have hinner : totalRate β v * t * Real.exp (-(ρ * t))
          ≤ 1 - Real.exp (-(totalRate β v * t)) := by
        have h1 : totalRate β v * t * Real.exp (-(ρ * t))
            ≤ totalRate β v * t * Real.exp (-(totalRate β v * t)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hrv.le ht.le)
        linarith [hstep]
      have hfac : 0 ≤ Real.exp (-(a * t)) * (k v * m v) := mul_nonneg hpe.le hkm
      rw [hsplit]
      calc Real.exp (-(a * t)) * Real.exp (-(ρ * t)) * (totalRate β v * k v * m v) * t
          = Real.exp (-(a * t)) * (k v * m v)
              * (totalRate β v * t * Real.exp (-(ρ * t))) := by ring
        _ ≤ Real.exp (-(a * t)) * (k v * m v)
              * (1 - Real.exp (-(totalRate β v * t))) :=
            mul_le_mul_of_nonneg_left hinner hfac
        _ = k v * Real.exp (-(a * t)) * (1 - Real.exp (-(totalRate β v * t))) * m v := by ring
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
  have hfinL : ∑ v ∈ F, ENNReal.ofReal (totalRate β v) * skeletonKernel β v {w} * μ {v} ≠ ∞ :=
    (ENNReal.sum_ne_top).2 fun v _ =>
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (measure_ne_top _ _)
  have hfinR : ENNReal.ofReal (totalRate β w) * μ {w} ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  refine (ENNReal.toReal_le_toReal hfinL hfinR).1 ?_
  rw [ENNReal.toReal_sum fun v _ =>
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (measure_ne_top _ _),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (totalRate_pos β w).le]
  refine le_trans (le_of_eq ?_) hS₀le
  rw [hS₀]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (totalRate_pos β v).le]

/-! #### The measure `q · μ`

Weighting `μ` by the jump rate turns the inequality above into a statement about measures:
`ν K ≤ ν`.  Two small facts about measures on a countable space are needed to say it, and
neither is in Mathlib in this form. -/

/-- Domination at the points is domination. -/
theorem le_of_forall_singleton_le {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {μ ν : Measure α} (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  refine Measure.le_iff.2 fun s hs => ?_
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  conv_rhs => rw [← Measure.sum_smul_dirac ν]
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  refine ENNReal.tsum_le_tsum fun a => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left (h a) _

/-- Agreement at the points is equality. -/
theorem ext_of_forall_singleton {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {μ ν : Measure α} (h : ∀ x, μ {x} = ν {x}) : μ = ν :=
  le_antisymm (le_of_forall_singleton_le fun x => (h x).le)
    (le_of_forall_singleton_le fun x => (h x).ge)

/-- One step of a kernel is monotone in the measure it is applied to. -/
theorem bind_mono {α : Type*} [MeasurableSpace α] {μ ν : Measure α} (κ : Kernel α α)
    (h : μ ≤ ν) : μ.bind κ ≤ ν.bind κ := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  exact lintegral_mono' h le_rfl

/-- The measure `ν = q_β · μ` that equation (13) inverts. -/
noncomputable def rateMeasure (β : ℝ) (μ : Measure (Pressure N M)) : Measure (Pressure N M) :=
  μ.withDensity fun v => ENNReal.ofReal (totalRate β v)

omit [NeZero N] [NeZero M] in
@[simp]
theorem rateMeasure_singleton (β : ℝ) (μ : Measure (Pressure N M)) (w : Pressure N M) :
    rateMeasure β μ {w} = ENNReal.ofReal (totalRate β w) * μ {w} := by
  rw [rateMeasure, withDensity_apply _ (measurableSet_singleton w), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, mul_comm]

omit [NeZero N] [NeZero M] in
theorem rateMeasure_compl_stateSet (β : ℝ) {μ : Measure (Pressure N M)}
    (hμ : IsCarriedByState μ) : rateMeasure β μ (stateSet N M)ᶜ = 0 := by
  rw [rateMeasure, withDensity_apply _ (measurableSet_pressure _),
    Measure.restrict_eq_zero.2 hμ, lintegral_zero_measure]

/-- **`νK ≤ ν`.**  The skeleton sends `ν = q_β · μ` to at most itself, at every matrix. -/
theorem bind_skeletonKernel_le_rateMeasure (β : ℝ) {μ : Measure (Pressure N M)}
    [IsProbabilityMeasure μ] (hμ : IsInvariantCts β μ) :
    (rateMeasure β μ).bind (skeletonKernel β) ≤ rateMeasure β μ := by
  refine le_of_forall_singleton_le fun w => ?_
  rw [bind_apply_singleton, rateMeasure_singleton, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  refine le_trans (le_of_eq ?_) (finsetSum_rate_le β hμ w F)
  exact Finset.sum_congr rfl fun v _ => by rw [rateMeasure_singleton]; ring

/-! #### The minorisation closes the argument

`νK ≤ ν` on its own does not make `ν` finite, and equation (13) needs it to be.  The
minorisation of p. 15 supplies it: iterating the inequality gives `ν {l} ≥ c · ν (S)`, and the
left-hand side is finite because the jump rate at `l` is.  Finiteness then turns the
inequality into an equality, the two sides having the same total mass. -/

theorem bind_iterateKernel_le {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {ν : Measure α} {κ : Kernel α α} [IsSFiniteKernel κ]
    (h : ν.bind κ ≤ ν) : ∀ n : ℕ, ν.bind (iterateKernel κ n) ≤ ν
  | 0 => by
      rw [iterateKernel]
      exact le_of_eq Measure.id_comp
  | n + 1 => by
      rw [iterateKernel, ← Measure.comp_assoc]
      exact le_trans (bind_mono κ (bind_iterateKernel_le h n)) h

/-- A measure dominated by another of the same finite total mass is that measure. -/
theorem eq_of_le_of_univ_eq {α : Type*} [MeasurableSpace α] {ρ ν : Measure α} (hle : ρ ≤ ν)
    (huniv : ρ Set.univ = ν Set.univ) (hfin : ν Set.univ ≠ ∞) : ρ = ν := by
  refine Measure.ext fun s hs => ?_
  have h2 : ρ sᶜ ≤ ν sᶜ := Measure.le_iff'.1 hle sᶜ
  have e1 : ρ s + ρ sᶜ = ρ Set.univ := measure_add_measure_compl hs
  have e2 : ν s + ν sᶜ = ν Set.univ := measure_add_measure_compl hs
  have hfc : ν sᶜ ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (Set.subset_univ _))
  refine le_antisymm (Measure.le_iff'.1 hle s) ?_
  have hadd : ν s + ν sᶜ ≤ ρ s + ν sᶜ := by
    rw [e2, ← huniv, ← e1]
    exact add_le_add le_rfl h2
  exact (ENNReal.add_le_add_iff_right hfc).1 hadd

/-- **`ν = q_β · μ` has finite total mass.** -/
theorem rateMeasure_univ_ne_top (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Measure (Pressure N M)} [IsProbabilityMeasure μ] (hμS : IsCarriedByState μ)
    (hμ : IsInvariantCts β μ) : rateMeasure β μ Set.univ ≠ ∞ := by
  classical
  set ν := rateMeasure β μ with hν
  set o : Opinion M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ with ho
  set c : ℝ≥0∞ := ENNReal.ofReal (zeta N M β) ^ N
    * ENNReal.ofReal (stepFloor N M β (greedyBound N M + (N : ℤ) * ((M : ℤ) - 1))) ^ N with hc
  have hcpos : 0 < c := by
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · exact (ENNReal.ofReal_pos.2 (zeta_pos N M β)).ne'
    · exact (ENNReal.ofReal_pos.2 (stepFloor_pos N M β _)).ne'
  have hiter := bind_iterateKernel_le (bind_skeletonKernel_le_rateMeasure β hμ) (N + N)
  have hS : ν Set.univ = ν (stateSet N M) := by
    have h := measure_add_measure_compl (μ := ν) (measurableSet_pressure (stateSet N M))
    rw [hν, rateMeasure_compl_stateSet β hμS, add_zero] at h
    exact h.symm
  have hle : c * ν Set.univ ≤ ν {ladderOf N o} := by
    refine le_trans ?_ (Measure.le_iff'.1 hiter {ladderOf N o})
    rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
    calc c * ν Set.univ = ∫⁻ _ in stateSet N M, c ∂ν := by rw [setLIntegral_const, hS]
      _ ≤ ∫⁻ v in stateSet N M,
            iterateKernel (skeletonKernel β) (N + N) v {ladderOf N o} ∂ν :=
          setLIntegral_mono (Kernel.measurable_coe _ (measurableSet_singleton _))
            (fun v hv => minorisation_iterateKernel hM hβ o hv)
      _ ≤ ∫⁻ v, iterateKernel (skeletonKernel β) (N + N) v {ladderOf N o} ∂ν :=
          setLIntegral_le_lintegral _ _
  have hfin : ν {ladderOf N o} ≠ ∞ := by
    rw [hν, rateMeasure_singleton]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  intro htop
  rw [htop, ENNReal.mul_top hcpos.ne'] at hle
  exact hfin (top_le_iff.1 hle)

/-- **`q_β · μ` is invariant for the skeleton.**  This is the half of the equivalence quoted at
p. 18 that equation (13) needs, and the paper cites it rather than proving it. -/
theorem invariant_rateMeasure (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Measure (Pressure N M)} [IsProbabilityMeasure μ] (hμS : IsCarriedByState μ)
    (hμ : IsInvariantCts β μ) :
    Kernel.Invariant (skeletonKernel β) (rateMeasure β μ) := by
  have huniv : ((rateMeasure β μ).bind (skeletonKernel β)) Set.univ
      = rateMeasure β μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp
  exact eq_of_le_of_univ_eq (bind_skeletonKernel_le_rateMeasure β hμ) huniv
    (rateMeasure_univ_ne_top hM hβ hμS hμ)

/-! ### Equation (13) -/

/-- **Equation (13).**  For every `u ∈ S`,

```
μ^β (u) = (μ̃^β (u) / q_β (u)) / ∑_{v} μ̃^β (v) / q_β (v).
```

**Follows the paper's proof**, with the step it cites supplied:
`SocialNetwork.invariant_rateMeasure` is "a probability measure is invariant for the process
if and only if its product with the jump rate is invariant for the skeleton chain", in the
direction the display needs.  The normalising sum is finite by
`SocialNetwork.tsum_div_totalRate_le`, and `q_β · μ` has finite total mass by
`SocialNetwork.rateMeasure_univ_ne_top`; normalising it and appealing to
`SocialNetwork.existsUnique_invariantSkeleton` identifies it with `μ̃^β`, and the display is
that identification inverted.

The paper's `N ≥ 3` is not used, and neither is Theorem 1.1: see the header of this file. -/
theorem invariantCts_eq_of_invariantSkeleton (hM : 2 ≤ M) (_hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μ μskel : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ) (hμS : IsCarriedByState μ)
    (hμinv : IsInvariantCts β μ) (hs : IsProbabilityMeasure μskel)
    (hsS : IsCarriedByState μskel) (hsinv : Kernel.Invariant (skeletonKernel β) μskel)
    (v : Pressure N M) :
    μ {v} = (μskel {v} / ENNReal.ofReal (totalRate β v)) /
      ∑' w : Pressure N M, μskel {w} / ENNReal.ofReal (totalRate β w) := by
  classical
  have hμprob : IsProbabilityMeasure μ := hμ
  have hsprob : IsProbabilityMeasure μskel := hs
  have hq0 : ∀ w : Pressure N M, ENNReal.ofReal (totalRate β w) ≠ 0 :=
    fun w => (ENNReal.ofReal_pos.2 (totalRate_pos β w)).ne'
  set ν := rateMeasure β μ with hν
  set Z := ν Set.univ with hZ
  have hZtop : Z ≠ ∞ := rateMeasure_univ_ne_top hM hβ hμS hμinv
  have hZ0 : Z ≠ 0 := by
    intro h0
    have hall : ∀ w : Pressure N M, μ {w} = 0 := by
      intro w
      have hle : ν {w} ≤ Z := measure_mono (Set.subset_univ _)
      rw [h0, le_zero_iff, hν, rateMeasure_singleton] at hle
      rcases mul_eq_zero.1 hle with h | h
      · exact absurd h (hq0 w)
      · exact h
    have hone := tsum_measure_singleton μ
    rw [tsum_congr hall] at hone
    simp at hone
  set ν' := Z⁻¹ • ν with hν'
  have hν'apply : ∀ w : Pressure N M, ν' {w} = Z⁻¹ * ν {w} := by
    intro w
    rw [hν', Measure.smul_apply, smul_eq_mul]
  have : IsProbabilityMeasure ν' := by
    refine ⟨?_⟩
    rw [hν', Measure.smul_apply, smul_eq_mul, ← hZ, ENNReal.inv_mul_cancel hZ0 hZtop]
  have hν'S : ν' (stateSet N M)ᶜ = 0 := by
    rw [hν', Measure.smul_apply, smul_eq_mul, hν, rateMeasure_compl_stateSet β hμS, mul_zero]
  have hbase : ν.bind (skeletonKernel β) = ν := invariant_rateMeasure hM hβ hμS hμinv
  have hν'inv : Kernel.Invariant (skeletonKernel β) ν' := by
    have hsing : ∀ y : Pressure N M, (ν'.bind (skeletonKernel β)) {y} = ν' {y} := by
      intro y
      rw [bind_apply_singleton]
      have hcong : ∀ x : Pressure N M, skeletonKernel β x {y} * ν' {x}
          = Z⁻¹ * (skeletonKernel β x {y} * ν {x}) := by
        intro x
        rw [hν'apply x, ← mul_assoc, ← mul_assoc, mul_comm (skeletonKernel β x {y}) Z⁻¹]
      rw [tsum_congr hcong, ENNReal.tsum_mul_left, ← bind_apply_singleton, hbase, hν'apply y]
    show ν'.bind (skeletonKernel β) = ν'
    exact ext_of_forall_singleton hsing
  have heq : ν' = μskel := eq_of_invariant_skeletonKernel hM hβ hν'S hsS hν'inv hsinv
  have hskel : ∀ w : Pressure N M,
      μskel {w} = Z⁻¹ * μ {w} * ENNReal.ofReal (totalRate β w) := by
    intro w
    rw [← heq, hν'apply w, hν, rateMeasure_singleton]
    ring
  have hdiv : ∀ w : Pressure N M,
      μskel {w} / ENNReal.ofReal (totalRate β w) = Z⁻¹ * μ {w} := by
    intro w
    rw [hskel w, div_eq_mul_inv, mul_assoc,
      ENNReal.mul_inv_cancel (hq0 w) ENNReal.ofReal_ne_top, mul_one]
  have htsum : ∑' w : Pressure N M, μskel {w} / ENNReal.ofReal (totalRate β w) = Z⁻¹ := by
    rw [tsum_congr hdiv, ENNReal.tsum_mul_left, tsum_measure_singleton μ, mul_one]
  rw [hdiv v, htsum, div_eq_mul_inv, inv_inv, mul_comm Z⁻¹ (μ {v}), mul_assoc,
    ENNReal.inv_mul_cancel hZ0 hZtop, mul_one]

/-- **Theorem 1.2, the uniqueness half.**  The process has at most one invariant probability
measure carried by `S`: equation (13) writes both of them in terms of `μ̃^β`, which
`SocialNetwork.existsUnique_invariantSkeleton` says is unique.

Existence is the converse direction of the correspondence, and is not proved here; see the
node `thm1-2` of the blueprint. -/
theorem eq_of_invariantCts (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μ ν : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ) (hμS : IsCarriedByState μ)
    (hμinv : IsInvariantCts β μ) (hν : IsProbabilityMeasure ν) (hνS : IsCarriedByState ν)
    (hνinv : IsInvariantCts β ν) : μ = ν := by
  obtain ⟨μskel, ⟨hsprob, hsS, hsinv⟩, -⟩ := existsUnique_invariantSkeleton (N := N) (M := M) hM hβ
  refine ext_of_forall_singleton fun v => ?_
  rw [invariantCts_eq_of_invariantSkeleton hM hN hβ hμ hμS hμinv hsprob hsS hsinv v,
    invariantCts_eq_of_invariantSkeleton hM hN hβ hν hνS hνinv hsprob hsS hsinv v]

end Transfer

end SocialNetwork
