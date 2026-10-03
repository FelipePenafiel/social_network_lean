/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Graphical
import SocialNetwork.Transfer

/-!
# Theorem 1.2: existence, and the correspondence of p. 18 in full

`SocialNetwork.Transfer` proves one direction of the equivalence the paper cites at p. 18,

> For a non-explosive process, a probability measure is invariant for `(U_t^{β,u})_t` if and
> only if its product with the jump rate is invariant for the skeleton chain,

the direction equation (13) consumes, and with it the uniqueness half of Theorem 1.2.  This
file proves the other direction, and with it existence.

## The argument

Write `q` for the jump rate, `K` for the skeleton kernel and `μ` for a probability measure
carried by `S` with `(q · μ) K ≤ q · μ`.  The aim is `μ P_t ≤ μ` at every matrix: both sides
are probability measures, so the inequality is an equality.

Decompose `P_t` along the number of expressions made by time `t`,
`P_t (v, w) = ∑_n P^{(n)}_t (v, w)`.  This is where **Theorem 1.1** enters, and it has to: the
decomposition misses exactly the realisations that explode before `t`.  For an explosive chain
`μ` need not be invariant at all.

Restarting at the first expression gives `P^{(n+1)} = 𝓑 P^{(n)}`, where `𝓑` averages over the
first step: the pair is drawn from `K (v, ·)` and the holding time from `Exp (q (v))`,
independently.  This is what the construction of the process makes available.  The induction
below wants the other end instead, `P^{(n+1)} = 𝓛 P^{(n)}`, where `𝓛` decomposes along the
*last* expression before `t`:

```
(𝓛 F) (v, w, t) = ∑_x q(x) K (x, w) ∫_0^t e^{-q(w) r} F (v, x, t - r) dr.
```

The two operators **commute**, by Tonelli alone: each averages over an independent time and
the two time shifts add.  They agree on `P^{(0)}`, by the reflection `r ↦ t - r`.  So
`P^{(n+1)} = 𝓛 P^{(n)}` for every `n`.

With `𝓛` the bound is an induction on the number of expressions.  If
`∑_v μ (v) ∑_{n < K} P^{(n)}_s (v, ·) ≤ μ` at every time `s ≥ 0`, then one more term costs

```
μ (w) e^{-q(w) t} + ∑_x q(x) μ (x) K (x, w) ∫_0^t e^{-q(w) r} dr
  ≤ μ (w) e^{-q(w) t} + q(w) μ (w) (1 - e^{-q(w) t}) / q(w) = μ (w).
```

## What this does not need

**Not a forward equation for the semigroup.**  `𝓛` is the forward equation's integral form for
one fixed number of jumps, and it is obtained from `𝓑` by Tonelli, not by differentiating
`P_t`.

**Not Chapman–Kolmogorov.**  Nothing composes `P_s` with `P_t`.

## Main statements

* `SocialNetwork.firstStep_lastStep` — the two operators commute.
* `SocialNetwork.nJump_succ_eq_lastStep` — `P^{(n+1)} = 𝓛 P^{(n)}`.
* `SocialNetwork.transitionKernel_le_tsum_nJump` — the decomposition, from Theorem 1.1.
* `SocialNetwork.invariantCts_of_bind_rateMeasure_le` — the converse of
  `SocialNetwork.invariant_rateMeasure`.
* `SocialNetwork.isInvariantCts_iff` — the correspondence of p. 18, both directions.
* `SocialNetwork.existsUnique_invariantCts` — **Theorem 1.2**.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### The holding time, as a survival function -/

section Survival

/-- `e^{-q(v) t}` for `t ≥ 0`, and `0` before time `0`: the chance that the clock at `v` has not
rung by time `t`, together with the convention that nothing happens before time `0`. -/
noncomputable def survival (β : ℝ) (v : Pressure N M) (t : ℝ) : ℝ≥0∞ :=
  Set.indicator (Set.Ici 0) (fun s => ENNReal.ofReal (Real.exp (-(totalRate β v * s)))) t

omit [NeZero N] [NeZero M] in
theorem measurable_survival (β : ℝ) (v : Pressure N M) : Measurable (survival β v) := by
  refine Measurable.indicator ?_ measurableSet_Ici
  fun_prop

omit [NeZero N] [NeZero M] in
/-- The exponential density is the rate times the survival function. -/
theorem exponentialPDF_totalRate (β : ℝ) (v : Pressure N M) (s : ℝ) :
    exponentialPDF (totalRate β v) s = ENNReal.ofReal (totalRate β v) * survival β v s := by
  rw [exponentialPDF_eq, survival]
  by_cases hs : 0 ≤ s
  · rw [if_pos hs, Set.indicator_of_mem (Set.mem_Ici.2 hs),
      ENNReal.ofReal_mul (totalRate_nonneg β v)]
  · have hs' : s ∉ Set.Ici (0 : ℝ) := by simpa using hs
    rw [if_neg hs, Set.indicator_of_notMem hs', ENNReal.ofReal_zero, mul_zero]

omit [NeZero N] [NeZero M] in
/-- Integrating against the exponential law is integrating against its density. -/
theorem lintegral_expMeasure_totalRate (β : ℝ) (v : Pressure N M) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ s, f s ∂(expMeasure (totalRate β v))
      = ENNReal.ofReal (totalRate β v) * ∫⁻ s, survival β v s * f s := by
  rw [show expMeasure (totalRate β v)
      = volume.withDensity (exponentialPDF (totalRate β v)) from rfl,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_exponentialPDFReal (totalRate β v)).ennreal_ofReal hf,
    ← lintegral_const_mul _ ((measurable_survival β v).mul hf)]
  refine lintegral_congr fun s => ?_
  rw [Pi.mul_apply, exponentialPDF_totalRate, mul_assoc]

/-- **No mass is lost by time `t`.**  The clock at `w` has either not rung by `t`, or rung in
`[0, t]`; before time `0` neither term counts.  In the form the induction uses:
`e^{-q t} + q ∫_0^t e^{-q r} dr = 1` for `t ≥ 0`. -/
theorem survival_add_lintegral (β : ℝ) (w : Pressure N M) (t : ℝ) :
    survival β w t + ENNReal.ofReal (totalRate β w)
        * ∫⁻ r, survival β w r * Set.indicator (Set.Ici 0) 1 (t - r)
      = Set.indicator (Set.Ici 0) 1 t := by
  have hq := totalRate_pos β w
  have hind : Measurable fun r : ℝ => Set.indicator (Set.Ici (0 : ℝ)) (1 : ℝ → ℝ≥0∞) (t - r) :=
    (measurable_one.indicator measurableSet_Ici).comp (measurable_const.sub measurable_id)
  have hE : ENNReal.ofReal (totalRate β w)
        * ∫⁻ r, survival β w r * Set.indicator (Set.Ici 0) 1 (t - r)
      = expMeasure (totalRate β w) (Set.Iic t) := by
    rw [← lintegral_expMeasure_totalRate β w hind, ← lintegral_indicator_one measurableSet_Iic]
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
  · have h1 : Real.exp (-(totalRate β w * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [survival, Set.indicator_of_mem (Set.mem_Ici.2 ht), Set.indicator_of_mem (Set.mem_Ici.2 ht),
      expMeasure_Iic_of_nonneg hq ht, Pi.one_apply,
      ← ENNReal.ofReal_add (Real.exp_pos _).le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  · have hnull : expMeasure (totalRate β w) (Set.Iic t) = 0 :=
      measure_mono_null (Set.Iic_subset_Iic.2 (le_of_not_ge ht)) (expMeasure_Iic_zero hq)
    have ht' : t ∉ Set.Ici (0 : ℝ) := by simpa using ht
    rw [survival, Set.indicator_of_notMem ht', Set.indicator_of_notMem ht', hnull, zero_add]

end Survival

/-! ### Exactly `n` expressions by time `t`

`P^{(n)}_t (v, w)` is the chance, from `v`, of having made exactly `n` expressions by time `t`
and sitting at `w`.  Its events are read off the jump times directly, so they make sense
whether or not the realisation explodes later. -/

section Count

/-- The realisations that have made exactly `n` expressions by time `t` and sit at `w`. -/
def nJumpSet (v w : Pressure N M) (n : ℕ) (t : ℝ) : Set (ℕ → Step N M) :=
  {ω | jumpTime n ω ≤ t ∧ t < jumpTime (n + 1) ω ∧ (Trajectory.ofStepPath ω).state v n = w}

/-- The same events, at all times at once. -/
def nJumpGraph (v w : Pressure N M) (n : ℕ) : Set (ℝ × (ℕ → Step N M)) :=
  {x | x.2 ∈ nJumpSet v w n x.1}

theorem measurableSet_nJumpGraph (v w : Pressure N M) (n : ℕ) :
    MeasurableSet (nJumpGraph v w n) := by
  have h1 : Measurable fun x : ℝ × (ℕ → Step N M) => jumpTime n x.2 :=
    (measurable_jumpTime n).comp measurable_snd
  have h2 : Measurable fun x : ℝ × (ℕ → Step N M) => jumpTime (n + 1) x.2 :=
    (measurable_jumpTime (n + 1)).comp measurable_snd
  have h3 : Measurable fun x : ℝ × (ℕ → Step N M) => (Trajectory.ofStepPath x.2).state v n :=
    (measurable_state_ofStepPath v n).comp measurable_snd
  have hset : nJumpGraph v w n
      = {x : ℝ × (ℕ → Step N M) | jumpTime n x.2 ≤ x.1}
        ∩ ({x | x.1 < jumpTime (n + 1) x.2}
          ∩ ((fun x : ℝ × (ℕ → Step N M) => (Trajectory.ofStepPath x.2).state v n) ⁻¹' {w})) :=
    rfl
  rw [hset]
  exact (measurableSet_le h1 measurable_fst).inter
    ((measurableSet_lt measurable_fst h2).inter (h3 (measurableSet_singleton w)))

theorem measurableSet_nJumpSet (v w : Pressure N M) (n : ℕ) (t : ℝ) :
    MeasurableSet (nJumpSet v w n t) := by
  show MeasurableSet (Prod.mk t ⁻¹' nJumpGraph v w n)
  exact measurable_prodMk_left (measurableSet_nJumpGraph v w n)

/-- `P^{(n)}_t (v, w)`: the chance, from `v`, of having made exactly `n` expressions by time `t`
and sitting at `w`. -/
noncomputable def nJump (β : ℝ) (v w : Pressure N M) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ctsPathMeasure β v (nJumpSet v w n t)

theorem measurable_nJump (β : ℝ) (v w : Pressure N M) (n : ℕ) :
    Measurable (nJump β v w n) :=
  measurable_measure_prodMk_left (measurableSet_nJumpGraph v w n)

/-- **No expression by time `t`.** -/
theorem nJump_zero (β : ℝ) (v w : Pressure N M) (t : ℝ) :
    nJump β v w 0 t = if v = w then survival β v t else 0 := by
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl]
    by_cases ht : 0 ≤ t
    · have hset : nJumpSet v v 0 t = {ω | t < holdingTime 0 ω} := by
        ext ω
        simp [nJumpSet, ht, jumpTime_one]
      rw [nJump, hset, ctsPathMeasure_lt_holdingTime β v ht, survival,
        Set.indicator_of_mem (Set.mem_Ici.2 ht)]
    · have hset : nJumpSet v v 0 t = ∅ := by
        ext ω
        simp [nJumpSet, ht]
      have ht' : t ∉ Set.Ici (0 : ℝ) := by simpa using ht
      rw [nJump, hset, measure_empty, survival, Set.indicator_of_notMem ht']
  · rw [if_neg hvw]
    have hset : nJumpSet v w 0 t = ∅ := by
      ext ω
      simp [nJumpSet, hvw]
    rw [nJump, hset, measure_empty]

end Count

/-! ### Restarting at the first expression

The `(n+1)`-st jump time of a realisation is its first holding time plus the `n`-th jump time
of the rest, and the matrix it reaches is the one the rest reaches from the matrix the first
pair produced.  So `P^{(n+1)}` is `P^{(n)}` averaged over the first step. -/

section Restart

omit [NeZero N] [NeZero M] in
theorem jumpTime_succ_eq_shift (n : ℕ) (ω : ℕ → Step N M) :
    jumpTime (n + 1) ω = holdingTime 0 ω + jumpTime n (shiftStepPath ω) := by
  have hsum : ∑ k ∈ Finset.range n, holdingTime (k + 1) ω
      = ∑ k ∈ Finset.range n, holdingTime k (shiftStepPath ω) :=
    Finset.sum_congr rfl fun k _ => by
      show (ω (k + 1)).2 = (ω (1 + k)).2
      rw [add_comm]
  simp only [jumpTime]
  rw [Finset.sum_range_succ', hsum, add_comm]

omit [NeZero N] [NeZero M] in
theorem state_succ_eq_shift (v : Pressure N M) (n : ℕ) (ω : ℕ → Step N M) :
    (Trajectory.ofStepPath ω).state v (n + 1)
      = (Trajectory.ofStepPath (shiftStepPath ω)).state (express (ω 0).1.1 (ω 0).1.2 v) n := by
  rw [ofStepPath_shiftStepPath, ← state_one_ofStepPath v ω, ← Trajectory.state_add, add_comm]

/-- The event of `nJumpSet v w (n + 1) t`, read on the first step and the rest separately. -/
def nJumpPairs (v w : Pressure N M) (n : ℕ) (t : ℝ) : Set (Step N M × (ℕ → Step N M)) :=
  {x | x.2 ∈ nJumpSet (express x.1.1.1 x.1.1.2 v) w n (t - x.1.2)}

omit [NeZero N] [NeZero M] in
theorem nJumpSet_succ_eq_preimage (v w : Pressure N M) (n : ℕ) (t : ℝ) :
    nJumpSet v w (n + 1) t = {ω | (ω 0, shiftStepPath ω) ∈ nJumpPairs v w n t} := by
  ext ω
  have e1 := jumpTime_succ_eq_shift n ω
  have e2 := jumpTime_succ_eq_shift (n + 1) ω
  have e3 := state_succ_eq_shift v n ω
  simp only [holdingTime] at e1 e2
  simp only [nJumpSet, nJumpPairs, Set.mem_ofPred_eq, e3]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, h3⟩

theorem measurableSet_nJumpPairs (v w : Pressure N M) (n : ℕ) (t : ℝ) :
    MeasurableSet (nJumpPairs v w n t) := by
  have hset : nJumpPairs v w n t = ⋃ p : Jump N M,
      ((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹' {p})
        ∩ ((fun x : Step N M × (ℕ → Step N M) => (t - x.1.2, x.2)) ⁻¹'
            nJumpGraph (express p.1 p.2 v) w n) := by
    ext x
    simp only [nJumpPairs, nJumpGraph, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨x.1.1, rfl, h⟩
    · rintro ⟨p, rfl, h⟩
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun p => ?_
  refine ((measurable_fst.comp measurable_fst) (measurableSet_singleton p)).inter ?_
  exact ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    (measurableSet_nJumpGraph _ w n)

/-- **Restarting at the first expression**, on the step itself. -/
theorem nJump_succ (β : ℝ) (v w : Pressure N M) (n : ℕ) (t : ℝ) :
    nJump β v w (n + 1) t
      = ∫⁻ z, nJump β (express z.1.1 z.1.2 v) w n (t - z.2) ∂(stepLaw β v) := by
  rw [nJump, nJumpSet_succ_eq_preimage,
    ctsPathMeasure_firstStep_apply β v (measurableSet_nJumpPairs v w n t)]
  exact lintegral_congr fun z => rfl

/-- The first-step operator `𝓑`: the pair is drawn from the skeleton kernel and the holding time
from the exponential law of the current rate, independently. -/
noncomputable def firstStep (β : ℝ) (F : Pressure N M → Pressure N M → ℝ → ℝ≥0∞)
    (v w : Pressure N M) (t : ℝ) : ℝ≥0∞ :=
  ∑' u, skeletonKernel β v {u} * ∫⁻ s, F u w (t - s) ∂(expMeasure (totalRate β v))

/-- **`P^{(n+1)} = 𝓑 P^{(n)}`.**  The pair and the holding time of a step are independent, and
the matrix reached depends on the pair alone. -/
theorem nJump_succ_eq_firstStep (β : ℝ) (v w : Pressure N M) (n : ℕ) (t : ℝ) :
    nJump β v w (n + 1) t = firstStep β (fun u x s => nJump β u x n s) v w t := by
  have hE : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure (totalRate_pos β v)
  have hmeas : Measurable fun z : Jump N M × ℝ => nJump β (express z.1.1 z.1.2 v) w n (t - z.2) := by
    refine measurable_from_prod_countable_right fun p => ?_
    exact (measurable_nJump β (express p.1 p.2 v) w n).comp (measurable_const.sub measurable_id)
  have hg : Measurable fun u : Pressure N M =>
      ∫⁻ s, nJump β u w n (t - s) ∂(expMeasure (totalRate β v)) :=
    measurable_of_countable _
  have hmap : skeletonKernel β v
      = (jumpPMF β v).toMeasure.map (fun p : Jump N M => express p.1 p.2 v) := by
    rw [skeletonKernel_apply, PMF.toMeasure_map _ _ (measurable_of_countable _)]
  have hstep : ∫⁻ z, nJump β (express z.1.1 z.1.2 v) w n (t - z.2) ∂(stepLaw β v)
      = ∫⁻ u, ∫⁻ s, nJump β u w n (t - s) ∂(expMeasure (totalRate β v)) ∂(skeletonKernel β v) := by
    rw [stepLaw, lintegral_prod _ hmeas.aemeasurable, hmap,
      lintegral_map hg (measurable_of_countable _)]
  rw [nJump_succ, hstep, lintegral_countable', firstStep]
  exact tsum_congr fun u => mul_comm _ _

end Restart

/-! ### The last-step operator, and why it agrees with the first

`𝓛` decomposes along the last expression before `t`.  It averages over a time just as `𝓑`
does, but at the far end, and the two averages commute: that is Tonelli, the time shifts adding
in either order.  On `P^{(0)}` they agree by the reflection `r ↦ t - r`. -/

section LastStep

/-- The last-step operator `𝓛`: the last expression before `t` takes the process from `x` to `w`
at rate `q(x) K (x, w)`, and it then holds at `w` for the remaining time. -/
noncomputable def lastStep (β : ℝ) (F : Pressure N M → Pressure N M → ℝ → ℝ≥0∞)
    (v w : Pressure N M) (t : ℝ) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
    * ∫⁻ r, survival β w r * F v x (t - r)

/-- **`𝓑` and `𝓛` commute.**  Tonelli, three times: once for the two time integrals, twice to
take the sums over matrices outside. -/
theorem firstStep_lastStep (β : ℝ) {F : Pressure N M → Pressure N M → ℝ → ℝ≥0∞}
    (hF : ∀ u x, Measurable (F u x)) (v w : Pressure N M) (t : ℝ) :
    firstStep β (lastStep β F) v w t = lastStep β (firstStep β F) v w t := by
  set E := expMeasure (totalRate β v) with hEdef
  have hE : IsProbabilityMeasure E := isProbabilityMeasure_expMeasure (totalRate_pos β v)
  have hjoint : ∀ u x, Measurable fun p : ℝ × ℝ => survival β w p.2 * F u x (t - p.1 - p.2) :=
    fun u x => ((measurable_survival β w).comp measurable_snd).mul
      ((hF u x).comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  have hjoint' : ∀ u x, Measurable fun p : ℝ × ℝ => survival β w p.1 * F u x (t - p.1 - p.2) :=
    fun u x => ((measurable_survival β w).comp measurable_fst).mul
      ((hF u x).comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  -- the two time integrals, in either order
  have hswap : ∀ u x, ∫⁻ s, ∫⁻ r, survival β w r * F u x (t - s - r) ∂volume ∂E
      = ∫⁻ r, ∫⁻ s, survival β w r * F u x (t - r - s) ∂E ∂volume := by
    intro u x
    rw [lintegral_lintegral_swap (f := fun s r => survival β w r * F u x (t - s - r))
      (hjoint u x).aemeasurable]
    refine lintegral_congr fun r => lintegral_congr fun s => ?_
    rw [sub_sub, sub_sub, add_comm s r]
  have hL : ∀ u, ∫⁻ s, lastStep β F u w (t - s) ∂E
      = ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * ∫⁻ s, ∫⁻ r, survival β w r * F u x (t - s - r) ∂volume ∂E := by
    intro u
    have hm : ∀ x, Measurable fun s => ∫⁻ r, survival β w r * F u x (t - s - r) :=
      fun x => Measurable.lintegral_prod_right
        (f := fun s r : ℝ => survival β w r * F u x (t - s - r)) (hjoint u x)
    simp only [lastStep]
    rw [lintegral_tsum fun x => ((hm x).const_mul _).aemeasurable]
    exact tsum_congr fun x => lintegral_const_mul _ (hm x)
  have hR : ∀ x, ∫⁻ r, survival β w r * firstStep β F v x (t - r)
      = ∑' u, skeletonKernel β v {u}
          * ∫⁻ r, ∫⁻ s, survival β w r * F u x (t - r - s) ∂E ∂volume := by
    intro x
    have hJ : ∀ u, Measurable fun r => ∫⁻ s, F u x (t - r - s) ∂E := fun u =>
      Measurable.lintegral_prod_right (f := fun r s : ℝ => F u x (t - r - s))
        ((hF u x).comp ((measurable_const.sub measurable_fst).sub measurable_snd))
    have hK : ∀ u, Measurable fun r => ∫⁻ s, survival β w r * F u x (t - r - s) ∂E := fun u =>
      Measurable.lintegral_prod_right
        (f := fun r s : ℝ => survival β w r * F u x (t - r - s)) (hjoint' u x)
    simp only [firstStep]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum fun u => ((measurable_survival β w).mul ((hJ u).const_mul _)).aemeasurable]
    refine tsum_congr fun u => ?_
    have hpt : ∀ r, survival β w r * (skeletonKernel β v {u} * ∫⁻ s, F u x (t - r - s) ∂E)
        = skeletonKernel β v {u} * ∫⁻ s, survival β w r * F u x (t - r - s) ∂E := by
      intro r
      have hm : Measurable fun s => F u x (t - r - s) :=
        (hF u x).comp (measurable_const.sub measurable_id)
      rw [lintegral_const_mul _ hm]
      ring
    rw [lintegral_congr hpt, lintegral_const_mul _ (hK u)]
  calc firstStep β (lastStep β F) v w t
      = ∑' u, skeletonKernel β v {u} * ∫⁻ s, lastStep β F u w (t - s) ∂E := rfl
    _ = ∑' u, ∑' x, skeletonKernel β v {u} * (ENNReal.ofReal (totalRate β x)
          * skeletonKernel β x {w} * ∫⁻ s, ∫⁻ r, survival β w r * F u x (t - s - r) ∂volume ∂E) :=
        tsum_congr fun u => by rw [hL u, ENNReal.tsum_mul_left]
    _ = ∑' x, ∑' u, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * (skeletonKernel β v {u} * ∫⁻ r, ∫⁻ s, survival β w r * F u x (t - r - s) ∂E ∂volume) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun x => tsum_congr fun u => ?_
        rw [hswap u x]
        ring
    _ = lastStep β (firstStep β F) v w t := by
        simp only [lastStep]
        exact tsum_congr fun x => by rw [hR x, ENNReal.tsum_mul_left]

/-- **`𝓑` and `𝓛` agree on `P^{(0)}`.**  Both are `q(v) K (v, w) ∫_0^t e^{-q(v) s} e^{-q(w)(t-s)} ds`,
written once from each end of `[0, t]`. -/
theorem firstStep_nJump_zero (β : ℝ) (v w : Pressure N M) (t : ℝ) :
    firstStep β (fun u x s => nJump β u x 0 s) v w t
      = lastStep β (fun u x s => nJump β u x 0 s) v w t := by
  have hL : firstStep β (fun u x s => nJump β u x 0 s) v w t
      = skeletonKernel β v {w} * ∫⁻ s, survival β w (t - s) ∂(expMeasure (totalRate β v)) := by
    simp only [firstStep, nJump_zero]
    rw [tsum_eq_single w fun u hu => by simp [hu]]
    simp
  have hR : lastStep β (fun u x s => nJump β u x 0 s) v w t
      = ENNReal.ofReal (totalRate β v) * skeletonKernel β v {w}
          * ∫⁻ r, survival β w r * survival β v (t - r) := by
    simp only [lastStep, nJump_zero]
    rw [tsum_eq_single v fun x hx => by simp [Ne.symm hx]]
    simp
  have hreflect : ∫⁻ s, survival β v s * survival β w (t - s)
      = ∫⁻ r, survival β w r * survival β v (t - r) := by
    have h := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun r => survival β w r * survival β v (t - r)) t
    simp only [sub_sub_cancel] at h
    rw [← h]
    exact lintegral_congr fun s => mul_comm _ _
  have hf : Measurable fun s => survival β w (t - s) :=
    (measurable_survival β w).comp (measurable_const.sub measurable_id)
  rw [hL, hR, lintegral_expMeasure_totalRate β v hf, hreflect]
  ring

/-- **`P^{(n+1)} = 𝓛 P^{(n)}`**: the decomposition along the last expression before `t`. -/
theorem nJump_succ_eq_lastStep (β : ℝ) (n : ℕ) :
    (fun v w t => nJump β v w (n + 1) t) = lastStep β (fun v w t => nJump β v w n t) := by
  induction n with
  | zero =>
      funext v w t
      rw [nJump_succ_eq_firstStep, firstStep_nJump_zero]
  | succ n ih =>
      funext v w t
      have hfirst : (fun u x s => nJump β u x (n + 1) s)
          = firstStep β (fun u x s => nJump β u x n s) := by
        funext u x s
        exact nJump_succ_eq_firstStep β u x n s
      show nJump β v w (n + 1 + 1) t = lastStep β (fun u x s => nJump β u x (n + 1) s) v w t
      rw [nJump_succ_eq_firstStep, ih,
        firstStep_lastStep β (fun u x => measurable_nJump β u x n), ← hfirst]

end LastStep

/-! ### Starting from a measure

Mixing `P^{(n)}` over the starting matrix commutes with `𝓛`, which acts on the end point.  The
bound is then an induction on the number of expressions. -/

section Mix

/-- `∑_v μ (v) P^{(n)}_t (v, w)`. -/
noncomputable def mixJump (β : ℝ) (μ : Measure (Pressure N M)) (w : Pressure N M) (n : ℕ)
    (t : ℝ) : ℝ≥0∞ :=
  ∑' v, μ {v} * nJump β v w n t

theorem measurable_mixJump (β : ℝ) (μ : Measure (Pressure N M)) (w : Pressure N M) (n : ℕ) :
    Measurable (mixJump β μ w n) :=
  Measurable.ennreal_tsum fun v => (measurable_nJump β v w n).const_mul _

theorem mixJump_zero (β : ℝ) (μ : Measure (Pressure N M)) (w : Pressure N M) (t : ℝ) :
    mixJump β μ w 0 t = μ {w} * survival β w t := by
  rw [mixJump, tsum_eq_single w fun v hv => by rw [nJump_zero, if_neg hv, mul_zero],
    nJump_zero, if_pos rfl]

theorem mixJump_succ (β : ℝ) (μ : Measure (Pressure N M)) (w : Pressure N M) (n : ℕ) (t : ℝ) :
    mixJump β μ w (n + 1) t
      = ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * ∫⁻ r, survival β w r * mixJump β μ x n (t - r) := by
  have hpt : ∀ v, nJump β v w (n + 1) t
      = ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * ∫⁻ r, survival β w r * nJump β v x n (t - r) :=
    fun v => congrFun (congrFun (congrFun (nJump_succ_eq_lastStep β n) v) w) t
  have hinner : ∀ x, ∫⁻ r, survival β w r * mixJump β μ x n (t - r)
      = ∑' v, μ {v} * ∫⁻ r, survival β w r * nJump β v x n (t - r) := by
    intro x
    have hm : ∀ v, Measurable fun r => survival β w r * nJump β v x n (t - r) := fun v =>
      (measurable_survival β w).mul
        ((measurable_nJump β v x n).comp (measurable_const.sub measurable_id))
    simp only [mixJump]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [lintegral_tsum fun v => ((measurable_survival β w).mul
      (((measurable_nJump β v x n).comp (measurable_const.sub measurable_id)).const_mul _)).aemeasurable]
    refine tsum_congr fun v => ?_
    rw [← lintegral_const_mul _ (hm v)]
    exact lintegral_congr fun r => by ring
  calc mixJump β μ w (n + 1) t
      = ∑' v, ∑' x, μ {v} * (ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * ∫⁻ r, survival β w r * nJump β v x n (t - r)) :=
        tsum_congr fun v => by rw [hpt v, ENNReal.tsum_mul_left]
    _ = ∑' x, ∑' v, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * (μ {v} * ∫⁻ r, survival β w r * nJump β v x n (t - r)) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun x => tsum_congr fun v => by ring
    _ = ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
          * ∫⁻ r, survival β w r * mixJump β μ x n (t - r) :=
        tsum_congr fun x => by rw [hinner x, ENNReal.tsum_mul_left]

/-- **The induction on the number of expressions.**  If `q · μ` is sent below itself by the
skeleton, then at most `μ (w)` of the mass started from `μ` sits at `w` at any time `t ≥ 0`
having made fewer than `K` expressions --- and none before time `0`. -/
theorem sum_mixJump_le (β : ℝ) {μ : Measure (Pressure N M)}
    (hinv : ∀ w, ∑' x, skeletonKernel β x {w} * (ENNReal.ofReal (totalRate β x) * μ {x})
      ≤ ENNReal.ofReal (totalRate β w) * μ {w}) (K : ℕ) :
    ∀ w t, ∑ n ∈ Finset.range K, mixJump β μ w n t ≤ μ {w} * Set.indicator (Set.Ici 0) 1 t := by
  induction K with
  | zero => intro w t; simp
  | succ K ih =>
      intro w t
      set I : ℝ≥0∞ := ∫⁻ r, survival β w r * Set.indicator (Set.Ici 0) 1 (t - r) with hI
      have hmix : ∀ x n, Measurable fun r => survival β w r * mixJump β μ x n (t - r) :=
        fun x n => (measurable_survival β w).mul
          ((measurable_mixJump β μ x n).comp (measurable_const.sub measurable_id))
      have hswap : ∑ n ∈ Finset.range K, mixJump β μ w (n + 1) t
          = ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
              * ∫⁻ r, survival β w r * ∑ n ∈ Finset.range K, mixJump β μ x n (t - r) := by
        simp_rw [mixJump_succ]
        rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine tsum_congr fun x => ?_
        rw [← Finset.mul_sum, ← lintegral_finset_sum _ fun n _ => hmix x n]
        simp_rw [Finset.mul_sum]
      have hstep : ∑ n ∈ Finset.range K, mixJump β μ w (n + 1) t
          ≤ ENNReal.ofReal (totalRate β w) * μ {w} * I := by
        rw [hswap]
        calc ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
              * ∫⁻ r, survival β w r * ∑ n ∈ Finset.range K, mixJump β μ x n (t - r)
            ≤ ∑' x, ENNReal.ofReal (totalRate β x) * skeletonKernel β x {w}
              * ∫⁻ r, survival β w r * (μ {x} * Set.indicator (Set.Ici 0) 1 (t - r)) :=
              ENNReal.tsum_le_tsum fun x => by
                have h : ∫⁻ r, survival β w r * ∑ n ∈ Finset.range K, mixJump β μ x n (t - r)
                    ≤ ∫⁻ r, survival β w r * (μ {x} * Set.indicator (Set.Ici 0) 1 (t - r)) :=
                  lintegral_mono fun r => by gcongr; exact ih x (t - r)
                gcongr
          _ = ∑' x, skeletonKernel β x {w} * (ENNReal.ofReal (totalRate β x) * μ {x}) * I := by
              refine tsum_congr fun x => ?_
              have hpt : ∀ r, survival β w r * (μ {x} * Set.indicator (Set.Ici 0) 1 (t - r))
                  = μ {x} * (survival β w r * Set.indicator (Set.Ici 0) 1 (t - r)) :=
                fun r => by ring
              rw [lintegral_congr hpt, lintegral_const_mul' _ _ (measure_ne_top μ {x})]
              ring
          _ = (∑' x, skeletonKernel β x {w} * (ENNReal.ofReal (totalRate β x) * μ {x})) * I :=
              ENNReal.tsum_mul_right
          _ ≤ ENNReal.ofReal (totalRate β w) * μ {w} * I := by gcongr; exact hinv w
      rw [Finset.sum_range_succ', mixJump_zero]
      calc ∑ n ∈ Finset.range K, mixJump β μ w (n + 1) t + μ {w} * survival β w t
          ≤ ENNReal.ofReal (totalRate β w) * μ {w} * I + μ {w} * survival β w t :=
            add_le_add hstep le_rfl
        _ = μ {w} * (survival β w t + ENNReal.ofReal (totalRate β w) * I) := by ring
        _ = μ {w} * Set.indicator (Set.Ici 0) 1 t := by rw [hI, survival_add_lintegral]

end Mix

/-! ### The decomposition, from Theorem 1.1

Away from a null set the holding times are positive and the jump times do not accumulate; then
the number of expressions made by `t` is finite, and the realisation lies in the event of
`P^{(n)}_t` for that number.  Without Theorem 1.1 the decomposition would miss the realisations
that explode before `t`. -/

section Decomposition

omit [NeZero N] [NeZero M] in
theorem bddAbove_of_explosionTime_eq_top {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω)
    (hexp : explosionTime ω = ⊤) (t : ℝ) : BddAbove {n : ℕ | jumpTime n ω ≤ t} := by
  by_contra hb
  have hall : ∀ n, jumpTime n ω ≤ t := by
    intro n
    obtain ⟨m, hm, hnm⟩ := not_bddAbove_iff.1 hb n
    exact le_trans (jumpTime_mono hpos hnm.le) hm
  have hle : explosionTime ω ≤ ENNReal.ofReal t :=
    iSup_le fun n => ENNReal.ofReal_le_ofReal (hall n)
  rw [hexp] at hle
  exact ENNReal.ofReal_ne_top (top_le_iff.1 hle)

omit [NeZero N] [NeZero M] in
/-- Below the explosion time the jump counter names the event the realisation lies in. -/
theorem mem_nJumpSet_jumpCount (v : Pressure N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) (hexp : explosionTime ω = ⊤) {t : ℝ} (ht : 0 ≤ t) :
    ω ∈ nJumpSet v (process v t ω) (jumpCount ω t) t := by
  have hb := bddAbove_of_explosionTime_eq_top hpos hexp t
  have hne : {n : ℕ | jumpTime n ω ≤ t}.Nonempty := ⟨0, by simpa using ht⟩
  refine ⟨Nat.sSup_mem hne hb, ?_, rfl⟩
  by_contra hle
  have : jumpCount ω t + 1 ≤ jumpCount ω t := le_csSup hb (not_lt.1 hle)
  omega

omit [NeZero N] [NeZero M] in
theorem measurable_explosionTime : Measurable (explosionTime (N := N) (M := M)) :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_jumpTime n)

/-- **`P_t ≤ ∑_n P^{(n)}_t`.**  This is where Theorem 1.1 is used. -/
theorem transitionKernel_le_tsum_nJump (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {v : Pressure N M} (hv : IsState v) (w : Pressure N M) {t : ℝ} (ht : 0 ≤ t) :
    transitionKernel β t v {w} ≤ ∑' n, nJump β v w n t := by
  set A : Set (ℕ → Step N M) := {ω | ∃ n, holdingTime n ω ≤ 0} with hAdef
  set B : Set (ℕ → Step N M) := {ω | explosionTime ω = ⊤}ᶜ with hBdef
  have hA : ctsPathMeasure β v A = 0 := ctsPathMeasure_exists_holdingTime_nonpos β v
  have hB : ctsPathMeasure β v B = 0 :=
    (prob_compl_eq_zero_iff (measurable_explosionTime (measurableSet_singleton ⊤))).2
      (nonExplosion hM hN hβ hv)
  have hsub : process v t ⁻¹' {w} ⊆ (⋃ n, nJumpSet v w n t) ∪ (A ∪ B) := by
    intro ω hω
    by_cases hpos : ∀ n, 0 < holdingTime n ω
    · by_cases hexp : explosionTime ω = ⊤
      · left
        refine Set.mem_iUnion.2 ⟨jumpCount ω t, ?_⟩
        have h := mem_nJumpSet_jumpCount v hpos hexp ht
        rwa [show process v t ω = w from hω] at h
      · exact Or.inr (Or.inr hexp)
    · push_neg at hpos
      exact Or.inr (Or.inl hpos)
  rw [transitionKernel_apply, Measure.map_apply (measurable_process v t) (measurableSet_singleton w)]
  calc ctsPathMeasure β v (process v t ⁻¹' {w})
      ≤ ctsPathMeasure β v ((⋃ n, nJumpSet v w n t) ∪ (A ∪ B)) := measure_mono hsub
    _ ≤ ctsPathMeasure β v (⋃ n, nJumpSet v w n t)
          + (ctsPathMeasure β v A + ctsPathMeasure β v B) :=
        le_trans (measure_union_le _ _) (add_le_add le_rfl (measure_union_le _ _))
    _ = ctsPathMeasure β v (⋃ n, nJumpSet v w n t) := by rw [hA, hB, add_zero, add_zero]
    _ ≤ ∑' n, nJump β v w n t := measure_iUnion_le _

end Decomposition

/-! ### The converse, and Theorem 1.2 -/

section Existence

/-- **The converse of `SocialNetwork.invariant_rateMeasure`.**  If the skeleton sends `q_β · μ`
below itself, then `μ` is invariant for the process.

This is the direction of the equivalence of p. 18 that existence needs.  It uses Theorem 1.1,
and has to: see the header of this file. -/
theorem invariantCts_of_bind_rateMeasure_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Measure (Pressure N M)} [IsProbabilityMeasure μ] (hμS : IsCarriedByState μ)
    (hle : (rateMeasure β μ).bind (skeletonKernel β) ≤ rateMeasure β μ) :
    IsInvariantCts β μ := by
  have hinv : ∀ w, ∑' x, skeletonKernel β x {w} * (ENNReal.ofReal (totalRate β x) * μ {x})
      ≤ ENNReal.ofReal (totalRate β w) * μ {w} := by
    intro w
    simpa only [bind_apply_singleton, rateMeasure_singleton] using Measure.le_iff'.1 hle {w}
  intro t ht
  have hbound : ∀ w, (μ.bind (transitionKernel β t)) {w} ≤ μ {w} := by
    intro w
    rw [bind_apply_singleton]
    have hterm : ∀ v, transitionKernel β t v {w} * μ {v} ≤ μ {v} * ∑' n, nJump β v w n t := by
      intro v
      by_cases hv : IsState v
      · rw [mul_comm]
        gcongr
        exact transitionKernel_le_tsum_nJump hM hN hβ hv w ht
      · have hzero : μ {v} = 0 := measure_mono_null (Set.singleton_subset_iff.2 hv) hμS
        simp [hzero]
    calc ∑' v, transitionKernel β t v {w} * μ {v}
        ≤ ∑' v, μ {v} * ∑' n, nJump β v w n t := ENNReal.tsum_le_tsum hterm
      _ = ∑' n, mixJump β μ w n t := by
          simp_rw [← ENNReal.tsum_mul_left]
          exact ENNReal.tsum_comm
      _ = ⨆ K, ∑ n ∈ Finset.range K, mixJump β μ w n t := ENNReal.tsum_eq_iSup_nat
      _ ≤ μ {w} * Set.indicator (Set.Ici 0) 1 t := iSup_le fun K => sum_mixJump_le β hinv K w t
      _ = μ {w} := by rw [Set.indicator_of_mem (Set.mem_Ici.2 ht), Pi.one_apply, mul_one]
  have huniv : (μ.bind (transitionKernel β t)) Set.univ = μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp
  exact eq_of_le_of_univ_eq (le_of_forall_singleton_le hbound) huniv (measure_ne_top μ _)

/-- **The correspondence of p. 18**, in both directions: a probability measure carried by `S`
is invariant for the process exactly when its product with the jump rate is invariant for the
skeleton.  The paper cites it; `SocialNetwork.invariant_rateMeasure` and
`SocialNetwork.invariantCts_of_bind_rateMeasure_le` prove it. -/
theorem isInvariantCts_iff (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Measure (Pressure N M)} [IsProbabilityMeasure μ] (hμS : IsCarriedByState μ) :
    IsInvariantCts β μ ↔ Kernel.Invariant (skeletonKernel β) (rateMeasure β μ) :=
  ⟨invariant_rateMeasure hM hβ hμS,
    fun h => invariantCts_of_bind_rateMeasure_le hM hN hβ hμS (le_of_eq h)⟩

/-- The right-hand side of equation (13), as a measure: `μ̃ / q_β`, normalised. -/
noncomputable def ctsOfSkeleton (β : ℝ) (μ : Measure (Pressure N M)) : Measure (Pressure N M) :=
  (∑' v, μ {v} / ENNReal.ofReal (totalRate β v))⁻¹
    • μ.withDensity fun v => (ENNReal.ofReal (totalRate β v))⁻¹

omit [NeZero N] [NeZero M] in
theorem ctsOfSkeleton_singleton (β : ℝ) (μ : Measure (Pressure N M)) (w : Pressure N M) :
    ctsOfSkeleton β μ {w}
      = (∑' v, μ {v} / ENNReal.ofReal (totalRate β v))⁻¹
          * (μ {w} / ENNReal.ofReal (totalRate β w)) := by
  rw [ctsOfSkeleton, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton w), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, div_eq_mul_inv]

/-- **Existence for Theorem 1.2.**  The right-hand side of equation (13) is an invariant
probability measure of the process, carried by `S`. -/
theorem ctsOfSkeleton_spec (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μskel : Measure (Pressure N M)} [IsProbabilityMeasure μskel]
    (hsS : IsCarriedByState μskel) (hsinv : Kernel.Invariant (skeletonKernel β) μskel) :
    IsProbabilityMeasure (ctsOfSkeleton β μskel) ∧ IsCarriedByState (ctsOfSkeleton β μskel)
      ∧ IsInvariantCts β (ctsOfSkeleton β μskel) := by
  set Z := ∑' v, μskel {v} / ENNReal.ofReal (totalRate β v) with hZ
  have hq0 : ∀ w : Pressure N M, ENNReal.ofReal (totalRate β w) ≠ 0 :=
    fun w => (ENNReal.ofReal_pos.2 (totalRate_pos β w)).ne'
  have hZtop : Z ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_div_totalRate_le β μskel hsS)
    exact ENNReal.div_ne_top ENNReal.one_ne_top (by exact_mod_cast NeZero.ne M)
  have hZ0 : Z ≠ 0 := by
    intro h0
    have hall : ∀ w : Pressure N M, μskel {w} = 0 := by
      intro w
      have hle : μskel {w} / ENNReal.ofReal (totalRate β w) ≤ Z :=
        ENNReal.le_tsum (f := fun v => μskel {v} / ENNReal.ofReal (totalRate β v)) w
      rw [h0, le_zero_iff, ENNReal.div_eq_zero_iff] at hle
      exact hle.resolve_right ENNReal.ofReal_ne_top
    have hone := tsum_measure_singleton μskel
    rw [tsum_congr hall] at hone
    simp at hone
  have hsing : ∀ w, ctsOfSkeleton β μskel {w}
      = Z⁻¹ * (μskel {w} / ENNReal.ofReal (totalRate β w)) :=
    ctsOfSkeleton_singleton β μskel
  have hprob : IsProbabilityMeasure (ctsOfSkeleton β μskel) := by
    refine ⟨?_⟩
    have h := lintegral_countable' (μ := ctsOfSkeleton β μskel) (fun _ => (1 : ℝ≥0∞))
    simp only [lintegral_const, one_mul] at h
    rw [h, tsum_congr hsing, ENNReal.tsum_mul_left, ← hZ, ENNReal.inv_mul_cancel hZ0 hZtop]
  have hS : IsCarriedByState (ctsOfSkeleton β μskel) := by
    show ctsOfSkeleton β μskel (stateSet N M)ᶜ = 0
    rw [ctsOfSkeleton, Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ (measurableSet_pressure _), Measure.restrict_eq_zero.2 hsS,
      lintegral_zero_measure, mul_zero]
  refine ⟨hprob, hS, invariantCts_of_bind_rateMeasure_le hM hN hβ hS ?_⟩
  -- `q_β · (μ̃ / q_β) / Z = μ̃ / Z`, which the skeleton keeps
  have hrate : ∀ w, rateMeasure β (ctsOfSkeleton β μskel) {w} = Z⁻¹ * μskel {w} := by
    intro w
    rw [rateMeasure_singleton, hsing, div_eq_mul_inv, ← mul_assoc, mul_comm _ Z⁻¹, mul_assoc,
      mul_comm (μskel {w}), ← mul_assoc (ENNReal.ofReal _),
      ENNReal.mul_inv_cancel (hq0 w) ENNReal.ofReal_ne_top, one_mul]
  refine le_of_forall_singleton_le fun w => le_of_eq ?_
  rw [bind_apply_singleton]
  simp only [hrate]
  have hfix : ∑' x, skeletonKernel β x {w} * μskel {x} = μskel {w} := by
    rw [← bind_apply_singleton, hsinv]
  calc ∑' x, skeletonKernel β x {w} * (Z⁻¹ * μskel {x})
      = Z⁻¹ * ∑' x, skeletonKernel β x {w} * μskel {x} := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by ring
    _ = Z⁻¹ * μskel {w} := by rw [hfix]

/-- **Theorem 1.2.**  The process has a unique invariant probability measure `μ^β` carried by
`S`.

**Follows the paper's proof**, with the step it cites supplied.  The skeleton has a unique
invariant measure `μ̃^β` (`SocialNetwork.existsUnique_invariantSkeleton`), and the correspondence
of p. 18 (`SocialNetwork.isInvariantCts_iff`) transfers it: existence is
`SocialNetwork.ctsOfSkeleton_spec`, uniqueness is `SocialNetwork.eq_of_invariantCts`. -/
theorem existsUnique_invariantCts (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ∃! μ : Measure (Pressure N M),
      IsProbabilityMeasure μ ∧ IsCarriedByState μ ∧ IsInvariantCts β μ := by
  obtain ⟨μskel, ⟨hsprob, hsS, hsinv⟩, -⟩ := existsUnique_invariantSkeleton (N := N) (M := M) hM hβ
  refine ⟨ctsOfSkeleton β μskel, ctsOfSkeleton_spec hM hN hβ hsS hsinv, ?_⟩
  rintro ν ⟨hν, hνS, hνinv⟩
  obtain ⟨hprob, hS, hinv⟩ := ctsOfSkeleton_spec hM hN hβ hsS hsinv
  exact eq_of_invariantCts hM hN hβ hν hνS hνinv hprob hS hinv

end Existence

end SocialNetwork
