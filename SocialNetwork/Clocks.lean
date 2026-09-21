/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The race between independent exponential clocks

Attach to each `i` of a finite set an independent clock ringing at an exponential time of
rate `r i > 0`.  This file proves that the pair

```
(which clock rings first,  when it rings)
```

has law `(the probability mass function `i ↦ r i / ∑ r`) ⊗ (exponential of rate `∑ r`)`:
the winner and the winning time are independent, the winner is drawn from the normalised
rates, and the time is exponential of the total rate.

Mathlib has the exponential distribution but neither half of this: nothing on the minimum
of independent exponentials, and nothing on which of several exponentials is smallest.

## Why the paper needs it

`SocialNetwork.stepLaw` builds one step of the continuous-time process in the *jump-hold*
form — the expressed pair from the Gibbs law of equation (3), the holding time exponential
of the total rate, independently of it.  The proof of Theorem 1.1 at p. 16 of
arXiv:2607.19651 needs the *other* form, one clock per pair, because its bound (11) is a
statement about the clocks of a sub-family: the expressions coming from actors carrying
social pressure below `N` have total rate at most `NMe^{βN}` whatever the rest of the
matrix does, and that is what sandwiches them between two Poisson processes.  The two
forms describe the same law, and that is this file.

## Main results

* `SocialNetwork.expMeasure_Ioi_of_nonneg` — the tail of one clock.
* `SocialNetwork.pi_expMeasure_pi_Ioi` — no clock has rung by time `t`, with probability
  `e^{-(∑ r) t}`.
* `SocialNetwork.map_min_pi_expMeasure` — the first ring is exponential of rate `∑ r`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace SocialNetwork

/-! ### The tail of one exponential clock -/

theorem expMeasure_Iic_of_nonneg {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Set.Iic x) = ENNReal.ofReal (1 - Real.exp (-(r * x))) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hx]

theorem expMeasure_Ioi_of_nonneg {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  have hp : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hcompl : Set.Ioi x = (Set.Iic x)ᶜ := by ext y; simp
  rw [hcompl, prob_compl_eq_one_sub measurableSet_Iic, expMeasure_Iic_of_nonneg hr hx]
  have h1 : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1
  ring

theorem expMeasure_Iic_zero {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  rw [expMeasure_Iic_of_nonneg hr le_rfl]
  simp

/-- The exponential law has no atom: it is `volume.withDensity` of a density, hence
absolutely continuous. -/
theorem expMeasure_singleton (r : ℝ) (x : ℝ) : expMeasure r {x} = 0 := by
  have hac : expMeasure r ≪ MeasureTheory.volume := by
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _
  exact hac (measure_singleton x)

/-- The closed tail carries the same mass as the open one. -/
theorem expMeasure_Ici_of_nonneg {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure r (Set.Ici x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  have hsplit : Set.Ici x = {x} ∪ Set.Ioi x := by
    ext y; simp [Set.mem_Ici, le_iff_lt_or_eq, or_comm]
  rw [hsplit, measure_union (by simp) measurableSet_Ioi, expMeasure_singleton, zero_add,
    expMeasure_Ioi_of_nonneg hr hx]

/-- Below the origin the clock has not rung. -/
theorem expMeasure_Ioi_of_neg {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : x < 0) :
    expMeasure r (Set.Ioi x) = 1 := by
  have hp : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hcompl : Set.Ioi x = (Set.Iic x)ᶜ := by ext y; simp
  have hIic : expMeasure r (Set.Iic x) = 0 := by
    have : IsProbabilityMeasure (expMeasure r) := hp
    rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_neg (by linarith)]
    simp
  rw [hcompl, prob_compl_eq_one_sub measurableSet_Iic, hIic, tsub_zero]

/-! ### No clock has rung yet -/

variable {ι : Type*} [Fintype ι] {r : ι → ℝ}

/-- The clocks are independent, so the chance that none has rung by time `t` is the product
of the individual tails, which is the tail of the total rate. -/
theorem pi_expMeasure_pi_Ioi (hr : ∀ i, 0 < r i) {t : ℝ} (ht : 0 ≤ t) :
    Measure.pi (fun i => expMeasure (r i)) (Set.univ.pi fun _ => Set.Ioi t)
      = ENNReal.ofReal (Real.exp (-((∑ i, r i) * t))) := by
  have : ∀ i, IsProbabilityMeasure (expMeasure (r i)) := fun i =>
    isProbabilityMeasure_expMeasure (hr i)
  rw [Measure.pi_pi]
  have hterm : ∀ i : ι, expMeasure (r i) (Set.Ioi t)
      = ENNReal.ofReal (Real.exp (-(r i * t))) := fun i =>
    expMeasure_Ioi_of_nonneg (hr i) ht
  simp only [hterm]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib, Finset.sum_mul]

/-! ### Splitting off one clock

To compute which clock rings first, the clock at `i₀` has to be separated from the others.
Mathlib splits a product measure along a sum of index types
(`measurePreserving_sumPiEquivProdPi`) and along `Fin (n+1)`
(`measurePreserving_piFinSuccAbove`), but not along one point of an arbitrary index type;
this is that splitting, proved the same way. -/

variable [DecidableEq ι]

/-- The clocks, read as the clock at `i₀` together with all the others. -/
def clockSplit (i₀ : ι) : (ℝ × ({j : ι // j ≠ i₀} → ℝ)) ≃ (ι → ℝ) where
  toFun p j := if h : j = i₀ then p.1 else p.2 ⟨j, h⟩
  invFun c := (c i₀, fun j => c j.1)
  left_inv := by
    rintro ⟨x, g⟩
    refine Prod.ext (by simp) ?_
    funext j
    simp only [dif_neg j.2, Subtype.coe_eta]
  right_inv := by
    intro c
    funext j
    by_cases h : j = i₀ <;> simp [h]

omit [Fintype ι] in
@[simp]
theorem clockSplit_apply (i₀ : ι) (p : ℝ × ({j : ι // j ≠ i₀} → ℝ)) (j : ι) :
    clockSplit i₀ p j = if h : j = i₀ then p.1 else p.2 ⟨j, h⟩ := rfl

omit [Fintype ι] in
theorem measurable_clockSplit (i₀ : ι) : Measurable (clockSplit i₀) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j = i₀
  · simpa [clockSplit_apply, h] using measurable_fst
  · simp only [clockSplit_apply, dif_neg h]
    exact (measurable_pi_apply (⟨j, h⟩ : {j : ι // j ≠ i₀})).comp measurable_snd

omit [Fintype ι] in
/-- The preimage of a box is a rectangle. -/
theorem clockSplit_preimage_pi (i₀ : ι) (s : ι → Set ℝ) :
    clockSplit i₀ ⁻¹' (Set.univ.pi s)
      = (s i₀) ×ˢ (Set.univ.pi fun j : {j : ι // j ≠ i₀} => s j.1) := by
  ext ⟨x, g⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
    clockSplit_apply]
  constructor
  · intro h
    exact ⟨by simpa using h i₀, fun j => by simpa [dif_neg j.2] using h j.1⟩
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i₀
    · simpa [hj] using h1
    · simpa [dif_neg hj] using h2 ⟨j, hj⟩

/-- Splitting the product measure of the clocks at `i₀`. -/
theorem measurePreserving_clockSplit (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (i₀ : ι) :
    MeasurePreserving (clockSplit i₀)
      ((μ i₀).prod (Measure.pi fun j : {j : ι // j ≠ i₀} => μ j.1))
      (Measure.pi μ) := by
  refine ⟨measurable_clockSplit i₀, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (measurable_clockSplit i₀) (MeasurableSet.univ_pi hs),
    clockSplit_preimage_pi, Measure.prod_prod, Measure.pi_pi]
  have hsub : ∏ j : {j : ι // j ≠ i₀}, μ j.1 (s j.1)
      = ∏ j ∈ Finset.univ.erase i₀, μ j (s j) :=
    (Finset.prod_subtype _ (fun x => by simp) (fun j => μ j (s j))).symm
  rw [hsub, Finset.mul_prod_erase _ (fun j => μ j (s j)) (Finset.mem_univ i₀)]

/-! ### The clock at `i₀` rings first

The only analytic input of the file: against one exponential clock, the tail of a second
independent one integrates to the ratio of the rates.  This is where `r i₀ / ∑ r` comes
from. -/

/-- `∫ e^{-bx} over the tail `(t, ∞)` of an `Exp a` clock`. -/
theorem lintegral_exp_neg_expMeasure_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ x in Set.Ioi t, ENNReal.ofReal (Real.exp (-(b * x))) ∂(expMeasure a)
      = ENNReal.ofReal (a / (a + b) * Real.exp (-((a + b) * t))) := by
  have hab : 0 < a + b := by linarith
  have hdens : expMeasure a = MeasureTheory.volume.withDensity (exponentialPDF a) := rfl
  have hmeas : Measurable (exponentialPDF a) :=
    (measurable_exponentialPDFReal a).ennreal_ofReal
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(b * x))) :=
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).ennreal_ofReal
  rw [hdens, restrict_withDensity measurableSet_Ioi,
    lintegral_withDensity_eq_lintegral_mul _ hmeas hg]
  -- on the tail the density is `a e^{-ax}`, so the integrand is `a e^{-(a+b)x}`
  have hcongr : ∀ x ∈ Set.Ioi t, (exponentialPDF a * fun x : ℝ =>
      ENNReal.ofReal (Real.exp (-(b * x)))) x
      = ENNReal.ofReal (a * Real.exp (-((a + b) * x))) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans ht (le_of_lt hx)
    simp only [Pi.mul_apply, exponentialPDF_eq, if_pos hx0]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  -- and that integral is elementary
  have hint : IntegrableOn (fun x : ℝ => a * Real.exp (-((a + b) * x))) (Set.Ioi t) := by
    refine Integrable.const_mul ?_ a
    have h := integrableOn_exp_mul_Ioi (a := -(a + b)) (by linarith) t
    simp only [neg_mul] at h
    exact h
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi t)]
      fun x : ℝ => a * Real.exp (-((a + b) * x)) :=
    Filter.Eventually.of_forall fun x => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [integral_const_mul]
  have hsub : ∫ x : ℝ in Set.Ioi t, Real.exp (-((a + b) * x))
      = (a + b)⁻¹ * Real.exp (-((a + b) * t)) := by
    have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) t hab
    rw [integral_exp_neg_Ioi, smul_eq_mul] at h
    exact h
  rw [hsub]
  field_simp

/-! ### Which clock rings first -/

/-- The clock at `i₀` rings strictly before every other, and after time `t`. -/
def winsAfter (i₀ : ι) (t : ℝ) : Set (ι → ℝ) :=
  {c | (∀ j, j ≠ i₀ → c i₀ < c j) ∧ t < c i₀}

omit [Fintype ι] [DecidableEq ι] in
theorem measurableSet_winsAfter [Countable ι] (i₀ : ι) (t : ℝ) :
    MeasurableSet (winsAfter (ι := ι) i₀ t) := by
  have hrw : winsAfter (ι := ι) i₀ t
      = (⋂ j : ι, {c : ι → ℝ | j = i₀ ∨ c i₀ < c j}) ∩ {c : ι → ℝ | t < c i₀} := by
    ext c
    simp only [winsAfter, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, h2⟩
      by_cases hj : j = i₀
      · exact Or.inl hj
      · exact Or.inr (h1 j hj)
    · rintro ⟨h1, h2⟩
      exact ⟨fun j hj => (h1 j).resolve_left hj, h2⟩
  rw [hrw]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_)
    (measurableSet_lt measurable_const (measurable_pi_apply i₀))
  by_cases hj : j = i₀
  · simp [hj]
  · simpa [hj] using measurableSet_lt (measurable_pi_apply i₀) (measurable_pi_apply j)

omit [Fintype ι] in
theorem clockSplit_preimage_winsAfter (i₀ : ι) (t : ℝ) :
    clockSplit i₀ ⁻¹' winsAfter i₀ t
      = {p : ℝ × ({j : ι // j ≠ i₀} → ℝ) | (∀ j, p.1 < p.2 j) ∧ t < p.1} := by
  ext ⟨x, g⟩
  simp only [Set.mem_preimage, winsAfter, clockSplit_apply, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => by simpa [dif_neg j.2] using h1 j.1 j.2, ?_⟩
    simpa using h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => by simpa [dif_neg hj] using h1 ⟨j, hj⟩, ?_⟩
    simpa using h2

/-- The rates of the other clocks add up to the total minus this one. -/
theorem sum_subtype_ne (i₀ : ι) : ∑ j : {j : ι // j ≠ i₀}, r j.1 = (∑ i, r i) - r i₀ := by
  have hsub : ∑ j : {j : ι // j ≠ i₀}, r j.1 = ∑ j ∈ Finset.univ.erase i₀, r j :=
    (Finset.sum_subtype _ (fun x => by simp) r).symm
  rw [hsub, eq_sub_iff_add_eq, add_comm, Finset.add_sum_erase _ r (Finset.mem_univ i₀)]

/-- **The race.**  The clock at `i₀` rings first, and after time `t`, with probability
`(r i₀ / ∑ r) · e^{-(∑ r) t}`: the winner is drawn from the normalised rates, the winning
time is exponential of the total rate, and the two are independent. -/
theorem pi_expMeasure_winsAfter (hr : ∀ i, 0 < r i) (i₀ : ι) {t : ℝ} (ht : 0 ≤ t) :
    Measure.pi (fun i => expMeasure (r i)) (winsAfter i₀ t)
      = ENNReal.ofReal (r i₀ / (∑ i, r i) * Real.exp (-((∑ i, r i) * t))) := by
  have hprob : ∀ i, IsProbabilityMeasure (expMeasure (r i)) := fun i =>
    isProbabilityMeasure_expMeasure (hr i)
  set R := ∑ i, r i with hR
  have hrest : 0 ≤ R - r i₀ := by
    rw [hR, ← sum_subtype_ne (r := r) i₀]
    exact Finset.sum_nonneg fun j _ => (hr j.1).le
  have hcancel : r i₀ + (R - r i₀) = R := by ring
  set S := {p : ℝ × ({j : ι // j ≠ i₀} → ℝ) | (∀ j, p.1 < p.2 j) ∧ t < p.1} with hS
  have hmeasS : MeasurableSet S := by
    have hrw : S = (⋂ j : {j : ι // j ≠ i₀},
        {p : ℝ × ({j : ι // j ≠ i₀} → ℝ) | p.1 < p.2 j}) ∩ {p | t < p.1} := by
      ext p
      simp [hS, Set.mem_iInter]
    rw [hrw]
    exact MeasurableSet.inter
      (MeasurableSet.iInter fun j =>
        measurableSet_lt measurable_fst ((measurable_pi_apply j).comp measurable_snd))
      (measurableSet_lt measurable_const measurable_fst)
  rw [← (measurePreserving_clockSplit (fun i => expMeasure (r i)) i₀).map_eq,
    Measure.map_apply (measurable_clockSplit i₀) (measurableSet_winsAfter i₀ t),
    clockSplit_preimage_winsAfter, ← hS, Measure.prod_apply hmeasS]
  -- the section at `x` is a box when `x > t`, and empty otherwise
  have hsec : ∀ x : ℝ,
      Measure.pi (fun j : {j : ι // j ≠ i₀} => expMeasure (r j.1)) (Prod.mk x ⁻¹' S)
      = Set.indicator (Set.Ioi t)
          (fun x => ENNReal.ofReal (Real.exp (-((R - r i₀) * x)))) x := by
    intro x
    by_cases hx : t < x
    · have hbox : Prod.mk x ⁻¹' S = Set.univ.pi fun _ : {j : ι // j ≠ i₀} => Set.Ioi x := by
        ext g; simp [hS, hx]
      rw [hbox, Set.indicator_of_mem (Set.mem_Ioi.2 hx),
        pi_expMeasure_pi_Ioi (r := fun j : {j : ι // j ≠ i₀} => r j.1)
          (fun j => hr j.1) (le_trans ht hx.le),
        sum_subtype_ne (r := r) i₀, ← hR]
    · have hempty : Prod.mk x ⁻¹' S = ∅ := by
        ext g; simp [hS, hx]
      rw [hempty, Set.indicator_of_notMem (by simpa using hx), measure_empty]
  rw [lintegral_congr hsec, lintegral_indicator measurableSet_Ioi,
    lintegral_exp_neg_expMeasure_Ioi (hr i₀) hrest ht, hcancel]

/-! ### Ties are impossible

Two clocks ring at the same instant with probability zero, which is what lets *a* winner be
chosen measurably without the choice mattering. -/

/-- A null set in one coordinate is null for the clocks. -/
theorem pi_expMeasure_coord (hr : ∀ i, 0 < r i) (k : ι) {A : Set ℝ}
    (hA : expMeasure (r k) A = 0) :
    Measure.pi (fun i => expMeasure (r i)) {c : ι → ℝ | c k ∈ A} = 0 := by
  have hprob : ∀ i, IsProbabilityMeasure (expMeasure (r i)) := fun i =>
    isProbabilityMeasure_expMeasure (hr i)
  have hbox : {c : ι → ℝ | c k ∈ A}
      = Set.univ.pi fun k' => if k' = k then A else Set.univ := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h k'
      by_cases hk : k' = k <;> simp [hk, h]
    · intro h
      simpa using h k
  rw [hbox, Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  simp [hA]

theorem pi_expMeasure_coord_singleton (hr : ∀ i, 0 < r i) (k : ι) (x : ℝ) :
    Measure.pi (fun i => expMeasure (r i)) {c : ι → ℝ | c k = x} = 0 :=
  pi_expMeasure_coord (A := {x}) hr k (expMeasure_singleton _ _)

/-- Every clock is almost surely positive. -/
theorem pi_expMeasure_coord_nonpos (hr : ∀ i, 0 < r i) (k : ι) :
    Measure.pi (fun i => expMeasure (r i)) {c : ι → ℝ | c k ≤ 0} = 0 :=
  pi_expMeasure_coord (A := Set.Iic 0) hr k (expMeasure_Iic_zero (hr k))

theorem pi_expMeasure_ties (hr : ∀ i, 0 < r i) {i j : ι} (hij : i ≠ j) :
    Measure.pi (fun i => expMeasure (r i)) {c : ι → ℝ | c i = c j} = 0 := by
  have hprob : ∀ i, IsProbabilityMeasure (expMeasure (r i)) := fun i =>
    isProbabilityMeasure_expMeasure (hr i)
  have hmeas : MeasurableSet {c : ι → ℝ | c i = c j} :=
    measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  rw [← (measurePreserving_clockSplit (fun i => expMeasure (r i)) i).map_eq,
    Measure.map_apply (measurable_clockSplit i) hmeas]
  have hpre : clockSplit i ⁻¹' {c : ι → ℝ | c i = c j}
      = {p : ℝ × ({k : ι // k ≠ i} → ℝ) | p.1 = p.2 ⟨j, fun h => hij h.symm⟩} := by
    ext ⟨x, g⟩
    simp [clockSplit_apply, dif_neg (fun h => hij h.symm : j ≠ i)]
  have hms : MeasurableSet
      {p : ℝ × ({k : ι // k ≠ i} → ℝ) | p.1 = p.2 ⟨j, fun h => hij h.symm⟩} :=
    measurableSet_eq_fun measurable_fst ((measurable_pi_apply _).comp measurable_snd)
  rw [hpre, Measure.prod_apply hms]
  refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hms)).2
    (Filter.Eventually.of_forall fun x => ?_)
  have hsec : (Prod.mk x ⁻¹'
      {p : ℝ × ({k : ι // k ≠ i} → ℝ) | p.1 = p.2 ⟨j, fun h => hij h.symm⟩})
      = {g : {k : ι // k ≠ i} → ℝ | g ⟨j, fun h => hij h.symm⟩ = x} := by
    ext g; simp [eq_comm]
  simp only [Pi.zero_apply, hsec]
  exact pi_expMeasure_coord_singleton
    (r := fun k : {k : ι // k ≠ i} => r k.1) (fun k => hr k.1) _ x

/-! ### The law of the race -/

section Winner

variable [MeasurableSpace ι]

/-- A measurable choice of the clock that rings first.  Ties being null, every such choice
gives the same law, so no tie-break has to be fixed. -/
structure IsWinner (w : (ι → ℝ) → ι) : Prop where
  measurable : Measurable w
  le : ∀ (c : ι → ℝ) (i : ι), c (w c) ≤ c i

theorem pi_expMeasure_winner_eq (hr : ∀ i, 0 < r i) {w : (ι → ℝ) → ι} (hw : IsWinner w)
    (i₀ : ι) (t : ℝ) :
    Measure.pi (fun i => expMeasure (r i)) {c | w c = i₀ ∧ t < c (w c)}
      = Measure.pi (fun i => expMeasure (r i)) (winsAfter i₀ t) := by
  have hprob : ∀ i, IsProbabilityMeasure (expMeasure (r i)) := fun i =>
    isProbabilityMeasure_expMeasure (hr i)
  -- winning strictly means being chosen
  have hsub : winsAfter (ι := ι) i₀ t ⊆ {c | w c = i₀ ∧ t < c (w c)} := by
    rintro c ⟨h1, h2⟩
    have hwin : w c = i₀ := by
      by_contra hne
      exact absurd (hw.le c i₀) (not_le.2 (h1 (w c) hne))
    exact ⟨hwin, by rwa [hwin]⟩
  -- and the difference is a tie, which is null
  set T := ⋃ j ∈ ({j | j ≠ i₀} : Set ι), {c : ι → ℝ | c i₀ = c j} with hT
  have hdiff : {c : ι → ℝ | w c = i₀ ∧ t < c (w c)} ⊆ winsAfter i₀ t ∪ T := by
    rintro c ⟨hwin, ht⟩
    have ht' : t < c i₀ := by rwa [hwin] at ht
    by_cases hin : c ∈ winsAfter (ι := ι) i₀ t
    · exact Or.inl hin
    · refine Or.inr ?_
      have hex : ¬ ∀ j, j ≠ i₀ → c i₀ < c j := fun h => hin ⟨h, ht'⟩
      push Not at hex
      obtain ⟨j, hj, hle⟩ := hex
      refine Set.mem_biUnion (show j ∈ ({j | j ≠ i₀} : Set ι) from hj) ?_
      have h1 : c i₀ ≤ c j := by rw [← hwin]; exact hw.le c j
      exact le_antisymm h1 hle
  have hnull : Measure.pi (fun i => expMeasure (r i)) T = 0 := by
    rw [hT]
    refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun j hj => ?_
    exact pi_expMeasure_ties hr (Ne.symm hj)
  refine le_antisymm ?_ (measure_mono hsub)
  calc Measure.pi (fun i => expMeasure (r i)) {c | w c = i₀ ∧ t < c (w c)}
      ≤ Measure.pi (fun i => expMeasure (r i)) (winsAfter i₀ t ∪ T) := measure_mono hdiff
    _ ≤ Measure.pi (fun i => expMeasure (r i)) (winsAfter i₀ t)
        + Measure.pi (fun i => expMeasure (r i)) T := measure_union_le _ _
    _ = Measure.pi (fun i => expMeasure (r i)) (winsAfter i₀ t) := by rw [hnull, add_zero]

/-- **The law of the race, on tails.**  The clock at `i₀` rings first, after time `t`, with
probability `(r i₀ / ∑ r) · e^{-(∑ r) t}` — the product of the chance that `i₀` wins at all
and the tail of an exponential of the total rate.  Winner and winning time are therefore
independent, the winner is drawn from the normalised rates, and the time is exponential of
the total rate: this is the jump-hold form of `SocialNetwork.stepLaw`, read off the clocks. -/
theorem pi_expMeasure_race_Ioi [Nonempty ι] (hr : ∀ i, 0 < r i) {w : (ι → ℝ) → ι}
    (hw : IsWinner w) (i₀ : ι) {t : ℝ} (ht : 0 ≤ t) :
    Measure.pi (fun i => expMeasure (r i)) {c | w c = i₀ ∧ c (w c) ∈ Set.Ioi t}
      = ENNReal.ofReal (r i₀ / ∑ i, r i) * expMeasure (∑ i, r i) (Set.Ioi t) := by
  have hRpos : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hset : {c : ι → ℝ | w c = i₀ ∧ c (w c) ∈ Set.Ioi t}
      = {c : ι → ℝ | w c = i₀ ∧ t < c (w c)} := rfl
  rw [hset, pi_expMeasure_winner_eq hr hw i₀ t, pi_expMeasure_winsAfter hr i₀ ht,
    expMeasure_Ioi_of_nonneg hRpos ht, ← ENNReal.ofReal_mul (div_nonneg (hr i₀).le hRpos.le)]

/-! ### A winner exists

`IsWinner` would be an empty hypothesis without this: ties are null but not impossible, so
the choice has to be made, and measurably.  Breaking ties by an order on the index does it. -/

section FirstClock

variable [Nonempty ι] [LinearOrder ι]

open scoped Classical in
/-- The first clock to ring, ties broken by the order on `ι`. -/
noncomputable def firstClock (c : ι → ℝ) : ι :=
  (Finset.univ.filter fun i => ∀ j, c i ≤ c j).min' (by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_min_image Finset.univ c ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, fun j => hi j (Finset.mem_univ j)⟩⟩)

omit [DecidableEq ι] [MeasurableSpace ι] in
open scoped Classical in
theorem firstClock_mem (c : ι → ℝ) :
    firstClock c ∈ Finset.univ.filter fun i => ∀ j, c i ≤ c j :=
  Finset.min'_mem _ _

omit [DecidableEq ι] [MeasurableSpace ι] in
theorem firstClock_le (c : ι → ℝ) (i : ι) : c (firstClock c) ≤ c i := by
  classical
  have h := firstClock_mem c
  exact (Finset.mem_filter.1 h).2 i

omit [DecidableEq ι] [MeasurableSpace ι] in
open scoped Classical in
theorem firstClock_eq_iff (c : ι → ℝ) (i : ι) :
    firstClock c = i ↔ (∀ j, c i ≤ c j) ∧ ∀ k, (∀ j, c k ≤ c j) → i ≤ k := by
  classical
  set s := Finset.univ.filter fun i => ∀ j, c i ≤ c j with hs
  have hne : s.Nonempty := by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_min_image Finset.univ c ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, fun j => hi j (Finset.mem_univ j)⟩⟩
  constructor
  · rintro rfl
    refine ⟨(Finset.mem_filter.1 (firstClock_mem c)).2, fun k hk => ?_⟩
    exact Finset.min'_le _ k (Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩)
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ (h2 _ (Finset.mem_filter.1 (firstClock_mem c)).2)
    exact Finset.min'_le _ i (Finset.mem_filter.2 ⟨Finset.mem_univ i, h1⟩)

omit [DecidableEq ι] in
theorem measurable_firstClock : Measurable (firstClock (ι := ι)) := by
  refine measurable_to_countable' fun i => ?_
  have hrw : firstClock (ι := ι) ⁻¹' {i}
      = (⋂ j : ι, {c : ι → ℝ | c i ≤ c j})
        ∩ (⋂ k : ι, {c : ι → ℝ | (∀ j, c k ≤ c j) → i ≤ k}) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff, firstClock_eq_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hrw]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_) (MeasurableSet.iInter fun k => ?_)
  · exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  · by_cases hik : i ≤ k
    · simp [hik]
    · have : {c : ι → ℝ | (∀ j, c k ≤ c j) → i ≤ k} = {c : ι → ℝ | ¬ ∀ j, c k ≤ c j} := by
        ext c; simp [hik]
      rw [this, ← Set.compl_ofPred]
      refine MeasurableSet.compl ?_
      have : {c : ι → ℝ | ∀ j, c k ≤ c j} = ⋂ j : ι, {c : ι → ℝ | c k ≤ c j} := by
        ext c; simp [Set.mem_iInter]
      rw [this]
      exact MeasurableSet.iInter fun j =>
        measurableSet_le (measurable_pi_apply k) (measurable_pi_apply j)

omit [DecidableEq ι] in
theorem isWinner_firstClock : IsWinner (firstClock (ι := ι)) where
  measurable := measurable_firstClock
  le := firstClock_le

end FirstClock

end Winner

end SocialNetwork
