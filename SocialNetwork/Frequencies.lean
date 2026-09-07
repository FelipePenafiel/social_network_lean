/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-!
# Uniform opinion sequences and the event `E_ε^k`

The proof of Proposition 18 of arXiv:2607.19651 rewrites a sum over opinion words as an
expectation over an i.i.d. sequence `V₁, V₂, …` of uniform opinions, and then keeps only the
words on which the empirical frequencies have settled:

```
E_ε^k = {(1/M - ε) n ≤ ∑_{m ≤ n} 1_{V_m = o} ≤ (1/M + ε) n  for all n ≥ k and all o ∈ O}.
```

The paper's justification that `P (E_ε^k) > 0` for some `k` is the strong law of large numbers,
and that is what `SocialNetwork.exists_uniformSeq_freqGood_pos` does, with Mathlib's
`ProbabilityTheory.strong_law_ae_real`.

Nothing here mentions the social network: this file is about words over a finite alphabet.

## Main definitions

* `SocialNetwork.occCount` — how often an opinion occurs among the first `n` letters.
* `SocialNetwork.uniformSeq` — the law of an i.i.d. sequence of uniform opinions.
* `SocialNetwork.freqGood` — the event `E_ε^k`.

## Main results

* `SocialNetwork.exists_uniformSeq_freqGood_pos` — `P (E_ε^k) > 0` for some `k`, by the
  strong law of large numbers.
* `SocialNetwork.uniformSeq_freqGood_le` — the counting form used in Proposition 18: at
  every horizon `n`, the words of length `n` that satisfy the constraint up to `n` are at
  least a fraction `P (E_ε^k)` of all `M^n` words.
-/

namespace SocialNetwork

open Filter Finset MeasureTheory ProbabilityTheory

open scoped ENNReal Topology

variable {M : ℕ}

/-! ### Occurrence counts -/

section OccCount

/-- `occCount x o n` is the number of the first `n` letters of the word `x` that are `o`:
the paper's `∑_{m = 1}^{n} 1_{V_m = o}`. -/
def occCount (x : ℕ → Opinion M) (o : Opinion M) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => x i = o).card

theorem occCount_eq_sum (x : ℕ → Opinion M) (o : Opinion M) (n : ℕ) :
    ((occCount x o n : ℕ) : ℝ) = ∑ i ∈ Finset.range n, if x i = o then (1 : ℝ) else 0 :=
  (Finset.sum_boole _ _).symm

theorem occCount_succ (x : ℕ → Opinion M) (o : Opinion M) (n : ℕ) :
    occCount x o (n + 1) = occCount x o n + if x n = o then 1 else 0 := by
  classical
  unfold occCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : x n = o
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem]
    exact fun hmem => absurd (Finset.mem_range.1 (Finset.mem_filter.1 hmem).1) (lt_irrefl n)
  · rw [if_neg h, if_neg h, Nat.add_zero]

theorem occCount_le (x : ℕ → Opinion M) (o : Opinion M) (n : ℕ) : occCount x o n ≤ n := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- The count only reads the first `n` letters. -/
theorem occCount_congr {x y : ℕ → Opinion M} {n : ℕ} (h : ∀ i, i < n → x i = y i)
    (o : Opinion M) (j : ℕ) (hj : j ≤ n) : occCount x o j = occCount y o j := by
  unfold occCount
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [h i (lt_of_lt_of_le (Finset.mem_range.1 hi) hj)]

end OccCount

/-! ### The i.i.d. uniform sequence -/

section Uniform

variable (M)

/-- The uniform law on the opinions. -/
noncomputable def uniformOpinion [NeZero M] : Measure (Opinion M) :=
  (PMF.uniformOfFintype (Opinion M)).toMeasure

instance instIsProbabilityMeasureUniformOpinion [NeZero M] :
    IsProbabilityMeasure (uniformOpinion M) := by
  rw [uniformOpinion]; infer_instance

/-- The law of an i.i.d. sequence `V₁, V₂, …` of uniform opinions. -/
noncomputable def uniformSeq [NeZero M] : Measure (ℕ → Opinion M) :=
  Measure.infinitePi fun _ : ℕ => uniformOpinion M

variable {M}

instance [NeZero M] : IsProbabilityMeasure (uniformSeq M) := by
  rw [uniformSeq]; infer_instance

@[simp]
theorem uniformOpinion_singleton [NeZero M] (o : Opinion M) :
    uniformOpinion M {o} = ((M : ℝ≥0∞))⁻¹ := by
  rw [uniformOpinion, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton o),
    PMF.uniformOfFintype_apply]
  simp

/-- The word of the first `n` letters is uniform on the `M^n` words. -/
theorem uniformSeq_cylinder [NeZero M] (y : ℕ → Opinion M) (n : ℕ) :
    uniformSeq M {x : ℕ → Opinion M | ∀ i, i < n → x i = y i} = ((M : ℝ≥0∞))⁻¹ ^ n := by
  have hset : {x : ℕ → Opinion M | ∀ i, i < n → x i = y i}
      = Set.pi ↑(Finset.range n) fun i => {y i} := by
    ext x
    simp [Set.mem_pi]
  rw [hset, uniformSeq,
    Measure.infinitePi_pi (μ := fun _ : ℕ => uniformOpinion M)
      (mt := fun i _ => measurableSet_singleton (y i))]
  simp

end Uniform

/-! ### The strong law of large numbers -/

section StrongLaw

variable [NeZero M]

omit [NeZero M] in
theorem measurable_occCount (o : Opinion M) (n : ℕ) :
    Measurable fun x : ℕ → Opinion M => ((occCount x o n : ℕ) : ℝ) := by
  simp only [occCount_eq_sum]
  exact Finset.measurable_sum _ fun i _ =>
    (Measurable.of_discrete (f := fun p : Opinion M => if p = o then (1 : ℝ) else 0)).comp
      (measurable_pi_apply i)

/-- **The strong law of large numbers for the empirical frequency of an opinion**, which is
the step the paper takes to know that `E_ε^k` is not negligible. -/
theorem tendsto_occCount_ae (o : Opinion M) :
    ∀ᵐ x ∂(uniformSeq M),
      Tendsto (fun n : ℕ => ((occCount x o n : ℕ) : ℝ) / n) atTop (nhds ((M : ℝ))⁻¹) := by
  classical
  have hmeasg : Measurable (fun p : Opinion M => if p = o then (1 : ℝ) else 0) :=
    Measurable.of_discrete
  have hmeas : ∀ i : ℕ,
      Measurable fun x : ℕ → Opinion M => if x i = o then (1 : ℝ) else 0 :=
    fun i => hmeasg.comp (measurable_pi_apply i)
  have hmap : ∀ i : ℕ,
      (uniformSeq M).map (fun x : ℕ → Opinion M => if x i = o then (1 : ℝ) else 0)
        = (uniformOpinion M).map fun p : Opinion M => if p = o then (1 : ℝ) else 0 := by
    intro i
    rw [show (fun x : ℕ → Opinion M => if x i = o then (1 : ℝ) else 0)
        = (fun p : Opinion M => if p = o then (1 : ℝ) else 0) ∘ fun x : ℕ → Opinion M => x i from
        rfl, ← Measure.map_map hmeasg (measurable_pi_apply i), uniformSeq,
      Measure.infinitePi_map_eval]
  have hident : ∀ i : ℕ,
      IdentDistrib (fun x : ℕ → Opinion M => if x i = o then (1 : ℝ) else 0)
        (fun x : ℕ → Opinion M => if x 0 = o then (1 : ℝ) else 0) (uniformSeq M)
        (uniformSeq M) :=
    fun i => ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, by rw [hmap i, hmap 0]⟩
  have hint : Integrable (fun x : ℕ → Opinion M => if x 0 = o then (1 : ℝ) else 0)
      (uniformSeq M) := by
    refine (integrable_const (1 : ℝ)).mono' (hmeas 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖if x 0 = o then (1 : ℝ) else 0‖ ≤ 1
    split <;> simp
  have hev : (uniformSeq M).map (fun x : ℕ → Opinion M => x 0) = uniformOpinion M := by
    rw [uniformSeq, Measure.infinitePi_map_eval]
  have hmean : ∫ x, (if x 0 = o then (1 : ℝ) else 0) ∂(uniformSeq M) = ((M : ℝ))⁻¹ := by
    have hchange := integral_map (μ := uniformSeq M) (φ := fun x : ℕ → Opinion M => x 0)
      (f := fun p : Opinion M => if p = o then (1 : ℝ) else 0)
      (measurable_pi_apply 0).aemeasurable (by rw [hev]; exact hmeasg.aestronglyMeasurable)
    rw [hev] at hchange
    rw [← hchange, show (fun p : Opinion M => if p = o then (1 : ℝ) else 0)
        = Set.indicator {o} fun _ => (1 : ℝ) by funext p; rw [Set.indicator_apply]; simp,
      integral_indicator_const _ (measurableSet_singleton o)]
    simp [measureReal_def]
  have hslln := strong_law_ae_real
    (fun (i : ℕ) (x : ℕ → Opinion M) => if x i = o then (1 : ℝ) else 0) hint
    (fun i j hij => (iIndepFun_infinitePi
      (X := fun _ : ℕ => fun p : Opinion M => if p = o then (1 : ℝ) else 0)
      fun _ => Measurable.of_discrete).indepFun hij) hident
  rw [hmean] at hslln
  filter_upwards [hslln] with x hx
  refine hx.congr fun n => ?_
  rw [occCount_eq_sum]

end StrongLaw

/-! ### The event `E_ε^k` -/

section FreqGood

variable (M)

/-- The event `E_ε^k` of the proof of Proposition 18: from time `k` on, every opinion has
occurred with a frequency within `ε` of `1/M`.

Only the upper half is used downstream — through the lower bound it gives for the count of
the *other* opinions — but the paper writes both, and so does this. -/
def freqGood [NeZero M] (ε : ℝ) (k : ℕ) : Set (ℕ → Opinion M) :=
  {x | ∀ n, k ≤ n → ∀ o : Opinion M,
    (((M : ℝ))⁻¹ - ε) * n ≤ ((occCount x o n : ℕ) : ℝ) ∧
      ((occCount x o n : ℕ) : ℝ) ≤ (((M : ℝ))⁻¹ + ε) * n}

variable {M}

variable [NeZero M]

theorem measurableSet_freqGood (ε : ℝ) (k : ℕ) : MeasurableSet (freqGood M ε k) := by
  have : freqGood M ε k = ⋂ n : ℕ, ⋂ _ : k ≤ n, ⋂ o : Opinion M,
      ({x | (((M : ℝ))⁻¹ - ε) * n ≤ ((occCount x o n : ℕ) : ℝ)} ∩
        {x | ((occCount x o n : ℕ) : ℝ) ≤ (((M : ℝ))⁻¹ + ε) * n}) := by
    ext x
    simp [freqGood, Set.mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun o => MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const (measurable_occCount o n)
  · exact measurableSet_le (measurable_occCount o n) measurable_const

/-- **`P (E_ε^k) > 0` for some `k`**, which is what the paper reads off the strong law of
large numbers. -/
theorem exists_uniformSeq_freqGood_pos {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < uniformSeq M (freqGood M ε k) := by
  by_contra hcon
  push Not at hcon
  have hnull : ∀ k, uniformSeq M (freqGood M ε k) = 0 :=
    fun k => nonpos_iff_eq_zero.1 (hcon k)
  have hunion : uniformSeq M (⋃ k, freqGood M ε k) = 0 := measure_iUnion_null hnull
  have hae : ∀ᵐ x ∂(uniformSeq M), ∀ o : Opinion M,
      Tendsto (fun n : ℕ => ((occCount x o n : ℕ) : ℝ) / n) atTop (nhds ((M : ℝ))⁻¹) := by
    rw [ae_all_iff]
    exact tendsto_occCount_ae
  have hmem : ∀ᵐ x ∂(uniformSeq M), x ∈ ⋃ k, freqGood M ε k := by
    filter_upwards [hae] with x hx
    have hev : ∀ᶠ n : ℕ in atTop, ∀ o : Opinion M,
        |((occCount x o n : ℕ) : ℝ) / n - ((M : ℝ))⁻¹| < ε := by
      rw [Filter.eventually_all]
      exact fun o => (hx o).eventually (eventually_abs_sub_lt ((M : ℝ))⁻¹ hε)
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hev
    refine Set.mem_iUnion.2 ⟨max k 1, fun n hn o => ?_⟩
    have hn1 : (1 : ℕ) ≤ n := le_trans (le_max_right k 1) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have habs := hk n (le_trans (le_max_left k 1) hn) o
    rw [abs_lt] at habs
    have hcancel : ((occCount x o n : ℕ) : ℝ) / n * n = ((occCount x o n : ℕ) : ℝ) :=
      div_mul_cancel₀ _ hnpos.ne'
    constructor
    · calc (((M : ℝ))⁻¹ - ε) * n
          ≤ ((occCount x o n : ℕ) : ℝ) / n * n := by
            refine mul_le_mul_of_nonneg_right ?_ hnpos.le
            linarith [habs.1]
        _ = ((occCount x o n : ℕ) : ℝ) := hcancel
    · calc ((occCount x o n : ℕ) : ℝ)
          = ((occCount x o n : ℕ) : ℝ) / n * n := hcancel.symm
        _ ≤ (((M : ℝ))⁻¹ + ε) * n := by
            refine mul_le_mul_of_nonneg_right ?_ hnpos.le
            linarith [habs.2]
  have hcompl : uniformSeq M (⋃ k, freqGood M ε k)ᶜ = 0 := hmem
  have htot : uniformSeq M ((⋃ k, freqGood M ε k) ∪ (⋃ k, freqGood M ε k)ᶜ) = 1 := by
    rw [Set.union_compl_self]
    exact measure_univ
  have hle := measure_union_le (μ := uniformSeq M) (⋃ k, freqGood M ε k)
    (⋃ k, freqGood M ε k)ᶜ
  rw [htot, hunion, hcompl] at hle
  simp at hle

end FreqGood

/-! ### Counting the good words of a given length -/

section Counting

variable [NeZero M]

/-- Read a word of length `n` as an infinite sequence, padded after `n`. -/
def extendWord {n : ℕ} (f : Fin n → Opinion M) : ℕ → Opinion M :=
  fun i => if h : i < n then f ⟨i, h⟩ else (0 : Opinion M)

theorem extendWord_apply {n : ℕ} (f : Fin n → Opinion M) {i : ℕ} (h : i < n) :
    extendWord f i = f ⟨i, h⟩ := dif_pos h

open Classical in
/-- The words of length `n` on which the constraint defining `E_ε^k` holds up to time `n`. -/
noncomputable def freqGoodFinset (M : ℕ) [NeZero M] (ε : ℝ) (k n : ℕ) :
    Finset (Fin n → Opinion M) :=
  Finset.univ.filter fun f => ∀ j, j ≤ n → k ≤ j → ∀ o : Opinion M,
    ((occCount (extendWord f) o j : ℕ) : ℝ) ≤ (((M : ℝ))⁻¹ + ε) * j

theorem mem_freqGoodFinset {ε : ℝ} {k n : ℕ} {f : Fin n → Opinion M} :
    f ∈ freqGoodFinset M ε k n ↔ ∀ j, j ≤ n → k ≤ j → ∀ o : Opinion M,
      ((occCount (extendWord f) o j : ℕ) : ℝ) ≤ (((M : ℝ))⁻¹ + ε) * j := by
  classical
  rw [freqGoodFinset, Finset.mem_filter]
  simp

/-- **The counting form of `P (E_ε^k) > 0`.**  At every horizon `n`, the words of length `n`
that meet the constraint of `E_ε^k` up to `n` carry at least the mass `P (E_ε^k)` of the
uniform law on the `M^n` words.  This is what turns the paper's expectation over
`V₁, V₂, …` back into a sum over opinion words. -/
theorem uniformSeq_freqGood_le (ε : ℝ) (k n : ℕ) :
    uniformSeq M (freqGood M ε k)
      ≤ ∑ _f ∈ freqGoodFinset M ε k n, ((M : ℝ≥0∞))⁻¹ ^ n := by
  have hsub : freqGood M ε k ⊆ ⋃ f ∈ freqGoodFinset M ε k n,
      {x : ℕ → Opinion M | ∀ i, i < n → x i = extendWord f i} := by
    intro x hx
    have hxf : ∀ i, i < n → x i = extendWord (fun i : Fin n => x (i : ℕ)) i := fun i hi =>
      (extendWord_apply (fun i : Fin n => x (i : ℕ)) hi).symm
    have hf : (fun i : Fin n => x (i : ℕ)) ∈ freqGoodFinset M ε k n := by
      refine mem_freqGoodFinset.2 fun j hj hkj o => ?_
      rw [← occCount_congr hxf o j hj]
      exact (hx j hkj o).2
    exact Set.mem_biUnion hf hxf
  refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _) ?_)
  exact le_of_eq (Finset.sum_congr rfl fun f _ => uniformSeq_cylinder (extendWord f) n)

end Counting

end SocialNetwork
