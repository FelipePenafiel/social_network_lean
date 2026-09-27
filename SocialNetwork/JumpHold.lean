/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.ContinuousTime

/-!
# Non-explosion for a jump-hold chain with a slow sub-family

A *jump-hold chain* on `ℕ → Step N M` is the shape both models of the paper take in
continuous time: at each step a pair `(a, o)` is drawn from a law depending on the past, and
the holding time that follows is exponential of the total rate at the state reached,
independently of the pair.  `SocialNetwork.ctsPathMeasure` and
`SocialNetwork.Bias.biasedCtsPathMeasure` are two instances of
`SocialNetwork.jumpHoldMeasure`, and everything below is stated for the general one.

## What this file proves

`SocialNetwork.measure_explosionTime_eq_one`.  Distinguish some of the pairs at each state.
If

* every block of `b` consecutive steps carries at least one distinguished step, and
* one step, weighted by `e^{-θH}` and by an extra factor `d > 1` when the pair expressed is
  distinguished, still has total mass at most `1`,

then the jump times are almost surely unbounded: the chain does not explode.

The second hypothesis is what a sub-family of rate at most `λ` provides, with
`d = (λ + θ) / λ`; that computation is `SocialNetwork.lintegral_stepWeight_le_one`, and it is
the only place where the exponential law is used.

## Why this shape

This is the upper half of the sandwich (11) of arXiv:2607.19651, p. 16, which is asserted
there rather than constructed: the expressions coming from actors carrying pressure below `N`
"can be constructed in such a way that" they sit inside a Poisson process of rate
`λ = NMe^{βN}`, and Proposition 5 puts at least one of them in every `N` steps.  What the
proof of Theorem 1.1 uses of that coupling is the domination alone, and the domination is what
is proved here, in the form the conclusion needs: the weight `e^{-θTₙ} d^{Kₙ}`, where `Kₙ`
counts the distinguished steps among the first `n`, is a supermartingale.  So `Tₙ` cannot stay
bounded while `Kₙ` grows, and Markov's inequality turns that into the statement above.  No
Poisson point process is constructed, and none is needed.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

/-! ### The sample space of a jump-hold chain

A realisation is a sequence of steps, each carrying the jump that occurred and the time the
chain then waited.  `SocialNetwork.Step` is the case `J = SocialNetwork.Jump N M`, and every
definition here is the one of `SocialNetwork.ContinuousTime` read at that `J`. -/

/-- One step of a jump-hold chain: the jump, and the holding time that followed it. -/
abbrev Hold (J : Type*) := J × ℝ

variable {J : Type*} [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J]
  [DecidableEq J]

/-- The holding time between the `(n+1)`-st and the `(n+2)`-nd jump. -/
def holdTime (n : ℕ) (ω : ℕ → Hold J) : ℝ := (ω n).2

/-- The time of the `n`-th jump, with the convention `T₀ = 0`. -/
def holdSum (n : ℕ) (ω : ℕ → Hold J) : ℝ := ∑ k ∈ Finset.range n, holdTime k ω

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem holdSum_succ (n : ℕ) (ω : ℕ → Hold J) :
    holdSum (n + 1) ω = holdSum n ω + holdTime n ω :=
  Finset.sum_range_succ _ n

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem measurable_holdSum (n : ℕ) : Measurable (holdSum (J := J) n) :=
  Finset.measurable_sum _ fun k _ => measurable_snd.comp (measurable_pi_apply k)

/-- `sup {Tₘ : m ≥ 1}`, the explosion time of the chain. -/
noncomputable def holdBlowUp (ω : ℕ → Hold J) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal (holdSum n ω)

/-- The first step, read as a history of length one. -/
def holdHistoryZero (z : Hold J) : (i : Finset.Iic 0) → Hold J := fun _ => z

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem measurable_holdHistoryZero : Measurable (holdHistoryZero (J := J)) :=
  measurable_pi_lambda _ fun _ => measurable_id

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
/-- Forgetting the holding times of a finite history is measurable. -/
theorem measurable_holdHistoryJumps (n : ℕ) :
    Measurable fun (h : (i : Finset.Iic n) → Hold J) (i : Finset.Iic n) => (h i).1 :=
  measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)

/-! ### The Laplace transform of one holding time -/

/-- The Laplace transform of an exponential law: `E e^{-bX} = a / (a + b)` for `X` exponential
of rate `a`.  This is `SocialNetwork.lintegral_exp_neg_expMeasure_Ioi` at `t = 0`, the
exponential law giving no mass to the negative half-line. -/
theorem lintegral_exp_neg_expMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(b * x))) ∂(expMeasure a)
      = ENNReal.ofReal (a / (a + b)) := by
  have hcompl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 := by ext x; simp
  rw [← lintegral_add_compl (fun x => ENNReal.ofReal (Real.exp (-(b * x))))
      (measurableSet_Ioi (a := (0 : ℝ))), hcompl,
    setLIntegral_measure_zero _ _ (expMeasure_Iic_zero ha), add_zero,
    lintegral_exp_neg_expMeasure_Ioi ha hb le_rfl]
  simp

/-! ### The discount carried by one step -/

/-- The weight of one step: `e^{-θ H}`, and an extra factor `d` when the pair expressed comes
from the distinguished family `Lo`. -/
noncomputable def stepWeight (D : ℝ≥0∞) (θ : ℝ) (Lo : Finset (J)) (z : Hold J) : ℝ≥0∞ :=
  (if z.1 ∈ Lo then D else 1) * ENNReal.ofReal (Real.exp (-(θ * z.2)))

omit [Countable J] in
theorem measurable_stepWeight (D : ℝ≥0∞) (θ : ℝ) (Lo : Finset (J)) :
    Measurable (stepWeight D θ Lo) := by
  refine Measurable.mul ?_ ?_
  · exact (Measurable.of_discrete
      (f := fun p : J => if p ∈ Lo then D else 1)).comp measurable_fst
  · exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_snd).neg))

omit [Countable J] in
/-- **One step, discounted.**  Take the expressed pair from a law giving the family `Lo` the
fraction `l / R` of the mass, and the holding time exponential of rate `R`, independently.  If
`l ≤ L`, then weighting the step by `e^{-θH}`, and by `(L + θ) / L` when the pair falls in `Lo`,
gives total mass at most `1`.

This is the one estimate the whole argument rests on: a sub-family carrying rate at most `L`
can be discounted at the rate `L` for free. -/
theorem lintegral_stepWeight_le_one {p : PMF (J)} {R L θ l : ℝ} {Lo : Finset (J)}
    (hR : 0 < R) (hL : 0 < L) (hθ : 0 < θ) (hl0 : 0 ≤ l) (hlR : l ≤ R) (hlL : l ≤ L)
    (hmass : p.toMeasure ↑Lo = ENNReal.ofReal (l / R))
    (hmassc : p.toMeasure (↑Lo : Set (J))ᶜ = ENNReal.ofReal ((R - l) / R)) :
    ∫⁻ z, stepWeight (ENNReal.ofReal ((L + θ) / L)) θ Lo z
      ∂(p.toMeasure.prod (expMeasure R)) ≤ 1 := by
  have hprob : IsProbabilityMeasure (expMeasure R) := isProbabilityMeasure_expMeasure hR
  have hf : Measurable fun q : J => if q ∈ Lo then ENNReal.ofReal ((L + θ) / L) else 1 :=
    Measurable.of_discrete
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(θ * x))) := by fun_prop
  simp only [stepWeight]
  rw [lintegral_prod_mul hf.aemeasurable hg.aemeasurable, lintegral_exp_neg_expMeasure hR hθ.le]
  have hjump : ∫⁻ q, (if q ∈ Lo then ENNReal.ofReal ((L + θ) / L) else 1) ∂(p.toMeasure)
      = ENNReal.ofReal ((L + θ) / L) * ENNReal.ofReal (l / R)
        + ENNReal.ofReal ((R - l) / R) := by
    rw [← lintegral_add_compl (fun q : J => if q ∈ Lo then ENNReal.ofReal ((L + θ) / L)
      else 1) (MeasurableSet.of_discrete (s := (↑Lo : Set (J))))]
    congr 1
    · rw [setLIntegral_congr_fun MeasurableSet.of_discrete
        (g := fun _ => ENNReal.ofReal ((L + θ) / L)) fun q hq => by
          rw [if_pos (by exact_mod_cast hq)], setLIntegral_const, hmass]
    · rw [setLIntegral_congr_fun MeasurableSet.of_discrete (g := fun _ => (1 : ℝ≥0∞))
        fun q hq => by rw [if_neg (by simpa using hq)], setLIntegral_const, hmassc, one_mul]
  rw [hjump]
  have hsum : ENNReal.ofReal ((L + θ) / L) * ENNReal.ofReal (l / R)
      + ENNReal.ofReal ((R - l) / R)
      = ENNReal.ofReal ((L + θ) / L * (l / R) + (R - l) / R) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
  rw [hsum, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_one.2 ?_
  have key : ((L + θ) / L * (l / R) + (R - l) / R) * (R / (R + θ))
      = (R + θ * l / L) / (R + θ) := by
    field_simp
    ring
  rw [key, div_le_one (by linarith)]
  have hstep : θ * l / L ≤ θ := by
    rw [div_le_iff₀ hL]
    nlinarith

  linarith

/-! ### Histories read as realisations -/

/-- A finite history, read as a realisation by repeating its last step. -/
def stepExtend {n : ℕ} (h : (i : Finset.Iic n) → Hold J) : ℕ → Hold J :=
  fun k => h ⟨min k n, Finset.mem_Iic.2 (min_le_right k n)⟩

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem stepExtend_apply {n : ℕ} (h : (i : Finset.Iic n) → Hold J) {k : ℕ} (hk : k ≤ n) :
    stepExtend h k = h ⟨k, Finset.mem_Iic.2 hk⟩ := by
  simp only [stepExtend]
  congr 1
  exact Subtype.ext (min_eq_left hk)

/-- A finite history of expressed pairs, read as a realisation by repeating its last pair. -/
def jumpExtend {n : ℕ} (g : (i : Finset.Iic n) → J) : ℕ → J :=
  fun k => g ⟨min k n, Finset.mem_Iic.2 (min_le_right k n)⟩

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem jumpExtend_apply {n : ℕ} (g : (i : Finset.Iic n) → J) {k : ℕ} (hk : k ≤ n) :
    jumpExtend g k = g ⟨k, Finset.mem_Iic.2 hk⟩ := by
  simp only [jumpExtend]
  congr 1
  exact Subtype.ext (min_eq_left hk)

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem jumps_stepExtend {n : ℕ} (h : (i : Finset.Iic n) → Hold J) :
    (fun k => (stepExtend h k).1) = jumpExtend fun i => (h i).1 := rfl

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem stepExtend_frestrictLe {n : ℕ} (ω : ℕ → Hold J) {k : ℕ} (hk : k ≤ n) :
    stepExtend (Preorder.frestrictLe (π := fun _ : ℕ => Hold J) n ω) k = ω k := by
  rw [stepExtend_apply _ hk]
  rfl

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem holdSum_congr {ω ω' : ℕ → Hold J} {n : ℕ} (h : ∀ i < n, ω i = ω' i) :
    holdSum n ω = holdSum n ω' :=
  Finset.sum_congr rfl fun k hk => by
    show (ω k).2 = (ω' k).2
    rw [h k (Finset.mem_range.1 hk)]

/-! ### The discounted weight of a run -/

section Discount

variable (low : ℕ → (ℕ → J) → Prop) [∀ k j, Decidable (low k j)]

/-- How many of the first `n` steps are distinguished. -/
def lowCountOf (n : ℕ) (j : ℕ → J) : ℕ := #{k ∈ Finset.range n | low k j}

variable {low}

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem lowCountOf_congr (hlow : ∀ (k : ℕ) (j j' : ℕ → J),
    (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j')) {j j' : ℕ → J} {n : ℕ}
    (h : ∀ i < n, j i = j' i) : lowCountOf low n j = lowCountOf low n j' := by
  unfold lowCountOf
  congr 1
  refine Finset.filter_congr fun k hk => ?_
  have hk' : k < n := Finset.mem_range.1 hk
  exact hlow k j j' fun i hi => h i (by omega)

variable (low)

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
/-- The last of `n + 1` steps is counted separately. -/
theorem lowCountOf_succ (n : ℕ) (j : ℕ → J) :
    lowCountOf low (n + 1) j = lowCountOf low n j + (if low n j then 1 else 0) := by
  unfold lowCountOf
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hn : low n j
  · rw [if_pos hn, if_pos hn, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg hn, if_neg hn, add_zero]

/-- The weight `e^{-θ Tₙ} d^{Kₙ}` of the first `n` steps, where `Kₙ` counts the distinguished
steps among them. -/
noncomputable def discountOf (D : ℝ≥0∞) (θ : ℝ) (n : ℕ) (ω : ℕ → Hold J) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(θ * holdSum n ω))) * D ^ lowCountOf low n fun k => (ω k).1

/-- The weight of a history of `n + 1` steps. -/
noncomputable def histDiscountOf (D : ℝ≥0∞) (θ : ℝ) (n : ℕ)
    (h : (i : Finset.Iic n) → Hold J) : ℝ≥0∞ :=
  discountOf low D θ (n + 1) (stepExtend h)

variable {low}

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem discountOf_congr (hlow : ∀ (k : ℕ) (j j' : ℕ → J),
    (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j')) {D : ℝ≥0∞} {θ : ℝ} {n : ℕ}
    {ω ω' : ℕ → Hold J} (h : ∀ i < n, ω i = ω' i) :
    discountOf low D θ n ω = discountOf low D θ n ω' := by
  rw [discountOf, discountOf, holdSum_congr h,
    lowCountOf_congr hlow fun i hi => by rw [h i hi]]

variable (low)

omit [DecidableEq J] in
theorem measurable_histDiscountOf (D : ℝ≥0∞) (θ : ℝ) (n : ℕ) :
    Measurable (histDiscountOf low D θ n) := by
  unfold histDiscountOf discountOf
  have hsum : Measurable fun h : (i : Finset.Iic n) → Hold J =>
      holdSum (n + 1) (stepExtend h) := by
    simp only [holdSum, holdTime, stepExtend]
    exact Finset.measurable_sum _ fun k _ => measurable_snd.comp (measurable_pi_apply _)
  have htime : Measurable fun h : (i : Finset.Iic n) → Hold J =>
      ENNReal.ofReal (Real.exp (-(θ * holdSum (n + 1) (stepExtend h)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hsum.const_mul θ).neg)
  have hcount : Measurable fun h : (i : Finset.Iic n) → Hold J =>
      lowCountOf low (n + 1) fun k => (stepExtend h k).1 := by
    simp only [jumps_stepExtend]
    exact (Measurable.of_discrete (f := fun g : (i : Finset.Iic n) → J =>
      lowCountOf low (n + 1) (jumpExtend g))).comp (measurable_holdHistoryJumps n)
  exact htime.mul ((Measurable.of_discrete (f := fun m : ℕ => D ^ m)).comp hcount)

end Discount

/-! ### The chain and its finite-dimensional laws -/

section Chain

variable (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Hold J) (Hold J))
  [∀ n, IsMarkovKernel (κ n)] (ν : Measure (Hold J)) [IsProbabilityMeasure ν]

/-- The law of a realisation of a jump-hold chain: the first step follows `ν`, and the step
after a history `h` follows `κ n h`.  Its existence is the Ionescu-Tulcea theorem. -/
noncomputable def jumpHoldMeasure : Measure (ℕ → Hold J) :=
  Kernel.traj (X := fun _ : ℕ => Hold J) κ 0 ∘ₘ (ν.map holdHistoryZero)

/-- The law of the first `n + 1` steps. -/
noncomputable def jumpHoldHistory (n : ℕ) : Measure ((i : Finset.Iic n) → Hold J) :=
  Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ 0 n ∘ₘ (ν.map holdHistoryZero)

instance isProbabilityMeasure_jumpHoldMeasure : IsProbabilityMeasure (jumpHoldMeasure κ ν) := by
  rw [jumpHoldMeasure]
  have : IsProbabilityMeasure (ν.map (holdHistoryZero (J := J))) :=
    Measure.isProbabilityMeasure_map measurable_holdHistoryZero.aemeasurable
  infer_instance

instance isProbabilityMeasure_jumpHoldHistory (n : ℕ) :
    IsProbabilityMeasure (jumpHoldHistory κ ν n) := by
  rw [jumpHoldHistory]
  have : IsProbabilityMeasure (ν.map (holdHistoryZero (J := J))) :=
    Measure.isProbabilityMeasure_map measurable_holdHistoryZero.aemeasurable
  infer_instance

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
omit [IsProbabilityMeasure ν] in
theorem jumpHoldMeasure_map_frestrictLe (n : ℕ) :
    (jumpHoldMeasure κ ν).map (Preorder.frestrictLe (π := fun _ : ℕ => Hold J) n)
      = jumpHoldHistory κ ν n := by
  unfold jumpHoldMeasure jumpHoldHistory
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe n), Kernel.traj_map_frestrictLe]

omit [DecidableEq J] in
/-- Under one step of the kernel the past is almost surely the history it started from. -/
theorem partialTraj_ae_history_eq (n : ℕ) (h : (i : Finset.Iic n) → Hold J) :
    ∀ᵐ x ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h),
      Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h := by
  have hmeas : MeasurableSet (Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J)
      (Nat.le_succ n) ⁻¹' {h}) :=
    (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Hold J) (Nat.le_succ n))
      (measurableSet_singleton h)
  have hone : Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) ⁻¹' {h}) = 1 := by
    rw [← Measure.map_apply (Preorder.measurable_frestrictLe₂
        (X := fun _ : ℕ => Hold J) (Nat.le_succ n)) (measurableSet_singleton h),
      Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Hold J) h (Nat.le_succ n),
      Kernel.partialTraj_self, Kernel.id_apply]
    exact Measure.dirac_apply_of_mem rfl
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff hmeas).2 hone

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
/-- Under one step of the kernel the new coordinate follows the law that kernel prescribes. -/
theorem partialTraj_map_lastStep (n : ℕ) (h : (i : Finset.Iic n) → Hold J) :
    (Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h).map
        (fun x : (i : Finset.Iic (n + 1)) → Hold J => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      = κ n h := by
  rw [← Kernel.map_apply _ (measurable_pi_apply _), Kernel.map_partialTraj_succ_self]

end Chain

/-! ### The supermartingale -/

section Supermartingale

variable {low : ℕ → (ℕ → J) → Prop} [∀ k j, Decidable (low k j)] {D : ℝ≥0∞} {θ : ℝ}

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] in
/-- **The weight of one more step.**  The weight of a history of `n + 2` steps is the weight of
the history it restricts to, times the weight of the step just taken. -/
theorem histDiscountOf_succ (hlow : ∀ (k : ℕ) (j j' : ℕ → J),
      (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j'))
    {n : ℕ} {h : (i : Finset.Iic n) → Hold J} {x : (i : Finset.Iic (n + 1)) → Hold J}
    {Lo : Finset (J)}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h)
    (hsucc : low (n + 1) (fun k => (stepExtend x k).1)
      ↔ (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1 ∈ Lo) :
    histDiscountOf low D θ (n + 1) x
      = histDiscountOf low D θ n h * stepWeight D θ Lo (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  set z := x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ with hz
  have hagree : ∀ i < n + 1, stepExtend x i = stepExtend h i := by
    intro i hi
    rw [stepExtend_apply _ (show i ≤ n + 1 by omega), stepExtend_apply _ (show i ≤ n by omega),
      ← hx]
    rfl
  have hlast : stepExtend x (n + 1) = z := stepExtend_apply _ le_rfl
  have htime : holdSum (n + 2) (stepExtend x) = holdSum (n + 1) (stepExtend h) + z.2 := by
    rw [holdSum_succ, holdSum_congr hagree]
    congr 1
    show (stepExtend x (n + 1)).2 = z.2
    rw [hlast]
  have hcount : lowCountOf low (n + 2) (fun k => (stepExtend x k).1)
      = lowCountOf low (n + 1) (fun k => (stepExtend h k).1) + (if z.1 ∈ Lo then 1 else 0) := by
    rw [lowCountOf_succ, lowCountOf_congr hlow (fun i hi => by rw [hagree i hi])]
    congr 1
    exact if_congr hsucc rfl rfl
  rw [histDiscountOf, histDiscountOf, discountOf, discountOf, htime, hcount, stepWeight]
  rw [show -(θ * (holdSum (n + 1) (stepExtend h) + z.2))
      = -(θ * holdSum (n + 1) (stepExtend h)) + -(θ * z.2) by ring, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le, pow_add]
  split
  · rw [pow_one]; ring
  · rw [pow_zero]; ring

variable (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Hold J) (Hold J))
  [∀ n, IsMarkovKernel (κ n)]

/-- **One step of the kernel does not increase the weight.** -/
theorem lintegral_partialTraj_histDiscountOf_le
    (hlow : ∀ (k : ℕ) (j j' : ℕ → J), (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j'))
    (Lo : (n : ℕ) → ((i : Finset.Iic n) → Hold J) → Finset (J))
    (hsucc : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J)
      (x : (i : Finset.Iic (n + 1)) → Hold J),
      Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h →
        (low (n + 1) (fun k => (stepExtend x k).1)
          ↔ (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1 ∈ Lo n h))
    (hκ : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J),
      ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) ≤ 1)
    (n : ℕ) (h : (i : Finset.Iic n) → Hold J) :
    ∫⁻ x, histDiscountOf low D θ (n + 1) x
        ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h)
      ≤ histDiscountOf low D θ n h := by
  calc ∫⁻ x, histDiscountOf low D θ (n + 1) x
        ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h)
      = ∫⁻ x, histDiscountOf low D θ n h
          * stepWeight D θ (Lo n h) (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
        ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h) := by
        refine lintegral_congr_ae ?_
        filter_upwards [partialTraj_ae_history_eq κ n h] with x hx
        exact histDiscountOf_succ hlow hx (hsucc n h x hx)
    _ = histDiscountOf low D θ n h * ∫⁻ x, stepWeight D θ (Lo n h)
          (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
        ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h) :=
        lintegral_const_mul _ ((measurable_stepWeight D θ (Lo n h)).comp
          (measurable_pi_apply _))
    _ = histDiscountOf low D θ n h * ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) := by
        have hmap : ∫⁻ x, stepWeight D θ (Lo n h) (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
            ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h)
            = ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) := by
          rw [← partialTraj_map_lastStep κ n h]
          exact (lintegral_map (measurable_stepWeight D θ (Lo n h))
            (measurable_pi_apply (⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic (n + 1)))).symm
        rw [hmap]
    _ ≤ histDiscountOf low D θ n h * 1 := by gcongr; exact hκ n h
    _ = histDiscountOf low D θ n h := mul_one _

variable (ν : Measure (Hold J)) [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- **The weight is a supermartingale.**  Its expectation stays at most `1`. -/
theorem lintegral_histDiscountOf_le_one
    (hlow : ∀ (k : ℕ) (j j' : ℕ → J), (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j'))
    (Lo : (n : ℕ) → ((i : Finset.Iic n) → Hold J) → Finset (J))
    (Lo₀ : Finset (J))
    (hbase : ∀ z : Hold J, low 0 (fun _ => z.1) ↔ z.1 ∈ Lo₀)
    (hsucc : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J)
      (x : (i : Finset.Iic (n + 1)) → Hold J),
      Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h →
        (low (n + 1) (fun k => (stepExtend x k).1)
          ↔ (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1 ∈ Lo n h))
    (hν : ∫⁻ z, stepWeight D θ Lo₀ z ∂ν ≤ 1)
    (hκ : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J),
      ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) ≤ 1)
    (n : ℕ) :
    ∫⁻ h, histDiscountOf low D θ n h ∂(jumpHoldHistory κ ν n) ≤ 1 := by
  induction n with
  | zero =>
      have hzero : ∀ z : Hold J, histDiscountOf low D θ 0 (holdHistoryZero z)
          = stepWeight D θ Lo₀ z := by
        intro z
        have htime : holdSum 1 (stepExtend (holdHistoryZero z)) = z.2 := by
          simp [holdSum, holdTime, stepExtend, holdHistoryZero]
        have hcount : lowCountOf low 1 (fun k => (stepExtend (holdHistoryZero z) k).1)
            = if z.1 ∈ Lo₀ then 1 else 0 := by
          rw [lowCountOf_succ]
          simp only [lowCountOf, Finset.range_zero, Finset.filter_empty, Finset.card_empty,
            Nat.zero_add]
          exact if_congr (hbase z) rfl rfl
        rw [histDiscountOf, discountOf, htime, hcount, stepWeight]
        by_cases hP : z.1 ∈ Lo₀
        · rw [if_pos hP, if_pos hP, pow_one, mul_comm]
        · rw [if_neg hP, if_neg hP, pow_zero, mul_one, one_mul]
      unfold jumpHoldHistory
      rw [Kernel.partialTraj_self, Measure.id_comp,
        lintegral_map (measurable_histDiscountOf low D θ 0) measurable_holdHistoryZero]
      calc ∫⁻ z, histDiscountOf low D θ 0 (holdHistoryZero z) ∂ν
          = ∫⁻ z, stepWeight D θ Lo₀ z ∂ν := lintegral_congr hzero
        _ ≤ 1 := hν
  | succ n ih =>
      have hstep : ∫⁻ x, histDiscountOf low D θ (n + 1) x ∂(jumpHoldHistory κ ν (n + 1))
          = ∫⁻ h, (∫⁻ x, histDiscountOf low D θ (n + 1) x
              ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h))
            ∂(jumpHoldHistory κ ν n) := by
        unfold jumpHoldHistory
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc]
        exact Measure.lintegral_bind (Kernel.aemeasurable _)
          (measurable_histDiscountOf low D θ (n + 1)).aemeasurable
      rw [hstep]
      calc ∫⁻ h, (∫⁻ x, histDiscountOf low D θ (n + 1) x
              ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) κ n (n + 1) h))
            ∂(jumpHoldHistory κ ν n)
          ≤ ∫⁻ h, histDiscountOf low D θ n h ∂(jumpHoldHistory κ ν n) :=
            lintegral_mono fun h =>
              lintegral_partialTraj_histDiscountOf_le κ hlow Lo hsucc hκ n h
        _ ≤ 1 := ih

/-- The same bound, read on the sample space of the chain. -/
theorem lintegral_discountOf_le_one
    (hlow : ∀ (k : ℕ) (j j' : ℕ → J), (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j'))
    (Lo : (n : ℕ) → ((i : Finset.Iic n) → Hold J) → Finset (J))
    (Lo₀ : Finset (J))
    (hbase : ∀ z : Hold J, low 0 (fun _ => z.1) ↔ z.1 ∈ Lo₀)
    (hsucc : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J)
      (x : (i : Finset.Iic (n + 1)) → Hold J),
      Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h →
        (low (n + 1) (fun k => (stepExtend x k).1)
          ↔ (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1 ∈ Lo n h))
    (hν : ∫⁻ z, stepWeight D θ Lo₀ z ∂ν ≤ 1)
    (hκ : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J),
      ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) ≤ 1)
    (n : ℕ) :
    ∫⁻ ω, discountOf low D θ n ω ∂(jumpHoldMeasure κ ν) ≤ 1 := by
  cases n with
  | zero =>
      have hone : ∀ ω : ℕ → Hold J, discountOf low D θ 0 ω = 1 := by
        intro ω
        rw [discountOf]
        simp [lowCountOf, holdSum]
      rw [lintegral_congr hone, lintegral_const, measure_univ, mul_one]
  | succ n =>
      have heq : ∀ ω : ℕ → Hold J, discountOf low D θ (n + 1) ω
          = histDiscountOf low D θ n (Preorder.frestrictLe (π := fun _ : ℕ => Hold J) n ω) :=
        fun ω => discountOf_congr hlow fun i hi =>
          (stepExtend_frestrictLe ω (show i ≤ n by omega)).symm
      calc ∫⁻ ω, discountOf low D θ (n + 1) ω ∂(jumpHoldMeasure κ ν)
          = ∫⁻ ω, histDiscountOf low D θ n
              (Preorder.frestrictLe (π := fun _ : ℕ => Hold J) n ω) ∂(jumpHoldMeasure κ ν) :=
            lintegral_congr heq
        _ = ∫⁻ h, histDiscountOf low D θ n h ∂(jumpHoldHistory κ ν n) := by
            rw [← jumpHoldMeasure_map_frestrictLe κ ν n,
              lintegral_map (measurable_histDiscountOf low D θ n)
                (Preorder.measurable_frestrictLe n)]
        _ ≤ 1 := lintegral_histDiscountOf_le_one κ ν hlow Lo Lo₀ hbase hsucc hν hκ n

end Supermartingale

/-! ### Non-explosion -/

section NoExplosion

variable {low : ℕ → (ℕ → J) → Prop} [∀ k j, Decidable (low k j)] {D : ℝ≥0∞} {θ : ℝ}
  (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → Hold J) (Hold J))
  [∀ n, IsMarkovKernel (κ n)] (ν : Measure (Hold J)) [IsProbabilityMeasure ν]

/-- **Markov's inequality along the blocks.**  If every block of `b` steps carries at least one
distinguished step, the `qb`-th jump happens before time `t` with probability at most
`e^{θt} d^{-q}`. -/
theorem jumpHoldMeasure_holdSum_le
    (hlow : ∀ (k : ℕ) (j j' : ℕ → J), (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j'))
    (Lo : (n : ℕ) → ((i : Finset.Iic n) → Hold J) → Finset (J))
    (Lo₀ : Finset (J))
    (hbase : ∀ z : Hold J, low 0 (fun _ => z.1) ↔ z.1 ∈ Lo₀)
    (hsucc : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J)
      (x : (i : Finset.Iic (n + 1)) → Hold J),
      Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h →
        (low (n + 1) (fun k => (stepExtend x k).1)
          ↔ (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1 ∈ Lo n h))
    (hν : ∫⁻ z, stepWeight D θ Lo₀ z ∂ν ≤ 1)
    (hκ : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J),
      ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) ≤ 1)
    (hθ : 0 < θ) (hD : 1 ≤ D) {b : ℕ}
    (hblocks : ∀ (j : ℕ → J) (q : ℕ), q ≤ lowCountOf low (q * b) j)
    (t : ℝ) (q : ℕ) :
    jumpHoldMeasure κ ν {ω | holdSum (q * b) ω ≤ t}
      ≤ ENNReal.ofReal (Real.exp (θ * t)) * D⁻¹ ^ q := by
  set A : Set (ℕ → Hold J) := {ω | holdSum (q * b) ω ≤ t} with hA
  have hmeasA : MeasurableSet A := measurableSet_le (measurable_holdSum _) measurable_const
  have hpt : ∀ ω : ℕ → Hold J,
      A.indicator (fun _ => ENNReal.ofReal (Real.exp (-(θ * t))) * D ^ q) ω
        ≤ discountOf low D θ (q * b) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, discountOf]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) ?_
      · have hle : holdSum (q * b) ω ≤ t := hω
        nlinarith
      · exact pow_le_pow_right₀ hD (hblocks _ q)
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hmass : ENNReal.ofReal (Real.exp (-(θ * t))) * D ^ q * jumpHoldMeasure κ ν A ≤ 1 := by
    calc ENNReal.ofReal (Real.exp (-(θ * t))) * D ^ q * jumpHoldMeasure κ ν A
        = ∫⁻ ω, A.indicator (fun _ => ENNReal.ofReal (Real.exp (-(θ * t))) * D ^ q) ω
            ∂(jumpHoldMeasure κ ν) := by
          rw [lintegral_indicator hmeasA, setLIntegral_const]
      _ ≤ ∫⁻ ω, discountOf low D θ (q * b) ω ∂(jumpHoldMeasure κ ν) := lintegral_mono hpt
      _ ≤ 1 := lintegral_discountOf_le_one κ ν hlow Lo Lo₀ hbase hsucc hν hκ _
  have hinv : jumpHoldMeasure κ ν A ≤ (ENNReal.ofReal (Real.exp (-(θ * t))) * D ^ q)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le, mul_comm]
    exact hmass
  refine le_trans hinv (le_of_eq ?_)
  rw [ENNReal.mul_inv (Or.inl (by simp [Real.exp_pos])) (Or.inl (by simp)),
    ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg, ENNReal.inv_pow]

/-- **A jump-hold chain with a slow sub-family does not explode.**  Suppose every block of `b`
consecutive steps carries at least one distinguished step, and that discounting the
distinguished steps by a factor `d > 1` costs nothing.  Then the jump times are almost surely
unbounded. -/
theorem measure_holdBlowUp_eq_one
    (hlow : ∀ (k : ℕ) (j j' : ℕ → J), (∀ i ≤ k, j i = j' i) → (low k j ↔ low k j'))
    (Lo : (n : ℕ) → ((i : Finset.Iic n) → Hold J) → Finset (J))
    (Lo₀ : Finset (J))
    (hbase : ∀ z : Hold J, low 0 (fun _ => z.1) ↔ z.1 ∈ Lo₀)
    (hsucc : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J)
      (x : (i : Finset.Iic (n + 1)) → Hold J),
      Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.le_succ n) x = h →
        (low (n + 1) (fun k => (stepExtend x k).1)
          ↔ (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).1 ∈ Lo n h))
    (hν : ∫⁻ z, stepWeight D θ Lo₀ z ∂ν ≤ 1)
    (hκ : ∀ (n : ℕ) (h : (i : Finset.Iic n) → Hold J),
      ∫⁻ z, stepWeight D θ (Lo n h) z ∂(κ n h) ≤ 1)
    (hθ : 0 < θ) (hD : 1 < D) {b : ℕ}
    (hblocks : ∀ (j : ℕ → J) (q : ℕ), q ≤ lowCountOf low (q * b) j) :
    jumpHoldMeasure κ ν {ω | holdBlowUp ω = ⊤} = 1 := by
  -- the jump times are almost surely not all below a given bound
  have hbounded : ∀ t : ℝ, jumpHoldMeasure κ ν {ω | ∀ n, holdSum n ω ≤ t} = 0 := by
    intro t
    have hsub : ∀ q : ℕ, {ω : ℕ → Hold J | ∀ n, holdSum n ω ≤ t}
        ⊆ {ω | holdSum (q * b) ω ≤ t} := fun q ω hω => hω (q * b)
    have hbound : ∀ q : ℕ, jumpHoldMeasure κ ν {ω | ∀ n, holdSum n ω ≤ t}
        ≤ ENNReal.ofReal (Real.exp (θ * t)) * D⁻¹ ^ q := fun q =>
      le_trans (measure_mono (hsub q))
        (jumpHoldMeasure_holdSum_le κ ν hlow Lo Lo₀ hbase hsucc hν hκ hθ hD.le hblocks t q)
    have hlim : Filter.Tendsto (fun q : ℕ => ENNReal.ofReal (Real.exp (θ * t)) * D⁻¹ ^ q)
        Filter.atTop (nhds 0) := by
      have hzero := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := D⁻¹) (ENNReal.inv_lt_one.2 hD)
      have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (θ * t))) hzero
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at hmul
    exact le_antisymm (ge_of_tendsto' hlim hbound) (zero_le)
  -- and a finite explosion time would bound them all
  have hmeasExp : Measurable (holdBlowUp (J := J)) := by
    unfold holdBlowUp
    exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_holdSum n)
  have hmeas : MeasurableSet {ω : ℕ → Hold J | holdBlowUp ω = ⊤} :=
    hmeasExp (measurableSet_singleton ⊤)
  refine (prob_compl_eq_zero_iff hmeas).1 ?_
  have hcover : {ω : ℕ → Hold J | holdBlowUp ω = ⊤}ᶜ
      ⊆ ⋃ k : ℕ, {ω : ℕ → Hold J | ∀ n, holdSum n ω ≤ (k : ℝ)} := by
    intro ω hω
    have hne : holdBlowUp ω ≠ ⊤ := hω
    have hle : ∀ n, holdSum n ω ≤ (holdBlowUp ω).toReal := by
      intro n
      have hb : ENNReal.ofReal (holdSum n ω) ≤ holdBlowUp ω :=
        le_iSup (fun m : ℕ => ENNReal.ofReal (holdSum m ω)) n
      exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hb
    exact Set.mem_iUnion.2 ⟨⌈(holdBlowUp ω).toReal⌉₊,
      fun n => le_trans (hle n) (Nat.le_ceil _)⟩
  exact measure_mono_null hcover (measure_iUnion_null fun k => hbounded (k : ℝ))

end NoExplosion

/-! ### A chain driven by a state, and its restart

Both chains of this development have the same shape: a state space, a rule moving the state
along a jump, and a law of one step read at the current state.  `SocialNetwork.ctsPathMeasure`
is the case of the matrices and `SocialNetwork.stepLaw`; the mark chain of
`SocialNetwork.Graphical` is the case of the band.  The restart at the first step is proved
once, here. -/

section Driven

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (next : S → J → S) (L : S → Measure (Hold J))

/-- The state after `n` jumps. -/
def stateAfterJumps (s : S) (j : ℕ → J) : ℕ → S
  | 0 => s
  | n + 1 => next (stateAfterJumps s j n) (j n)

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
@[simp]
theorem stateAfterJumps_zero (s : S) (j : ℕ → J) : stateAfterJumps next s j 0 = s := rfl

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem stateAfterJumps_succ (s : S) (j : ℕ → J) (n : ℕ) :
    stateAfterJumps next s j (n + 1) = next (stateAfterJumps next s j n) (j n) := rfl

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem stateAfterJumps_congr (s : S) {j j' : ℕ → J} :
    ∀ n : ℕ, (∀ k < n, j k = j' k) → stateAfterJumps next s j n = stateAfterJumps next s j' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [stateAfterJumps_succ, stateAfterJumps_succ, ih fun k hk => h k (by omega),
        h n (by omega)]

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Running `n + k` jumps is running `n` of them and then running the rest from there. -/
theorem stateAfterJumps_add (s : S) (j : ℕ → J) (n k : ℕ) :
    stateAfterJumps next s j (n + k)
      = stateAfterJumps next (stateAfterJumps next s j n) (fun i => j (n + i)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show n + (k + 1) = n + k + 1 by ring, stateAfterJumps_succ, ih,
        stateAfterJumps_succ]

omit [DecidableEq J] [DiscreteMeasurableSpace S] in
theorem measurable_stateAfterJumpsHistory (s : S) (n k : ℕ) :
    Measurable fun h : (i : Finset.Iic n) → Hold J =>
      stateAfterJumps next s (jumpExtend fun i => (h i).1) k :=
  (Measurable.of_discrete (f := fun g : (i : Finset.Iic n) → J =>
    stateAfterJumps next s (jumpExtend g) k)).comp (measurable_holdHistoryJumps n)

/-- The kernel driving the chain: replay the jumps so far, and read the law at the state they
reach. -/
noncomputable def drivenKernel (s : S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Hold J) (Hold J) where
  toFun h := L (stateAfterJumps next s (jumpExtend fun i => (h i).1) (n + 1))
  measurable' :=
    (Measurable.of_discrete (f := fun t : S => L t)).comp
      (measurable_stateAfterJumpsHistory next s n (n + 1))

omit [DecidableEq J] in
theorem drivenKernel_apply (s : S) (n : ℕ) (h : (i : Finset.Iic n) → Hold J) :
    drivenKernel next L s n h
      = L (stateAfterJumps next s (jumpExtend fun i => (h i).1) (n + 1)) := rfl

instance isMarkovKernel_drivenKernel [∀ t : S, IsProbabilityMeasure (L t)] (s : S) (n : ℕ) :
    IsMarkovKernel (drivenKernel next L s n) :=
  ⟨fun h => by rw [drivenKernel_apply]; infer_instance⟩

/-- The law of a realisation of the chain started at `s`. -/
noncomputable def drivenMeasure [∀ t : S, IsProbabilityMeasure (L t)] (s : S) :
    Measure (ℕ → Hold J) :=
  jumpHoldMeasure (drivenKernel next L s) (L s)

instance isProbabilityMeasure_drivenMeasure [∀ t : S, IsProbabilityMeasure (L t)] (s : S) :
    IsProbabilityMeasure (drivenMeasure next L s) := by
  rw [drivenMeasure]; infer_instance

end Driven

/-! ### The restart at the first jump -/

section Restart

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (next : S → J → S) (L : S → Measure (Hold J)) [∀ t : S, IsProbabilityMeasure (L t)]

/-- The realisation shifted past its first step. -/
def shiftHold (ω : ℕ → Hold J) : ℕ → Hold J := fun i => ω (1 + i)

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem measurable_shiftHold : Measurable (shiftHold (J := J)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (1 + i)

/-- A history of the first `n + 2` steps, shifted past its first entry. -/
def shiftHoldHistory (n : ℕ) (x : (i : Finset.Iic (n + 1)) → Hold J) :
    (i : Finset.Iic n) → Hold J :=
  fun i => x ⟨1 + i.1, Finset.mem_Iic.2 (by have := Finset.mem_Iic.1 i.2; omega)⟩

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem measurable_shiftHoldHistory (n : ℕ) : Measurable (shiftHoldHistory (J := J) n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- A history of the first `n + 1` steps, extended by one more step. -/
def extendHoldHistory {n : ℕ} (x : (i : Finset.Iic n) → Hold J) (z : Hold J) :
    (i : Finset.Iic (n + 1)) → Hold J :=
  fun i => if h : i.1 ≤ n then x ⟨i.1, Finset.mem_Iic.2 h⟩ else z

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem measurable_extendHoldHistory {n : ℕ} (x : (i : Finset.Iic n) → Hold J) :
    Measurable (extendHoldHistory x) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.1 ≤ n
  · simp [extendHoldHistory, h]
  · simpa [extendHoldHistory, h] using measurable_id'

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem shiftHoldHistory_extendHoldHistory {n : ℕ} (x : (i : Finset.Iic (n + 1)) → Hold J)
    (z : Hold J) :
    shiftHoldHistory (n + 1) (extendHoldHistory x z) = extendHoldHistory (shiftHoldHistory n x) z := by
  funext i
  have hi : i.1 ≤ n + 1 := Finset.mem_Iic.1 i.2
  simp only [shiftHoldHistory, extendHoldHistory]
  by_cases h : i.1 ≤ n
  · rw [dif_pos (by omega), dif_pos h]
  · rw [dif_neg (by omega), dif_neg h]

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem frestrictLe_shiftHold (n : ℕ) (ω : ℕ → Hold J) :
    Preorder.frestrictLe (π := fun _ : ℕ => Hold J) n (shiftHold ω)
      = shiftHoldHistory n (Preorder.frestrictLe (π := fun _ : ℕ => Hold J) (n + 1) ω) := rfl

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem shiftHoldHistory_zero_comp (y : (i : Finset.Iic 0) → Hold J) :
    (shiftHoldHistory (J := J) 0) ∘ (extendHoldHistory y) = holdHistoryZero := by
  funext z i
  simp only [Function.comp_apply, shiftHoldHistory, extendHoldHistory, holdHistoryZero]
  rw [dif_neg (by omega)]

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- The state the first jump of a history reaches. -/
theorem stateAfterJumps_one (s : S) {n : ℕ} (h : (i : Finset.Iic n) → Hold J) :
    stateAfterJumps next s (jumpExtend fun i => (h i).1) 1
      = next s (h ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩).1 := by
  rw [stateAfterJumps_succ, stateAfterJumps_zero, jumpExtend_apply _ (Nat.zero_le n)]

omit [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- Replaying a shifted history from the state the first step reaches is replaying the whole
history one step further. -/
theorem stateAfterJumps_shiftHoldHistory (s : S) {n : ℕ}
    (x : (i : Finset.Iic (n + 1)) → Hold J) {k : ℕ} (hk : k ≤ n + 1) :
    stateAfterJumps next (stateAfterJumps next s (jumpExtend fun i => (x i).1) 1)
        (jumpExtend fun i => ((shiftHoldHistory n x) i).1) k
      = stateAfterJumps next s (jumpExtend fun i => (x i).1) (1 + k) := by
  rw [stateAfterJumps_add]
  refine stateAfterJumps_congr next _ k fun i hi => ?_
  have hin : i ≤ n := by omega
  rw [jumpExtend_apply _ hin, jumpExtend_apply _ (show 1 + i ≤ n + 1 by omega)]
  rfl

omit [DiscreteMeasurableSpace J] [Countable J] [DecidableEq J] in
theorem IicProdIoc_prodMk_piSingleton_hold {n : ℕ} (x : (i : Finset.Iic n) → Hold J) :
    (IicProdIoc (X := fun _ : ℕ => Hold J) n (n + 1)) ∘ (Prod.mk x) ∘
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Hold J) n)
      = extendHoldHistory x := by
  funext z i
  simp only [Function.comp_apply, IicProdIoc, extendHoldHistory]
  by_cases h : i.1 ≤ n
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    simp only [MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      eqRec_eq_cast, cast_eq]

omit [DecidableEq J] in
/-- One step of the kernel keeps the history it started from and appends a step drawn from the
law at the state the history reaches. -/
theorem drivenPartialTraj_succ_apply (s : S) (n : ℕ) (x : (i : Finset.Iic n) → Hold J) :
    Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) n (n + 1) x
      = (L (stateAfterJumps next s (jumpExtend fun i => (x i).1) (n + 1))).map
          (extendHoldHistory x) := by
  have hpi : Measurable (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Hold J) n) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Hold J) n).measurable
  have hIic : Measurable (IicProdIoc (X := fun _ : ℕ => Hold J) n (n + 1)) :=
    measurable_IicProdIoc
  have hmk : Measurable (Prod.mk (β := (i : Finset.Ioc n (n + 1)) → Hold J) x) :=
    measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hIic, Kernel.prod_apply,
    Kernel.id_apply, Kernel.map_apply _ hpi, drivenKernel_apply, Measure.dirac_prod,
    Measure.map_map hmk hpi, Measure.map_map hIic (hmk.comp hpi),
    IicProdIoc_prodMk_piSingleton_hold]

omit [DecidableEq J] in
/-- **The restart at the first jump, on histories.**  From a fixed first step, the history of
the steps that follow is the history of the chain started at the state that step reaches. -/
theorem map_drivenPartialTraj_shiftHoldHistory (s : S) (n : ℕ)
    (y : (i : Finset.Iic 0) → Hold J) :
    (Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0 (n + 1) y).map
        (shiftHoldHistory n)
      = jumpHoldHistory
          (drivenKernel next L (stateAfterJumps next s (jumpExtend fun i => (y i).1) 1))
          (L (stateAfterJumps next s (jumpExtend fun i => (y i).1) 1)) n := by
  induction n with
  | zero =>
      rw [drivenPartialTraj_succ_apply, Measure.map_map (measurable_shiftHoldHistory 0)
        (measurable_extendHoldHistory y), shiftHoldHistory_zero_comp]
      unfold jumpHoldHistory
      rw [Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
      set v := stateAfterJumps next s (jumpExtend fun i => (y i).1) 1 with hv
      have hone : ∀ x : (i : Finset.Iic (n + 1)) → Hold J,
          stateAfterJumps next s (jumpExtend fun i => (x i).1) 1
            = next s (x ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩).1 :=
        fun x => stateAfterJumps_one next s x
      have hae : ∀ᵐ x ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J)
          (drivenKernel next L s) 0 (n + 1) y),
          stateAfterJumps next s (jumpExtend fun i => (x i).1) 1 = v := by
        have hmeas : Measurable fun x : (i : Finset.Iic (n + 1)) → Hold J =>
            stateAfterJumps next s (jumpExtend fun i => (x i).1) 1 :=
          measurable_stateAfterJumpsHistory next s (n + 1) 1
        have hmeas0 : Measurable fun x : (i : Finset.Iic 0) → Hold J =>
            stateAfterJumps next s (jumpExtend fun i => (x i).1) 1 :=
          measurable_stateAfterJumpsHistory next s 0 1
        have hcomp : (fun x : (i : Finset.Iic (n + 1)) → Hold J =>
              stateAfterJumps next s (jumpExtend fun i => (x i).1) 1)
            = (fun h : (i : Finset.Iic 0) → Hold J =>
                stateAfterJumps next s (jumpExtend fun i => (h i).1) 1) ∘
              (Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.zero_le (n + 1))) := by
          funext x
          show stateAfterJumps next s (jumpExtend fun i => (x i).1) 1
            = stateAfterJumps next s (jumpExtend fun i =>
                ((Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J)
                  (Nat.zero_le (n + 1)) x) i).1) 1
          rw [stateAfterJumps_one next s x, stateAfterJumps_one next s
            (Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) (Nat.zero_le (n + 1)) x)]
          rfl
        have hmap : (Kernel.partialTraj (X := fun _ : ℕ => Hold J)
              (drivenKernel next L s) 0 (n + 1) y).map
            (fun x : (i : Finset.Iic (n + 1)) → Hold J =>
              stateAfterJumps next s (jumpExtend fun i => (x i).1) 1) = Measure.dirac v := by
          rw [hcomp, ← Measure.map_map hmeas0
              (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Hold J) (Nat.zero_le (n + 1))),
            Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Hold J) y
              (Nat.zero_le (n + 1)), Kernel.partialTraj_self, Kernel.id_apply,
            Measure.map_dirac' hmeas0 y]
        rw [Filter.eventually_iff, mem_ae_iff]
        have hset : {x : (i : Finset.Iic (n + 1)) → Hold J |
              stateAfterJumps next s (jumpExtend fun i => (x i).1) 1 = v}ᶜ
            = (fun x : (i : Finset.Iic (n + 1)) → Hold J =>
                stateAfterJumps next s (jumpExtend fun i => (x i).1) 1) ⁻¹' {v}ᶜ := rfl
        rw [hset, ← Measure.map_apply hmeas MeasurableSet.of_discrete, hmap,
          Measure.dirac_apply' _ MeasurableSet.of_discrete]
        simp
      ext T hT
      have hpt : ∀ x : (i : Finset.Iic (n + 1)) → Hold J,
          stateAfterJumps next s (jumpExtend fun i => (x i).1) 1 = v →
          Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L s)
              (n + 1) (n + 2) x (shiftHoldHistory (n + 1) ⁻¹' T)
            = Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L v) n (n + 1)
                (shiftHoldHistory n x) T := by
        intro x hx
        rw [drivenPartialTraj_succ_apply, drivenPartialTraj_succ_apply,
          Measure.map_apply (measurable_extendHoldHistory x)
            ((measurable_shiftHoldHistory (n + 1)) hT),
          Measure.map_apply (measurable_extendHoldHistory (shiftHoldHistory n x)) hT]
        have hpre : extendHoldHistory x ⁻¹' (shiftHoldHistory (n + 1) ⁻¹' T)
            = extendHoldHistory (shiftHoldHistory n x) ⁻¹' T := by
          rw [← Set.preimage_comp]
          exact congrArg (fun f => f ⁻¹' T)
            (funext fun z => shiftHoldHistory_extendHoldHistory x z)
        have hstate : stateAfterJumps next v
              (jumpExtend fun i => ((shiftHoldHistory n x) i).1) (n + 1)
            = stateAfterJumps next s (jumpExtend fun i => (x i).1) (n + 1 + 1) := by
          rw [← hx, stateAfterJumps_shiftHoldHistory next s x (le_refl (n + 1)),
            show 1 + (n + 1) = n + 1 + 1 from by omega]
        rw [hpre, hstate]
      have hstep : jumpHoldHistory (drivenKernel next L v) (L v) (n + 1) T
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L v)
              n (n + 1) h T ∂(jumpHoldHistory (drivenKernel next L v) (L v) n) := by
        unfold jumpHoldHistory
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply hT (Kernel.aemeasurable _)]
      rw [Measure.map_apply (measurable_shiftHoldHistory (n + 1)) hT,
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le (n + 1)),
        Kernel.comp_apply' _ _ _ ((measurable_shiftHoldHistory (n + 1)) hT), hstep]
      calc ∫⁻ x, Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L s)
              (n + 1) (n + 1 + 1) x (shiftHoldHistory (n + 1) ⁻¹' T)
            ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0 (n + 1) y)
          = ∫⁻ x, Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L v)
                n (n + 1) (shiftHoldHistory n x) T
              ∂(Kernel.partialTraj (X := fun _ : ℕ => Hold J)
                (drivenKernel next L s) 0 (n + 1) y) :=
            lintegral_congr_ae (hae.mono fun x hx => hpt x hx)
        _ = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L v)
                n (n + 1) h T
              ∂((Kernel.partialTraj (X := fun _ : ℕ => Hold J)
                (drivenKernel next L s) 0 (n + 1) y).map (shiftHoldHistory n)) :=
            (lintegral_map (Kernel.measurable_coe _ hT) (measurable_shiftHoldHistory n)).symm
        _ = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Hold J) (drivenKernel next L v)
                n (n + 1) h T ∂(jumpHoldHistory (drivenKernel next L v) (L v) n) := by rw [ih]

omit [DecidableEq J] in
/-- **The restart at the first jump, on realisations.**  From a fixed first step, the rest of
the realisation is a realisation of the chain started at the state that step reaches. -/
theorem map_drivenTraj_shiftHold (s : S) (y : (i : Finset.Iic 0) → Hold J) :
    (Kernel.traj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0 y).map shiftHold
      = drivenMeasure next L (stateAfterJumps next s (jumpExtend fun i => (y i).1) 1) := by
  have hprob : IsProbabilityMeasure
      ((Kernel.traj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0 y).map shiftHold) :=
    Measure.isProbabilityMeasure_map measurable_shiftHold.aemeasurable
  refine MeasureTheory.ext_of_generate_finite
    {a : Set (ℕ → Hold J) | ∃ (b : ℕ) (T : Set ((i : Finset.Iic b) → Hold J)),
      MeasurableSet T ∧ a = Preorder.frestrictLe (π := fun _ : ℕ => Hold J) b ⁻¹' T}
    ?_ ?_ ?_ ?_
  · refine le_antisymm (iSup_le fun i => ?_) (MeasurableSpace.generateFrom_le ?_)
    · rintro a ⟨T, hT, rfl⟩
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨i, (fun h : (j : Finset.Iic i) → Hold J => h ⟨i, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' T,
          (measurable_pi_apply _) hT, rfl⟩
    · rintro a ⟨b, T, hT, rfl⟩
      exact Preorder.measurable_frestrictLe b hT
  · rintro a ⟨b, T, hT, rfl⟩ c ⟨b', T', hT', rfl⟩ -
    rcases le_total b b' with hbb | hbb
    · exact ⟨b', (Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) hbb ⁻¹' T) ∩ T',
        ((Preorder.measurable_frestrictLe₂ hbb) hT).inter hT',
        by rw [Set.preimage_inter, ← Set.preimage_comp]; rfl⟩
    · exact ⟨b, T ∩ (Preorder.frestrictLe₂ (π := fun _ : ℕ => Hold J) hbb ⁻¹' T'),
        hT.inter ((Preorder.measurable_frestrictLe₂ hbb) hT'),
        by rw [Set.preimage_inter, ← Set.preimage_comp]; rfl⟩
  · rintro a ⟨b, T, hT, rfl⟩
    have hpre : shiftHold ⁻¹' (Preorder.frestrictLe (π := fun _ : ℕ => Hold J) b ⁻¹' T)
        = Preorder.frestrictLe (π := fun _ : ℕ => Hold J) (b + 1) ⁻¹'
          (shiftHoldHistory b ⁻¹' T) := rfl
    rw [Measure.map_apply measurable_shiftHold (Preorder.measurable_frestrictLe b hT),
      hpre, ← Measure.map_apply (Preorder.measurable_frestrictLe (b + 1))
        ((measurable_shiftHoldHistory b) hT),
      Kernel.traj_map_frestrictLe_apply, ← Measure.map_apply (measurable_shiftHoldHistory b) hT,
      map_drivenPartialTraj_shiftHoldHistory,
      ← Measure.map_apply (Preorder.measurable_frestrictLe b) hT]
    rw [drivenMeasure, jumpHoldMeasure_map_frestrictLe]
  · rw [measure_univ, measure_univ]

omit [DecidableEq J] in
/-- **The restart at the first jump.**  The first step is drawn from the law at the starting
state, and given it the rest of the realisation is a realisation of the chain started at the
state it reaches. -/
theorem drivenMeasure_restart (s : S) {B : Set (Hold J)} (hB : MeasurableSet B)
    {E : Set (ℕ → Hold J)} (hE : MeasurableSet E) :
    drivenMeasure next L s ({ω | ω 0 ∈ B} ∩ shiftHold ⁻¹' E)
      = ∫⁻ z in B, drivenMeasure next L (next s z.1) E ∂(L s) := by
  have hS : MeasurableSet ({ω : ℕ → Hold J | ω 0 ∈ B} ∩ shiftHold ⁻¹' E) :=
    ((measurable_pi_apply 0) hB).inter (measurable_shiftHold hE)
  have hzero : ∀ z : Hold J,
      Kernel.traj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0 (holdHistoryZero z)
          ({ω : ℕ → Hold J | ω 0 ∈ B} ∩ shiftHold ⁻¹' E)
        = Set.indicator B (fun w : Hold J => drivenMeasure next L (next s w.1) E) z := by
    intro z
    have hmeasc : MeasurableSet ({h : (i : Finset.Iic 0) → Hold J |
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = z}ᶜ) := by
      have hset : {h : (i : Finset.Iic 0) → Hold J | h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = z}ᶜ
          = (fun h : (i : Finset.Iic 0) → Hold J => h ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' {z}ᶜ :=
        rfl
      rw [hset]
      exact (measurable_pi_apply _) (measurableSet_singleton z).compl
    have hcoord : Kernel.traj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0
        (holdHistoryZero z) ({ω : ℕ → Hold J | ω 0 = z}ᶜ) = 0 := by
      have h1 : ({ω : ℕ → Hold J | ω 0 = z}ᶜ)
          = Preorder.frestrictLe (π := fun _ : ℕ => Hold J) 0 ⁻¹'
            ({h : (i : Finset.Iic 0) → Hold J | h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = z}ᶜ) := rfl
      rw [h1, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hmeasc,
        Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply,
        Measure.dirac_apply' _ hmeasc,
        Set.indicator_of_notMem (by simp [holdHistoryZero])]
    have hshift : Kernel.traj (X := fun _ : ℕ => Hold J) (drivenKernel next L s) 0
        (holdHistoryZero z) (shiftHold ⁻¹' E)
        = drivenMeasure next L (next s z.1) E := by
      rw [← Measure.map_apply measurable_shiftHold hE, map_drivenTraj_shiftHold,
        stateAfterJumps_one]
      rfl
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB, ← hshift]
      refine le_antisymm (measure_mono Set.inter_subset_right) ?_
      refine le_measure_of_inter hcoord (le_refl _) ?_
      rintro ω ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show ω 0 ∈ B
      rw [show ω 0 = z from h1]
      exact hzB
    · rw [Set.indicator_of_notMem hzB]
      refine le_antisymm ?_ (by simp)
      rw [← hcoord]
      refine measure_mono ?_
      rintro ω ⟨h1, -⟩ hcon
      apply hzB
      rw [← show ω 0 = z from hcon]
      exact h1
  rw [drivenMeasure, jumpHoldMeasure, Measure.bind_apply hS (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hS) measurable_holdHistoryZero,
    lintegral_congr hzero, lintegral_indicator hB]

/-- The chain started at the state one step reaches, as a kernel in that step. -/
noncomputable def restartKernel (s : S) : Kernel (Hold J) (ℕ → Hold J) where
  toFun z := drivenMeasure next L (next s z.1)
  measurable' :=
    (Measurable.of_discrete (f := fun a : J => drivenMeasure next L (next s a))).comp
      measurable_fst

omit [DecidableEq J] in
theorem restartKernel_apply (s : S) (z : Hold J) :
    restartKernel next L s z = drivenMeasure next L (next s z.1) := rfl

instance isMarkovKernel_restartKernel (s : S) : IsMarkovKernel (restartKernel next L s) :=
  ⟨fun z => by rw [restartKernel_apply]; infer_instance⟩

omit [DecidableEq J] in
/-- **The joint law of the first step and the rest.**  The first step follows the law at the
starting state, and given it the rest is a realisation from the state it reaches. -/
theorem map_drivenMeasure_firstRest (s : S) :
    (drivenMeasure next L s).map (fun ω => (ω 0, shiftHold ω))
      = (L s) ⊗ₘ (restartKernel next L s) := by
  have hmeas : Measurable fun ω : ℕ → Hold J => (ω 0, shiftHold ω) :=
    (measurable_pi_apply 0).prodMk measurable_shiftHold
  have hprob : IsProbabilityMeasure
      ((drivenMeasure next L s).map (fun ω => (ω 0, shiftHold ω))) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine MeasureTheory.ext_of_generate_finite
    {a : Set (Hold J × (ℕ → Hold J)) | ∃ (B : Set (Hold J)) (E : Set (ℕ → Hold J)),
      MeasurableSet B ∧ MeasurableSet E ∧ a = B ×ˢ E} ?_ ?_ ?_ ?_
  · rw [← generateFrom_prod]
    congr 1
    ext a
    constructor
    · rintro ⟨B, E, hB, hE, rfl⟩
      exact ⟨B, hB, E, hE, rfl⟩
    · rintro ⟨B, hB, E, hE, rfl⟩
      exact ⟨B, E, hB, hE, rfl⟩
  · rintro a ⟨B, E, hB, hE, rfl⟩ c ⟨B', E', hB', hE', rfl⟩ -
    exact ⟨B ∩ B', E ∩ E', hB.inter hB', hE.inter hE', Set.prod_inter_prod⟩
  · rintro a ⟨B, E, hB, hE, rfl⟩
    rw [Measure.map_apply hmeas (hB.prod hE), Measure.compProd_apply_prod hB hE]
    have hpre : (fun ω : ℕ → Hold J => (ω 0, shiftHold ω)) ⁻¹' (B ×ˢ E)
        = {ω | ω 0 ∈ B} ∩ shiftHold ⁻¹' E := rfl
    rw [hpre, drivenMeasure_restart next L s hB hE]
    rfl
  · rw [measure_univ, measure_univ]

omit [DecidableEq J] in
/-- The disintegration at the first step, as an integral. -/
theorem lintegral_drivenMeasure_restart (s : S) {f : Hold J → (ℕ → Hold J) → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ ω, f (ω 0) (shiftHold ω) ∂(drivenMeasure next L s)
      = ∫⁻ z, (∫⁻ ω', f z ω' ∂(drivenMeasure next L (next s z.1))) ∂(L s) := by
  have hmeas : Measurable fun ω : ℕ → Hold J => (ω 0, shiftHold ω) :=
    (measurable_pi_apply 0).prodMk measurable_shiftHold
  calc ∫⁻ ω, f (ω 0) (shiftHold ω) ∂(drivenMeasure next L s)
      = ∫⁻ y, Function.uncurry f y
          ∂((drivenMeasure next L s).map (fun ω => (ω 0, shiftHold ω))) :=
        (lintegral_map hf hmeas).symm
    _ = ∫⁻ y, Function.uncurry f y ∂((L s) ⊗ₘ (restartKernel next L s)) := by
        rw [map_drivenMeasure_firstRest]
    _ = ∫⁻ z, (∫⁻ ω', f z ω' ∂(drivenMeasure next L (next s z.1))) ∂(L s) :=
        Measure.lintegral_compProd hf

omit [DecidableEq J] in
/-- The first step follows the law at the starting state. -/
theorem map_drivenMeasure_first (s : S) :
    (drivenMeasure next L s).map (fun ω => ω 0) = L s := by
  have hmeas : Measurable fun ω : ℕ → Hold J => (ω 0, shiftHold ω) :=
    (measurable_pi_apply 0).prodMk measurable_shiftHold
  have h : (drivenMeasure next L s).map (fun ω => ω 0)
      = ((drivenMeasure next L s).map (fun ω => (ω 0, shiftHold ω))).map Prod.fst := by
    rw [Measure.map_map measurable_fst hmeas]
    rfl
  rw [h, map_drivenMeasure_firstRest]
  exact Measure.fst_compProd _ _

omit [DecidableEq J] in
/-- If every step law puts no mass on negative holding times, neither does the chain. -/
theorem drivenMeasure_holdTime_nonneg (hL : ∀ t : S, L t {z : Hold J | z.2 < 0} = 0) (s : S)
    (n : ℕ) : drivenMeasure next L s {ω | (ω n).2 < 0} = 0 := by
  induction n generalizing s with
  | zero =>
      have hmeas : MeasurableSet {z : Hold J | z.2 < 0} :=
        measurableSet_lt measurable_snd measurable_const
      have hpre : {ω : ℕ → Hold J | (ω 0).2 < 0}
          = (fun ω : ℕ → Hold J => ω 0) ⁻¹' {z : Hold J | z.2 < 0} := rfl
      rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) hmeas,
        map_drivenMeasure_first, hL s]
  | succ n ih =>
      have hmeasE : MeasurableSet {ω : ℕ → Hold J | (ω n).2 < 0} :=
        measurableSet_lt (measurable_snd.comp (measurable_pi_apply n)) measurable_const
      have hset : {ω : ℕ → Hold J | (ω (n + 1)).2 < 0}
          = {ω : ℕ → Hold J | ω 0 ∈ Set.univ} ∩ shiftHold ⁻¹' {ω' | (ω' n).2 < 0} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_inter_iff,
          Set.mem_preimage]
        show (ω (n + 1)).2 < 0 ↔ (ω (1 + n)).2 < 0
        rw [Nat.add_comm]
      rw [hset, drivenMeasure_restart next L s MeasurableSet.univ hmeasE,
        Measure.restrict_univ]
      have hz : ∀ z : Hold J,
          drivenMeasure next L (next s z.1) {ω : ℕ → Hold J | (ω n).2 < 0} = 0 :=
        fun z => ih (next s z.1)
      simp only [hz]
      exact lintegral_zero

end Restart

end SocialNetwork
