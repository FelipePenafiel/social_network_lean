/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedConcentration
import SocialNetwork.BiasedExistence
import SocialNetwork.BiasedMetastability
import SocialNetwork.ExitTime

/-!
# The mean exit time from a biased consensus set is finite

The biased twin of `SocialNetwork.ExitTime`: Theorem 31 and the biased Proposition 12 divide
by `E (R^{α,β,u} (C_α^{-o}))`, and this file proves that mean finite, from every state of `S^α`,
for `0 < γ < 1/(M-1)` and every `β ≥ 0`.

**No counterpart in the paper.**  The argument is that of `SocialNetwork.ExitTime`, transposed
to the memory profiles: the biased Doeblin minorisation
(`SocialNetwork.Bias.minorisation_iterateKernel`) gives the geometric tail of the time the
biased skeleton spends away from the staircase profile `l_α^{o'}`, the expressed pairs of the
biased process are distributed as the biased skeleton
(`SocialNetwork.Bias.map_biasedCtsPathMeasure_jumps`), and each holding time has mean at most
`∑_k e^{-k}` because the rate is at least `M` on `S^α`
(`SocialNetwork.Bias.IsBiasedState.le_biasedTotalRate`).  The lemmas of
`SocialNetwork.ExitTime` that know nothing about either model — the geometric tail of
`SocialNetwork.kacAvoid`, the uniqueness of a measure on sequences from its initial segments,
the counting bound on a holding time — are used as they stand.

The biased process is built by `Kernel.traj` like the unbiased one, but the files that use it
read it through its first step rather than through its finite histories, so the history
measures and the one-step formulas are set up here first.

## Main results

* `SocialNetwork.Bias.map_biasedCtsPathMeasure_jumps` — the expressed pairs of the biased
  process are distributed as the biased skeleton.
* `SocialNetwork.Bias.biasedExpHittingTimeCts_lt_top` — the mean hitting time of any set
  containing a staircase profile is finite.
* `SocialNetwork.Bias.biasedExpHittingTimeCts_consensusSetOther_lt_top` — the mean exit time
  from a biased consensus set is finite.
* `SocialNetwork.Bias.biasedExpHittingTimeCts_consensusSetOther_pos` — and positive.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### Finite histories of the biased process -/

section History

variable [NeZero N] [NeZero M]

/-- The law of the first `n + 1` steps of the biased process. -/
noncomputable def biasedCtsHistoryMeasure (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    Measure ((i : Finset.Iic n) → Step N M) :=
  Kernel.partialTraj (X := fun _ : ℕ => Step N M) (biasedCtsDrivingKernel γ β u) 0 n ∘ₘ
    ((biasedStepLaw γ β u).map toStepHistoryZero)

theorem biasedCtsPathMeasure_map_frestrictLe (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    (biasedCtsPathMeasure γ β u).map (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n)
      = biasedCtsHistoryMeasure γ β u n := by
  unfold biasedCtsHistoryMeasure biasedCtsPathMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe n), Kernel.traj_map_frestrictLe]

/-- The first marginal of one biased step is the Gibbs law of equation (7). -/
theorem biasedStepLaw_preimage_fst (γ β : ℝ) (P : Profile N M) (B : Set (Jump N M)) :
    biasedStepLaw γ β P ((fun z : Step N M => z.1) ⁻¹' B) = (biasedJumpPMF γ β P).toMeasure B := by
  have hp : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β P)) :=
    isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β P)
  have hset : (fun z : Step N M => z.1) ⁻¹' B = B ×ˢ (Set.univ : Set ℝ) := by
    ext z; simp
  rw [biasedStepLaw, hset, Measure.prod_prod, measure_univ, mul_one]

/-- The second marginal of one biased step is the exponential holding law. -/
theorem biasedStepLaw_preimage_snd (γ β : ℝ) (P : Profile N M) (A : Set ℝ) :
    biasedStepLaw γ β P ((fun z : Step N M => z.2) ⁻¹' A)
      = expMeasure (biasedTotalRate γ β P) A := by
  have hp : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β P)) :=
    isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β P)
  have hset : (fun z : Step N M => z.2) ⁻¹' A = (Set.univ : Set (Jump N M)) ×ˢ A := by
    ext z; simp
  rw [biasedStepLaw, hset, Measure.prod_prod, measure_univ, one_mul]

/-- One step of the biased kernel keeps the history it started from and appends a step drawn
from the law at the profile the history reaches.  The twin of
`SocialNetwork.ctsPartialTraj_succ_apply`. -/
theorem biasedCtsPartialTraj_succ_apply (γ β : ℝ) (u : Profile N M) (n : ℕ)
    (x : (i : Finset.Iic n) → Step N M) :
    Kernel.partialTraj (X := fun _ : ℕ => Step N M) (biasedCtsDrivingKernel γ β u) n (n + 1) x
      = (biasedStepLaw γ β (stateAfterStepHistory u x (n + 1))).map (extendStepHistory x) := by
  have hpi : Measurable (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Step N M) n) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Step N M) n).measurable
  have hIic : Measurable (IicProdIoc (X := fun _ : ℕ => Step N M) n (n + 1)) :=
    measurable_IicProdIoc
  have hmk : Measurable (Prod.mk (β := (i : Finset.Ioc n (n + 1)) → Step N M) x) :=
    measurable_prodMk_left
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hIic, Kernel.prod_apply,
    Kernel.id_apply, Kernel.map_apply _ hpi, biasedCtsDrivingKernel_apply, Measure.dirac_prod,
    Measure.map_map hmk hpi, Measure.map_map hIic (hmk.comp hpi),
    IicProdIoc_prodMk_piSingleton]

/-- Under one step of the biased kernel, the past is almost surely the history it started
from. -/
theorem biasedCtsPartialTraj_frestrictLe₂_apply (γ β : ℝ) (u : Profile N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Step N M) {T : Set ((i : Finset.Iic n) → Step N M)}
    (hT : MeasurableSet T) :
    Kernel.partialTraj (X := fun _ : ℕ => Step N M) (biasedCtsDrivingKernel γ β u) n (n + 1) h
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n) ⁻¹' T)
      = Measure.dirac h T := by
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe₂
      (X := fun _ : ℕ => Step N M) (Nat.le_succ n)) hT,
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Step N M) h (Nat.le_succ n),
    Kernel.partialTraj_self, Kernel.id_apply]

/-- Under one step of the biased kernel, the new coordinate follows the law of one step at the
profile the history reaches. -/
theorem biasedCtsPartialTraj_last_apply (γ β : ℝ) (u : Profile N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Step N M) {B : Set (Step N M)} (hB : MeasurableSet B) :
    Kernel.partialTraj (X := fun _ : ℕ => Step N M) (biasedCtsDrivingKernel γ β u) n (n + 1) h
        ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
          x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' B)
      = biasedStepLaw γ β (stateAfterStepHistory u h (n + 1)) B := by
  have hmeas : Measurable fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := measurable_pi_apply _
  rw [← Measure.map_apply hmeas hB, ← Kernel.map_apply _ hmeas,
    Kernel.map_partialTraj_succ_self, biasedCtsDrivingKernel_apply]

/-- One more step of the biased history measure: the law of the first `n + 2` steps against a
measurable set is the history measure of the first `n + 1` integrated against one step of the
kernel. -/
theorem biasedCtsHistoryMeasure_succ_apply (γ β : ℝ) (u : Profile N M) (n : ℕ)
    {S : Set ((i : Finset.Iic (n + 1)) → Step N M)} (hS : MeasurableSet S) :
    biasedCtsHistoryMeasure γ β u (n + 1) S
      = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
          (biasedCtsDrivingKernel γ β u) n (n + 1) h S ∂(biasedCtsHistoryMeasure γ β u n) := by
  unfold biasedCtsHistoryMeasure
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
    Measure.bind_apply hS (Kernel.aemeasurable _)]

end History

/-! ### The expressed pairs of the biased process are the biased skeleton -/

section Bridge

variable [NeZero N] [NeZero M]

/-- **The law of the expressed pairs of a finite history of the biased process**: the product
of the one-step probabilities along it, as for the biased skeleton
(`SocialNetwork.Bias.historyMeasure_singleton`). -/
theorem biasedCtsHistoryMeasure_jumps_singleton (γ β : ℝ) (u : Profile N M) (n : ℕ)
    (x : (i : Finset.Iic n) → Jump N M) :
    biasedCtsHistoryMeasure γ β u n
        ((fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1) ⁻¹' {x})
      = ∏ m ∈ Finset.range (n + 1),
          biasedJumpPMF γ β (stateAfterHistory u x m) (ofHistoryPath x m) := by
  induction n with
  | zero =>
      have h0 : biasedCtsHistoryMeasure γ β u 0 = (biasedStepLaw γ β u).map toStepHistoryZero := by
        unfold biasedCtsHistoryMeasure
        rw [Kernel.partialTraj_self, Measure.id_comp]
      have hpre : toStepHistoryZero ⁻¹'
            ((fun h : (i : Finset.Iic 0) → Step N M => fun i => (h i).1) ⁻¹' {x})
          = (fun z : Step N M => z.1) ⁻¹' {ofHistoryPath x 0} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hz
          have := congrFun hz ⟨0, Finset.mem_Iic.2 le_rfl⟩
          simpa [ofHistoryPath, toStepHistoryZero] using this
        · intro hz
          funext i
          have hi : i = (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0) :=
            Subtype.ext (Nat.le_zero.1 (Finset.mem_Iic.1 i.2))
          rw [hi]
          simpa [ofHistoryPath, toStepHistoryZero] using hz
      rw [h0, Measure.map_apply measurable_toStepHistoryZero
          ((measurable_stepHistoryJumps 0) (measurableSet_singleton x)), hpre,
        biasedStepLaw_preimage_fst, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        Finset.prod_range_one]
      rfl
  | succ n ih =>
      have hmeasS : MeasurableSet
          ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x}) :=
        (measurable_stepHistoryJumps (n + 1)) (measurableSet_singleton x)
      set h₀ := Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x with hh₀
      have hind : (fun h : (i : Finset.Iic n) → Step N M =>
            Kernel.partialTraj (X := fun _ : ℕ => Step N M) (biasedCtsDrivingKernel γ β u) n
              (n + 1) h
              ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x}))
          = Set.indicator
              ((fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1) ⁻¹' {h₀})
              (fun _ => biasedJumpPMF γ β (stateAfterHistory u h₀ (n + 1))
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)) := by
        funext h
        rw [biasedCtsPartialTraj_succ_apply,
          Measure.map_apply (measurable_extendStepHistory h) hmeasS]
        by_cases hc : (fun i => (h i).1) = h₀
        · rw [Set.indicator_of_mem (by simpa using hc)]
          have hpre : extendStepHistory h ⁻¹'
                ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
              = (fun z : Step N M => z.1) ⁻¹' {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩} := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            rw [extendStepHistory_jumps_eq_iff]
            exact ⟨fun hz => hz.2, fun hz => ⟨hc, hz⟩⟩
          have hst : stateAfterStepHistory u h (n + 1) = stateAfterHistory u h₀ (n + 1) := by
            rw [← hc]
            rfl
          rw [hpre, biasedStepLaw_preimage_fst,
            PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), hst]
        · rw [Set.indicator_of_notMem (by simpa using hc)]
          have hpre : extendStepHistory h ⁻¹'
                ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
              = ∅ := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
              iff_false]
            rw [extendStepHistory_jumps_eq_iff]
            exact fun hz => hc hz.1
          rw [hpre, measure_empty]
      have hlhs : biasedCtsHistoryMeasure γ β u (n + 1)
            ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
          = biasedJumpPMF γ β (stateAfterHistory u h₀ (n + 1))
              (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
            * ∏ m ∈ Finset.range (n + 1),
                biasedJumpPMF γ β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m) := by
        rw [biasedCtsHistoryMeasure_succ_apply γ β u n hmeasS, hind,
          lintegral_indicator ((measurable_stepHistoryJumps n) (measurableSet_singleton h₀)),
          setLIntegral_const, ih h₀]
      have hprod : ∀ m ∈ Finset.range (n + 1),
          biasedJumpPMF γ β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m)
            = biasedJumpPMF γ β (stateAfterHistory u x m) (ofHistoryPath x m) := by
        intro m hm
        have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        have h1 : stateAfterHistory u h₀ m = stateAfterHistory u x m :=
          (stateAfter_ofHistoryPath_eq (hx := hh₀.symm) u (k := m) (by omega)).symm
        have h2 : ofHistoryPath h₀ m = ofHistoryPath x m :=
          (ofHistoryPath_eq (hx := hh₀.symm) hmn).symm
        rw [h1, h2]
      have hlast : biasedJumpPMF γ β (stateAfterHistory u h₀ (n + 1))
          (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
          = biasedJumpPMF γ β (stateAfterHistory u x (n + 1)) (ofHistoryPath x (n + 1)) := by
        rw [ofHistoryPath_apply x (le_refl (n + 1)),
          show stateAfterHistory u h₀ (n + 1) = stateAfterHistory u x (n + 1) from
            (stateAfter_ofHistoryPath_eq (hx := hh₀.symm) u (k := n + 1) le_rfl).symm]
      rw [hlhs, Finset.prod_congr rfl hprod, hlast,
        Finset.prod_range_succ (f := fun m =>
          biasedJumpPMF γ β (stateAfterHistory u x m) (ofHistoryPath x m)) (n := n + 1)]
      ring

/-- The expressed pairs of a finite history of the biased process have the law of the same
history of the biased skeleton. -/
theorem biasedCtsHistoryMeasure_map_jumps (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    (biasedCtsHistoryMeasure γ β u n).map
        (fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1)
      = biasedHistoryMeasure γ β u n := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.map_apply (measurable_stepHistoryJumps n) (measurableSet_singleton x),
    biasedCtsHistoryMeasure_jumps_singleton, historyMeasure_singleton]

/-- **The expressed pairs of the biased process are distributed as the biased skeleton**, the
twin of `SocialNetwork.map_ctsPathMeasure_jumps`. -/
theorem map_biasedCtsPathMeasure_jumps (γ β : ℝ) (u : Profile N M) :
    (biasedCtsPathMeasure γ β u).map stepJumps = biasedPathMeasure γ β u := by
  refine eq_of_map_frestrictLe fun b => ?_
  rw [Measure.map_map (Preorder.measurable_frestrictLe b) measurable_stepJumps]
  have hcomp : Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ∘ stepJumps
      = (fun h : (i : Finset.Iic b) → Step N M => fun i => (h i).1)
        ∘ Preorder.frestrictLe (π := fun _ : ℕ => Step N M) b := rfl
  rw [hcomp, ← Measure.map_map (measurable_stepHistoryJumps b)
      (Preorder.measurable_frestrictLe b), biasedCtsPathMeasure_map_frestrictLe,
    biasedCtsHistoryMeasure_map_jumps]
  unfold biasedHistoryMeasure biasedPathMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe b), Kernel.traj_map_frestrictLe]

theorem biasedCtsPathMeasure_preimage_stepJumps (γ β : ℝ) (u : Profile N M)
    {E : Set (ℕ → Jump N M)} (hE : MeasurableSet E) :
    biasedCtsPathMeasure γ β u (stepJumps ⁻¹' E) = biasedPathMeasure γ β u E := by
  rw [← map_biasedCtsPathMeasure_jumps, Measure.map_apply measurable_stepJumps hE]

end Bridge

/-! ### The holding times -/

section Holding

variable [NeZero N] [NeZero M]

/-- The holding-time bound relative to the history, for the biased process: the twin of
`SocialNetwork.ctsPathMeasure_history_holdingTime_le_mul`. -/
theorem biasedCtsPathMeasure_history_holdingTime_le_mul (γ β : ℝ) (u : Profile N M) (n : ℕ)
    {G : Set ((i : Finset.Iic n) → Step N M)} (hmeasG : MeasurableSet G) {A : Set ℝ}
    (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hc : ∀ h ∈ G, expMeasure (biasedTotalRate γ β (stateAfterStepHistory u h (n + 1))) A ≤ c) :
    biasedCtsPathMeasure γ β u ((Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
        ∩ {ω | holdingTime (n + 1) ω ∈ A})
      ≤ c * biasedCtsPathMeasure γ β u
          (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G) := by
  set S : Set ((i : Finset.Iic (n + 1)) → Step N M) :=
    (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n) ⁻¹' G) ∩
      ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
        (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) with hS
  have hmeasLast : MeasurableSet ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) :=
    (measurable_snd.comp (measurable_pi_apply _)) hA
  have hmeasS : MeasurableSet S :=
    ((Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Step N M) (Nat.le_succ n)) hmeasG).inter
      hmeasLast
  have hsplit : (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
        ∩ {ω : ℕ → Step N M | holdingTime (n + 1) ω ∈ A}
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) (n + 1) ⁻¹' S := rfl
  have hG : biasedCtsPathMeasure γ β u
        (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
      = biasedCtsHistoryMeasure γ β u n G := by
    rw [← Measure.map_apply (Preorder.measurable_frestrictLe n) hmeasG,
      biasedCtsPathMeasure_map_frestrictLe]
  rw [hsplit, ← Measure.map_apply (Preorder.measurable_frestrictLe (n + 1)) hmeasS,
    biasedCtsPathMeasure_map_frestrictLe, hG, biasedCtsHistoryMeasure_succ_apply γ β u n hmeasS]
  calc ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
        (biasedCtsDrivingKernel γ β u) n (n + 1) h S ∂(biasedCtsHistoryMeasure γ β u n)
      ≤ ∫⁻ h, G.indicator (fun _ => c) h ∂(biasedCtsHistoryMeasure γ β u n) := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ G
        · rw [Set.indicator_of_mem hh]
          refine le_trans (measure_mono Set.inter_subset_right) ?_
          have hcomp : ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A)
              = (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                  x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
                ((fun z : Step N M => z.2) ⁻¹' A) := rfl
          rw [hcomp, biasedCtsPartialTraj_last_apply γ β u n h (measurable_snd hA),
            biasedStepLaw_preimage_snd]
          exact hc h hh
        · rw [Set.indicator_of_notMem hh]
          refine le_trans (measure_mono Set.inter_subset_left) (le_of_eq ?_)
          rw [biasedCtsPartialTraj_frestrictLe₂_apply γ β u n h hmeasG,
            Measure.dirac_apply' _ hmeasG, Set.indicator_of_notMem hh]
    _ = c * biasedCtsHistoryMeasure γ β u n G := lintegral_indicator_const hmeasG c

/-- On `S^α`, a biased holding time exceeds `k` with probability at most `e^{-k}`. -/
theorem expMeasure_biasedTotalRate_Ioi_le (hM : 2 ≤ M) (γ β : ℝ) {P : Profile N M}
    (hP : IsBiasedState P) (k : ℕ) :
    expMeasure (biasedTotalRate γ β P) (Set.Ioi (k : ℝ))
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [expMeasure_Ioi_of_nonneg (biasedTotalRate_pos γ β P) (Nat.cast_nonneg k)]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hq : (1 : ℝ) ≤ biasedTotalRate γ β P :=
    le_trans (by exact_mod_cast (by omega : 1 ≤ M)) (hP.le_biasedTotalRate γ β)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

end Holding

/-! ### The mean exit time -/

section ExitTime

variable [NeZero N] [NeZero M]

/-- The realisations whose first `n + 1` profiles all differ from `l`. -/
def biasedAvoidUpTo (u l : Profile N M) (n : ℕ) : Set (ℕ → Step N M) :=
  {ω | ∀ k ≤ n, stateAfter u (stepJumps ω) k ≠ l}

omit [NeZero N] [NeZero M] in
theorem biasedAvoidUpTo_eq_preimage (u l : Profile N M) (n : ℕ) :
    biasedAvoidUpTo u l n = stepJumps ⁻¹' biasedAvoidSet u l (n + 1) := by
  ext ω
  simp only [biasedAvoidUpTo, biasedAvoidSet, Set.mem_preimage, Set.mem_ofPred_eq]
  exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩

omit [NeZero N] [NeZero M] in
theorem measurableSet_biasedAvoidUpTo (u l : Profile N M) (n : ℕ) :
    MeasurableSet (biasedAvoidUpTo u l n) := by
  rw [biasedAvoidUpTo_eq_preimage]
  exact measurable_stepJumps (measurableSet_biasedAvoidSet u l (n + 1))

omit [NeZero N] [NeZero M] in
theorem biasedAvoidUpTo_succ_eq_preimage (u l : Profile N M) (m : ℕ) :
    biasedAvoidUpTo u l (m + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) m ⁻¹'
        {h | ∀ k ≤ m + 1, stateAfterStepHistory u h k ≠ l} := by
  ext ω
  simp only [biasedAvoidUpTo, Set.mem_preimage, Set.mem_ofPred_eq]
  have hst : ∀ k ≤ m + 1, stateAfterStepHistory u
        (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) m ω) k
      = stateAfter u (stepJumps ω) k :=
    fun k hk => stateAfter_ofHistoryPath_frestrictLe u (stepJumps ω) hk
  exact ⟨fun h k hk => by rw [hst k hk]; exact h k hk,
    fun h k hk => by rw [← hst k hk]; exact h k hk⟩

omit [NeZero N] [NeZero M] in
/-- The exit time is at most the sum of the holding times spent away from `l`: the twin of
`SocialNetwork.hittingTimeCts_le_tsum`. -/
theorem biasedHittingTimeCts_le_tsum {u l : Profile N M} {θ : Set (Profile N M)} (hl : l ∈ θ)
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω)
    (hhit : ∃ k, stateAfter u (stepJumps ω) k ∈ θ) :
    biasedHittingTimeCts u θ ω
      ≤ ∑' n : ℕ, Set.indicator (biasedAvoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω := by
  classical
  have hk : stateAfter u (stepJumps ω) (Nat.find hhit) ∈ θ := Nat.find_spec hhit
  have hmin : ∀ j < Nat.find hhit, stateAfter u (stepJumps ω) j ∉ θ :=
    fun j hj => Nat.find_min hhit hj
  rcases Nat.eq_zero_or_pos (Nat.find hhit) with hk0 | hk0
  · have h0 : biasedHittingTimeCts u θ ω ≤ ENNReal.ofReal 0 := by
      refine sInf_le ⟨0, ⟨le_rfl, ?_⟩, rfl⟩
      rw [biasedProcess, jumpCount_zero hpos]
      rw [hk0] at hk
      exact hk
    rw [ENNReal.ofReal_zero] at h0
    exact h0.trans zero_le
  · calc biasedHittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime (Nat.find hhit) ω) :=
          biasedHittingTimeCts_le_jumpTime hpos hk0.ne' hk
      _ = ∑ n ∈ Finset.range (Nat.find hhit), ENNReal.ofReal (holdingTime n ω) :=
          ENNReal.ofReal_sum_of_nonneg fun n _ => (hpos n).le
      _ = ∑ n ∈ Finset.range (Nat.find hhit), Set.indicator (biasedAvoidUpTo u l n)
            (fun ω => ENNReal.ofReal (holdingTime n ω)) ω := by
          refine Finset.sum_congr rfl fun n hn =>
            (Set.indicator_of_mem ?_ (fun ω => ENNReal.ofReal (holdingTime n ω))).symm
          intro j hj heq
          exact hmin j (by have := Finset.mem_range.1 hn; omega) (heq ▸ hl)
      _ ≤ _ := ENNReal.sum_le_tsum _

/-- **The mean hitting time of any set containing a staircase profile is finite** for the biased
process, from every state of `S^α`, for `0 < γ < 1/(M-1)` and every `β ≥ 0`.  The twin of
`SocialNetwork.expHittingTimeCts_lt_top`, with the same proof. -/
theorem biasedExpHittingTimeCts_lt_top (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u)
    {θ : Set (Profile N M)} {o : Opinion M} (hθ : biasedLadderOf N o ∈ θ) :
    biasedExpHittingTimeCts γ β u θ < ∞ := by
  set l := biasedLadderOf (N := N) o with hl
  set P := biasedCtsPathMeasure γ β u with hP
  have hNN : 0 < N + N := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    omega
  have hc : 0 < ENNReal.ofReal (biasedZeta N M γ β) ^ N
      * ENNReal.ofReal (biasedStepFloor N M β
          (biasedGreedyBound N M + (N : ℝ) * (1 + γ))) ^ N := by
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · exact (ENNReal.ofReal_pos.2 (biasedZeta_pos N M γ β)).ne'
    · exact (ENNReal.ofReal_pos.2 (biasedStepFloor_pos N M β _)).ne'
  have hsum : ∑' m : ℕ, kacAvoid (biasedSkeletonKernel γ β) l m u ≠ ∞ :=
    tsum_kacAvoid_ne_top (biasedSkeletonKernel γ β) (S := biasedStateSet N M) hNN hc
      (fun v hv => biasedSkeletonKernel_compl_biasedStateSet γ β hv)
      (fun v hv => minorisation_iterateKernel hM hN hγ hγ' hβ o hv) hu
  have hsum' : ∑' n : ℕ, kacAvoid (biasedSkeletonKernel γ β) l (n + 1) u ≠ ∞ := by
    refine ne_top_of_le_ne_top hsum ?_
    rw [tsum_eq_zero_add' (f := fun m => kacAvoid (biasedSkeletonKernel γ β) l m u)
      ENNReal.summable]
    exact le_add_self
  have hPavoid : ∀ n, P (biasedAvoidUpTo u l n)
      = kacAvoid (biasedSkeletonKernel γ β) l (n + 1) u := by
    intro n
    rw [hP, biasedAvoidUpTo_eq_preimage, biasedCtsPathMeasure_preimage_stepJumps γ β u
      (measurableSet_biasedAvoidSet u l (n + 1)), kacAvoid_biasedSkeletonKernel]
  have hpos_ae : ∀ᵐ ω ∂P, ∀ n, 0 < holdingTime n ω := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (biasedCtsPathMeasure_holdingTime_nonpos γ β n u)] with ω hω
    simpa using hω
  have hhit_ae : ∀ᵐ ω ∂P, ∃ k, stateAfter u (stepJumps ω) k ∈ θ := by
    have hnull : P (⋂ n, biasedAvoidUpTo u l n) = 0 := by
      have htend : Filter.Tendsto (fun n => kacAvoid (biasedSkeletonKernel γ β) l (n + 1) u)
          Filter.atTop (nhds 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum'
      refine le_antisymm (ge_of_tendsto' htend fun n => ?_) zero_le
      rw [← hPavoid n]
      exact measure_mono (Set.iInter_subset _ n)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
    by_contra hne
    exact hω (Set.mem_iInter.2 fun n k _ heq => (not_exists.1 hne) k (heq ▸ hθ))
  have hmeasH : ∀ n, Measurable fun ω : ℕ → Step N M => ENNReal.ofReal (holdingTime n ω) :=
    fun n => ENNReal.measurable_ofReal.comp (measurable_holdingTime n)
  have hterm : ∀ n, ∫⁻ ω, Set.indicator (biasedAvoidUpTo u l n)
        (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P
      ≤ ∑' k : ℕ, P (biasedAvoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) := by
    intro n
    have hmeasE : ∀ k : ℕ,
        MeasurableSet (biasedAvoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) :=
      fun k => (measurableSet_biasedAvoidUpTo u l n).inter
        ((measurable_holdingTime n) measurableSet_Ioi)
    calc ∫⁻ ω, Set.indicator (biasedAvoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P
        ≤ ∫⁻ ω, ∑' k : ℕ, Set.indicator
            (biasedAvoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)})
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ biasedAvoidUpTo u l n
          · rw [Set.indicator_of_mem hω]
            refine (ofReal_le_tsum_indicator_Ioi _).trans (le_of_eq (tsum_congr fun k => ?_))
            by_cases hk : holdingTime n ω ∈ Set.Ioi (k : ℝ)
            · rw [Set.indicator_of_mem hk,
                Set.indicator_of_mem (show ω ∈ biasedAvoidUpTo u l n ∩
                  {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)} from ⟨hω, hk⟩)]
            · rw [Set.indicator_of_notMem hk,
                Set.indicator_of_notMem fun h => hk h.2]
          · rw [Set.indicator_of_notMem hω]
            exact zero_le
      _ = ∑' k : ℕ, P (biasedAvoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) := by
          rw [lintegral_tsum fun k => (measurable_const.indicator (hmeasE k)).aemeasurable]
          exact tsum_congr fun k => lintegral_indicator_one (hmeasE k)
  have hterm0 : ∀ k : ℕ, P (biasedAvoidUpTo u l 0 ∩ {ω | holdingTime 0 ω ∈ Set.Ioi (k : ℝ)})
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
    intro k
    refine (measure_mono Set.inter_subset_right).trans ?_
    have hset : {ω : ℕ → Step N M | holdingTime 0 ω ∈ Set.Ioi (k : ℝ)}
        = {ω | (k : ℝ) < holdingTime 0 ω} := rfl
    rw [hset, hP, biasedCtsPathMeasure_lt_holdingTime γ β u (Nat.cast_nonneg k),
      ← expMeasure_Ioi_of_nonneg (biasedTotalRate_pos γ β u) (Nat.cast_nonneg k)]
    exact expMeasure_biasedTotalRate_Ioi_le hM γ β hu k
  have htermS : ∀ m k : ℕ,
      P (biasedAvoidUpTo u l (m + 1) ∩ {ω | holdingTime (m + 1) ω ∈ Set.Ioi (k : ℝ)})
        ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) * P (biasedAvoidUpTo u l (m + 1)) := by
    intro m k
    have hmeasG : MeasurableSet {h : (i : Finset.Iic m) → Step N M |
        ∀ k ≤ m + 1, stateAfterStepHistory u h k ≠ l} := by
      have hpre : {h : (i : Finset.Iic m) → Step N M |
            ∀ k ≤ m + 1, stateAfterStepHistory u h k ≠ l}
          = (fun h : (i : Finset.Iic m) → Step N M => fun i => (h i).1) ⁻¹'
            {y | ∀ k ≤ m + 1, stateAfterHistory u y k ≠ l} := rfl
      rw [hpre]
      exact (measurable_stepHistoryJumps m) MeasurableSet.of_discrete
    rw [biasedAvoidUpTo_succ_eq_preimage]
    exact biasedCtsPathMeasure_history_holdingTime_le_mul γ β u m hmeasG measurableSet_Ioi
      fun h _ => expMeasure_biasedTotalRate_Ioi_le hM γ β
        (isBiasedState_stateAfter hu _ (m + 1)) k
  set D := ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) with hD
  calc biasedExpHittingTimeCts γ β u θ
      ≤ ∫⁻ ω, ∑' n : ℕ, Set.indicator (biasedAvoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpos_ae, hhit_ae] with ω h1 h2
        exact biasedHittingTimeCts_le_tsum hθ h1 h2
    _ = ∑' n : ℕ, ∫⁻ ω, Set.indicator (biasedAvoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P :=
        lintegral_tsum fun n =>
          ((hmeasH n).indicator (measurableSet_biasedAvoidUpTo u l n)).aemeasurable
    _ ≤ ∑' n : ℕ, ∑' k : ℕ,
          P (biasedAvoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) :=
        ENNReal.tsum_le_tsum hterm
    _ = (∑' k : ℕ, P (biasedAvoidUpTo u l 0 ∩ {ω | holdingTime 0 ω ∈ Set.Ioi (k : ℝ)}))
          + ∑' m : ℕ, ∑' k : ℕ,
            P (biasedAvoidUpTo u l (m + 1) ∩ {ω | holdingTime (m + 1) ω ∈ Set.Ioi (k : ℝ)}) :=
        tsum_eq_zero_add' ENNReal.summable
    _ ≤ D + ∑' m : ℕ, D * kacAvoid (biasedSkeletonKernel γ β) l (m + 2) u := by
        gcongr with m
        · exact ENNReal.tsum_le_tsum hterm0
        · calc ∑' k : ℕ,
                P (biasedAvoidUpTo u l (m + 1) ∩
                  {ω | holdingTime (m + 1) ω ∈ Set.Ioi (k : ℝ)})
              ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ)))
                  * P (biasedAvoidUpTo u l (m + 1)) :=
                ENNReal.tsum_le_tsum (htermS m)
            _ = D * kacAvoid (biasedSkeletonKernel γ β) l (m + 2) u := by
                rw [ENNReal.tsum_mul_right, hPavoid]
    _ < ∞ := by
        refine ENNReal.add_lt_top.2 ⟨tsum_ofReal_exp_neg_ne_top.lt_top, ?_⟩
        rw [ENNReal.tsum_mul_left]
        refine ENNReal.mul_lt_top tsum_ofReal_exp_neg_ne_top.lt_top ?_
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun m => ?_) hsum'.lt_top
        exact kacAvoid_antitone (biasedSkeletonKernel γ β) l (Nat.le_succ (m + 1)) u

/-- **The mean exit time from a biased consensus set is finite**, from every state of `S^α`, for
`0 < γ < 1/(M-1)` and every `β ≥ 0`: `E (R^{α,β,u} (C_α^{-o})) < ∞`.  This is what makes the
ratios of Theorem 31 and of the biased Proposition 12 mean what they say. -/
theorem biasedExpHittingTimeCts_consensusSetOther_lt_top (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 0 < γ) (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {u : Profile N M}
    (hu : IsBiasedState u) (o : Opinion M) :
    biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o) < ∞ := by
  obtain ⟨o', ho'⟩ : ∃ o' : Opinion M, o' ≠ o := by
    by_cases h0 : (o : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
  refine biasedExpHittingTimeCts_lt_top hM hN hγ hγ' hβ hu (o := o') ?_
  exact ⟨o', ho', (isBiasedLadder_biasedLadderOf (N := N) γ o').isBiasedConsensus hγ
    (by omega)⟩

/-- **The mean exit time from a biased consensus set is positive**: from `u ∈ C_α^o` the process
sits at `u`, which is not in `C_α^{-o}`, until its first jump. -/
theorem biasedExpHittingTimeCts_consensusSetOther_pos (hM : 2 ≤ M) {γ : ℝ}
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (β : ℝ) {o : Opinion M} {u : Profile N M}
    (hu : IsBiasedConsensus γ o u) :
    0 < biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o) := by
  set P := biasedCtsPathMeasure γ β u with hP
  have hpos_ae : ∀ᵐ ω ∂P, ∀ n, 0 < holdingTime n ω := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (biasedCtsPathMeasure_holdingTime_nonpos γ β n u)] with ω hω
    simpa using hω
  have hR : ∀ᵐ ω ∂P, 0 < biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω := by
    filter_upwards [hpos_ae] with ω hω
    have hge : ENNReal.ofReal (holdingTime 0 ω)
        ≤ biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω := by
      refine le_sInf ?_
      rintro x ⟨t, ⟨ht0, htθ⟩, rfl⟩
      refine ENNReal.ofReal_le_ofReal (not_lt.1 fun hlt => ?_)
      rw [biasedProcess_eq_of_lt_holdingTime u hω ht0 hlt] at htθ
      exact hu.notMem hM hγ' htθ
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (hω 0)) hge
  rw [pos_iff_ne_zero, Ne, biasedExpHittingTimeCts,
    lintegral_eq_zero_iff (measurable_biasedHittingTimeCts _ _)]
  intro h0
  have hfalse : ∀ᵐ _ω ∂P, False := by
    filter_upwards [hR, h0] with ω h1 h2
    rw [h2, Pi.zero_apply] at h1
    exact lt_irrefl _ h1
  have hnull := ae_iff.1 hfalse
  simp only [not_false_eq_true, Set.ofPred_true, measure_univ] at hnull
  exact one_ne_zero hnull

end ExitTime

end Bias

end SocialNetwork
