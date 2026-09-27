/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Graphical

/-!
# Collapsing [GL24]'s construction onto the jump-hold process

Placeholder header, rewritten at the end.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ}

/-! ### Shifting past a block of marks -/

/-- Shifting `k` times drops the first `k` steps. -/
theorem shiftHold_iterate {J : Type*} (k : ℕ) (ω : ℕ → Hold J) :
    shiftHold^[k] ω = fun i => ω (k + i) := by
  induction k generalizing ω with
  | zero => funext i; simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      funext i
      show ω (1 + (k + i)) = ω (k + 1 + i)
      congr 1
      omega

theorem measurable_shiftHold_iterate {J : Type*} [MeasurableSpace J] (k : ℕ) :
    Measurable (fun ω : ℕ → Hold J => shiftHold^[k] ω) :=
  (measurable_shiftHold (J := J)).iterate k

/-- Peeling the first holding time off a sum. -/
theorem holdSum_succ_shiftHold {J : Type*} (k : ℕ) (ω : ℕ → Hold J) :
    holdSum (k + 1) ω = (ω 0).2 + holdSum k (shiftHold ω) := by
  have h1 : holdSum (k + 1) ω = (∑ i ∈ Finset.range k, holdTime (i + 1) ω) + holdTime 0 ω :=
    Finset.sum_range_succ' _ k
  have h2 : holdSum k (shiftHold ω) = ∑ i ∈ Finset.range k, holdTime (i + 1) ω :=
    Finset.sum_congr rfl fun i _ => by
      show (ω (1 + i)).2 = (ω (i + 1)).2
      rw [Nat.add_comm]
  rw [h1, h2, add_comm]
  rfl

variable [NeZero N] [NeZero M]

/-! ### The rest of the band, after the first expression -/

/-- The first mark of the band that is not discarded carries the pair `p`; it is one of the
first `n` marks, it arrives by time `t`, and the marks that follow it lie in `E`.

This is `SocialNetwork.acceptedWithin` for the singleton `{p}`, with a condition imposed on
the marks after the expression.  The point of it is that the condition factors out: what the
band does after the first expression is a fresh band, started from the matrix the expression
leads to, and independent of when the expression happened. -/
def acceptedRest (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) (n : ℕ) (t : ℝ) :
    Set (ℕ → Hold (MarkJump N M)) :=
  {ω | ∃ k < n, (∀ i < k, (ω i).1 = MarkJump.discard) ∧ (ω k).1 = MarkJump.jump p
        ∧ holdSum (k + 1) ω ≤ t ∧ shiftHold^[k + 1] ω ∈ E}

omit [NeZero N] [NeZero M] in
/-- The event, with its deadline shifted by a measurable amount, is measurable in the pair. -/
theorem measurableSet_acceptedRest_comap {α : Type*} [MeasurableSpace α] {g : α → ℝ}
    (hg : Measurable g) (p : Jump N M) {E : Set (ℕ → Hold (MarkJump N M))}
    (hE : MeasurableSet E) (n : ℕ) (t : ℝ) :
    MeasurableSet {r : α × (ℕ → Hold (MarkJump N M)) |
      r.2 ∈ acceptedRest p E n (t - g r.1)} := by
  have hcoord : ∀ (i : ℕ) (c : Set (MarkJump N M)),
      MeasurableSet {r : α × (ℕ → Hold (MarkJump N M)) | (r.2 i).1 ∈ c} :=
    fun i c => (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))
      MeasurableSet.of_discrete
  have hset : {r : α × (ℕ → Hold (MarkJump N M)) | r.2 ∈ acceptedRest p E n (t - g r.1)}
      = ⋃ k ∈ Finset.range n,
          ((⋂ i ∈ Finset.range k, {r : α × (ℕ → Hold (MarkJump N M)) |
              (r.2 i).1 ∈ ({MarkJump.discard} : Set (MarkJump N M))})
            ∩ {r : α × (ℕ → Hold (MarkJump N M)) |
                (r.2 k).1 ∈ ({MarkJump.jump p} : Set (MarkJump N M))}
            ∩ ({r : α × (ℕ → Hold (MarkJump N M)) | holdSum (k + 1) r.2 + g r.1 ≤ t}
              ∩ {r : α × (ℕ → Hold (MarkJump N M)) | shiftHold^[k + 1] r.2 ∈ E})) := by
    ext r
    simp only [acceptedRest, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨k, hk, hdis, hjump, htime, hrest⟩
      exact ⟨k, hk, ⟨⟨fun i hi => hdis i hi, hjump⟩, by linarith, hrest⟩⟩
    · rintro ⟨k, hk, ⟨hdis, hjump⟩, htime, hrest⟩
      exact ⟨k, hk, fun i hi => hdis i hi, hjump, by linarith, hrest⟩
  rw [hset]
  refine MeasurableSet.biUnion (Finset.range n).countable_toSet fun k _ => ?_
  refine ((MeasurableSet.biInter (Finset.range k).countable_toSet fun i _ => hcoord i _).inter
    (hcoord k _)).inter (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le
      (((measurable_holdSum (k + 1)).comp measurable_snd).add (hg.comp measurable_fst))
      measurable_const
  · exact ((measurable_shiftHold_iterate (k + 1)).comp measurable_snd) hE

omit [NeZero N] [NeZero M] in
theorem measurableSet_acceptedRest (p : Jump N M) {E : Set (ℕ → Hold (MarkJump N M))}
    (hE : MeasurableSet E) (n : ℕ) (t : ℝ) : MeasurableSet (acceptedRest p E n t) := by
  have h := measurableSet_acceptedRest_comap (α := ℝ) measurable_id p hE n t
  have hmap : Measurable fun ω : ℕ → Hold (MarkJump N M) => ((0 : ℝ), ω) :=
    measurable_const.prodMk measurable_id
  have hrw : acceptedRest p E n t
      = (fun ω : ℕ → Hold (MarkJump N M) => ((0 : ℝ), ω)) ⁻¹'
        {r : ℝ × (ℕ → Hold (MarkJump N M)) | r.2 ∈ acceptedRest p E n (t - r.1)} := by
    ext ω; simp
  rw [hrw]
  exact hmap h

omit [NeZero N] [NeZero M] in
theorem measurableSet_acceptedRest_prod (p : Jump N M) {E : Set (ℕ → Hold (MarkJump N M))}
    (hE : MeasurableSet E) (n : ℕ) (t : ℝ) :
    MeasurableSet {q : Hold (MarkJump N M) × (ℕ → Hold (MarkJump N M)) |
      q.2 ∈ acceptedRest p E n (t - q.1.2)} :=
  measurableSet_acceptedRest_comap measurable_snd p hE n t

omit [NeZero N] [NeZero M] in
/-- Either the first mark expresses `p`, or it is discarded and the band starts again. -/
theorem acceptedRest_succ (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) (n : ℕ) (t : ℝ) :
    acceptedRest p E (n + 1) t
      = ({ω | (ω 0).1 = MarkJump.jump p ∧ (ω 0).2 ≤ t} ∩ shiftHold ⁻¹' E)
        ∪ {ω | (ω 0).1 = MarkJump.discard
            ∧ shiftHold ω ∈ acceptedRest p E n (t - (ω 0).2)} := by
  ext ω
  constructor
  · rintro ⟨k, hk, hdis, hjump, htime, hrest⟩
    cases k with
    | zero =>
        refine Or.inl ⟨⟨hjump, ?_⟩, ?_⟩
        · rw [holdSum_succ_shiftHold 0 ω] at htime
          simpa [holdSum] using htime
        · simpa using hrest
    | succ k =>
        refine Or.inr ⟨hdis 0 (by omega), ⟨k, by omega, ?_, ?_, ?_, ?_⟩⟩
        · intro i hi
          show (ω (1 + i)).1 = MarkJump.discard
          exact hdis (1 + i) (by omega)
        · show (ω (1 + k)).1 = MarkJump.jump p
          rw [show 1 + k = k + 1 by omega]
          exact hjump
        · rw [holdSum_succ_shiftHold (k + 1) ω] at htime
          linarith
        · rwa [Function.iterate_succ_apply] at hrest
  · rintro (⟨⟨hjump, htime⟩, hrest⟩ | ⟨hdis, k, hk, hdis', hjump, htime, hrest⟩)
    · refine ⟨0, by omega, fun i hi => absurd hi (by omega), hjump, ?_, ?_⟩
      · rw [holdSum_succ_shiftHold 0 ω]
        simpa [holdSum] using htime
      · simpa using hrest
    · refine ⟨k + 1, by omega, ?_, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hdis
        | succ i =>
            have := hdis' i (by omega)
            show (ω (i + 1)).1 = MarkJump.discard
            rw [show i + 1 = 1 + i by omega]
            exact this
      · show (ω (k + 1)).1 = MarkJump.jump p
        rw [show k + 1 = 1 + k by omega]
        exact hjump
      · rw [holdSum_succ_shiftHold (k + 1) ω]
        linarith
      · rw [Function.iterate_succ_apply]
        exact hrest

/-! ### The rest factors out -/

/-- **One discarded mark, with a condition on what follows.**  This is the second half of
`SocialNetwork.measure_acceptedWithin_succ`, stated for an arbitrary family of events indexed
by the holding time of the discarded mark. -/
theorem measure_discard_restart (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    {F : ℝ → Set (ℕ → Hold (MarkJump N M))}
    (hF : MeasurableSet {q : Hold (MarkJump N M) × (ℕ → Hold (MarkJump N M)) |
      q.2 ∈ F q.1.2}) :
    markPathMeasure hM hβ v {ω | (ω 0).1 = MarkJump.discard ∧ shiftHold ω ∈ F (ω 0).2}
      = ∫⁻ z in {z : Hold (MarkJump N M) | z.1 = MarkJump.discard},
          markPathMeasure hM hβ v (F z.2) ∂(markLaw hM hβ v) := by
  classical
  set D : Set (Hold (MarkJump N M)) := {z | z.1 = MarkJump.discard} with hDdef
  have hD : MeasurableSet D := measurable_fst (measurableSet_singleton MarkJump.discard)
  have hslice : ∀ z : Hold (MarkJump N M), MeasurableSet (F z.2) := fun z =>
    measurable_prodMk_left hF
  have hfirst : Measurable fun ω : ℕ → Hold (MarkJump N M) => ω 0 := measurable_pi_apply 0
  have hpair : Measurable fun ω : ℕ → Hold (MarkJump N M) => (ω 0, shiftHold ω) :=
    hfirst.prodMk measurable_shiftHold
  set S₂ : Set (ℕ → Hold (MarkJump N M)) :=
    {ω | (ω 0).1 = MarkJump.discard ∧ shiftHold ω ∈ F (ω 0).2} with hS₂
  have hmeas2 : MeasurableSet S₂ := (hfirst hD).inter (hpair hF)
  set f : Hold (MarkJump N M) → (ℕ → Hold (MarkJump N M)) → ℝ≥0∞ :=
    fun z ω' => if z ∈ D then
      Set.indicator (F z.2) (1 : (ℕ → Hold (MarkJump N M)) → ℝ≥0∞) ω' else 0 with hf
  have hfmeas : Measurable (Function.uncurry f) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurable_fst hD
    · exact measurable_const.indicator hF
  have hind : ∀ ω : ℕ → Hold (MarkJump N M),
      Set.indicator S₂ (1 : (ℕ → Hold (MarkJump N M)) → ℝ≥0∞) ω = f (ω 0) (shiftHold ω) := by
    intro ω
    by_cases hd : ω 0 ∈ D
    · rw [hf]
      simp only [if_pos hd]
      by_cases hin : shiftHold ω ∈ F (ω 0).2
      · rw [Set.indicator_of_mem hin, Set.indicator_of_mem (show ω ∈ S₂ from ⟨hd, hin⟩)]
        rfl
      · rw [Set.indicator_of_notMem hin, Set.indicator_of_notMem (fun hcon => hin hcon.2)]
    · rw [hf]
      simp only [if_neg hd]
      rw [Set.indicator_of_notMem (fun hcon => hd hcon.1)]
  rw [← lintegral_indicator_one hmeas2, lintegral_congr hind, markPathMeasure,
    lintegral_drivenMeasure_restart markNext (markLaw hM hβ) v hfmeas,
    ← lintegral_indicator hD]
  refine lintegral_congr fun z => ?_
  by_cases hd : z ∈ D
  · rw [Set.indicator_of_mem hd, hf]
    simp only [if_pos hd]
    rw [lintegral_indicator_one (hslice z)]
    show markPathMeasure hM hβ (markNext v z.1) _ = _
    rw [show z.1 = MarkJump.discard from hd]
    rfl
  · rw [Set.indicator_of_notMem hd, hf]
    simp only [if_neg hd]
    exact lintegral_zero

omit [NeZero N] [NeZero M] in
theorem measurableSet_acceptJump (p : Jump N M) (t : ℝ) :
    MeasurableSet {z : Hold (MarkJump N M) | z.1 = MarkJump.jump p ∧ z.2 ≤ t} :=
  (measurable_fst (measurableSet_singleton (MarkJump.jump p))).inter
    (measurableSet_le measurable_snd measurable_const)

/-- **What happens after the first expression is a fresh band.**  The condition `E` on the
marks after the expression contributes a constant factor — the probability that a band started
from the matrix `express p v` lies in `E` — whatever the deadline `t` and however many marks
were discarded first.  This is the independence [GL24]'s construction is built to have: the
marks of the Poisson process are independent of one another, so the ones above the first
accepted mark know nothing of the ones below it. -/
theorem measure_acceptedRest (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (p : Jump N M)
    {E : Set (ℕ → Hold (MarkJump N M))} (hE : MeasurableSet E) (n : ℕ) (t : ℝ)
    (v : Pressure N M) :
    markPathMeasure hM hβ v (acceptedRest p E n t)
      = markPathMeasure hM hβ (express p.1 p.2 v) E
        * markPathMeasure hM hβ v (acceptedWithin {p} n t) := by
  classical
  induction n generalizing t with
  | zero =>
      have h1 : acceptedRest p E 0 t = ∅ := by
        ext ω
        simp only [acceptedRest, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨k, hk, -⟩
        omega
      have h2 : acceptedWithin ({p} : Finset (Jump N M)) 0 t = ∅ := by
        ext ω
        simp only [acceptedWithin, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨k, hk, -⟩
        omega
      rw [h1, h2, measure_empty, mul_zero]
  | succ n ih =>
      set A : Set (Hold (MarkJump N M)) :=
        {z | z.1 = MarkJump.jump p ∧ z.2 ≤ t} with hAdef
      have hA : MeasurableSet A := measurableSet_acceptJump p t
      set S₁ : Set (ℕ → Hold (MarkJump N M)) := {ω | ω 0 ∈ A} ∩ shiftHold ⁻¹' E with hS₁
      set S₂ : Set (ℕ → Hold (MarkJump N M)) :=
        {ω | (ω 0).1 = MarkJump.discard
          ∧ shiftHold ω ∈ acceptedRest p E n (t - (ω 0).2)} with hS₂
      have hfirst : Measurable fun ω : ℕ → Hold (MarkJump N M) => ω 0 := measurable_pi_apply 0
      have hpair : Measurable fun ω : ℕ → Hold (MarkJump N M) => (ω 0, shiftHold ω) :=
        hfirst.prodMk measurable_shiftHold
      have hD : MeasurableSet {z : Hold (MarkJump N M) | z.1 = MarkJump.discard} :=
        measurable_fst (measurableSet_singleton MarkJump.discard)
      have hmeas2 : MeasurableSet S₂ :=
        (hfirst hD).inter (hpair (measurableSet_acceptedRest_prod p hE n t))
      have hdisj : Disjoint S₁ S₂ := by
        rw [Set.disjoint_left]
        rintro ω ⟨⟨hp, -⟩, -⟩ ⟨hd, -⟩
        rw [hp] at hd
        exact absurd hd (by simp)
      -- the first mark expresses `p`
      have h1 : markPathMeasure hM hβ v S₁
          = markPathMeasure hM hβ (express p.1 p.2 v) E * markLaw hM hβ v A := by
        have hcongr : ∀ z ∈ A,
            drivenMeasure markNext (markLaw hM hβ) (markNext v z.1) E
              = markPathMeasure hM hβ (express p.1 p.2 v) E := by
          intro z hz
          rw [show z.1 = MarkJump.jump p from hz.1]
          rfl
        rw [hS₁, markPathMeasure, drivenMeasure_restart markNext (markLaw hM hβ) v hA hE,
          setLIntegral_congr_fun hA hcongr, setLIntegral_const]
      -- or it is discarded
      have h2 : markPathMeasure hM hβ v S₂
          = markPathMeasure hM hβ (express p.1 p.2 v) E
            * ∫⁻ z in {z : Hold (MarkJump N M) | z.1 = MarkJump.discard},
                markPathMeasure hM hβ v (acceptedWithin {p} n (t - z.2))
                  ∂(markLaw hM hβ v) := by
        rw [hS₂, measure_discard_restart hM hβ v (F := fun s => acceptedRest p E n (t - s))
            (measurableSet_acceptedRest_prod p hE n t),
          ← lintegral_const_mul' _ _ (measure_ne_top (markPathMeasure hM hβ
            (express p.1 p.2 v)) E)]
        exact setLIntegral_congr_fun hD fun z _ => ih (t - z.2)
      have hAeq : A = {z : Hold (MarkJump N M) |
          (∃ q ∈ ({p} : Finset (Jump N M)), z.1 = MarkJump.jump q) ∧ z.2 ≤ t} := by
        ext z
        simp [hAdef]
      have hunion : acceptedRest p E (n + 1) t = S₁ ∪ S₂ := acceptedRest_succ p E n t
      rw [hunion, measure_union hdisj hmeas2, h1, h2,
        measure_acceptedWithin_succ hM hβ ({p} : Finset (Jump N M)) n t v, mul_add, hAeq]

end SocialNetwork
