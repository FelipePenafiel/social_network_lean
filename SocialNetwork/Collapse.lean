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

/-! ### The first expression of the band -/

/-- Some mark of the band is not discarded.  [GL24]'s construction reads the process off the
marks above the strip, so this is the event on which it says anything at all; it has full
probability because the accepted marks carry rate `q(v) > 0` whatever the matrix is. -/
def Accepts : Set (ℕ → Hold (MarkJump N M)) := {ω | ∃ k, (ω k).1 ≠ MarkJump.discard}

omit [NeZero N] [NeZero M] in
theorem measurableSet_Accepts : MeasurableSet (Accepts (N := N) (M := M)) := by
  have : Accepts (N := N) (M := M)
      = ⋃ k : ℕ, {ω : ℕ → Hold (MarkJump N M) | (ω k).1 ∈ ({MarkJump.discard}ᶜ :
          Set (MarkJump N M))} := by
    ext ω; simp [Accepts]
  rw [this]
  exact MeasurableSet.iUnion fun k =>
    (measurable_fst.comp (measurable_pi_apply k)) MeasurableSet.of_discrete

open Classical in
/-- The index of the first mark that is not discarded, `0` on the null event that there is
none. -/
noncomputable def firstAccept (ω : ℕ → Hold (MarkJump N M)) : ℕ :=
  if h : ∃ k, (ω k).1 ≠ MarkJump.discard then Nat.find h else 0

omit [NeZero N] [NeZero M] in
theorem firstAccept_eq_of {ω : ℕ → Hold (MarkJump N M)} {k : ℕ}
    (hdis : ∀ i < k, (ω i).1 = MarkJump.discard) (hk : (ω k).1 ≠ MarkJump.discard) :
    firstAccept ω = k := by
  classical
  have h : ∃ k, (ω k).1 ≠ MarkJump.discard := ⟨k, hk⟩
  rw [firstAccept, dif_pos h]
  exact Nat.find_eq_iff h |>.2 ⟨hk, fun i hi hcon => hcon (hdis i hi)⟩

omit [NeZero N] [NeZero M] in
theorem firstAccept_spec {ω : ℕ → Hold (MarkJump N M)} (h : ω ∈ Accepts) :
    (∀ i < firstAccept ω, (ω i).1 = MarkJump.discard)
      ∧ (ω (firstAccept ω)).1 ≠ MarkJump.discard := by
  classical
  have h' : ∃ k, (ω k).1 ≠ MarkJump.discard := h
  rw [firstAccept, dif_pos h']
  exact ⟨fun i hi => not_not.1 (Nat.find_min h' hi), Nat.find_spec h'⟩

omit [NeZero N] [NeZero M] in
theorem measurable_firstAccept : Measurable (firstAccept (N := N) (M := M)) := by
  classical
  refine measurable_to_countable' fun k => ?_
  have hcoord : ∀ (j : ℕ) (c : Set (MarkJump N M)),
      MeasurableSet {ω : ℕ → Hold (MarkJump N M) | (ω j).1 ∈ c} :=
    fun j c => (measurable_fst.comp (measurable_pi_apply j)) MeasurableSet.of_discrete
  have hdis : ∀ j : ℕ, MeasurableSet
      {ω : ℕ → Hold (MarkJump N M) | (ω j).1 = MarkJump.discard} :=
    fun j => hcoord j {MarkJump.discard}
  have hacc : ∀ j : ℕ, MeasurableSet
      {ω : ℕ → Hold (MarkJump N M) | (ω j).1 ≠ MarkJump.discard} :=
    fun j => hcoord j {MarkJump.discard}ᶜ
  have hbase : MeasurableSet {ω : ℕ → Hold (MarkJump N M) |
      (∀ i < k, (ω i).1 = MarkJump.discard) ∧ (ω k).1 ≠ MarkJump.discard} := by
    have : {ω : ℕ → Hold (MarkJump N M) |
        (∀ i < k, (ω i).1 = MarkJump.discard) ∧ (ω k).1 ≠ MarkJump.discard}
        = (⋂ i ∈ Finset.range k, {ω : ℕ → Hold (MarkJump N M) |
            (ω i).1 = MarkJump.discard}) ∩ {ω | (ω k).1 ≠ MarkJump.discard} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
    rw [this]
    exact (MeasurableSet.biInter (Finset.range k).countable_toSet fun i _ => hdis i).inter (hacc k)
  by_cases hk : k = 0
  · subst hk
    have hset : firstAccept ⁻¹' ({0} : Set ℕ)
        = {ω : ℕ → Hold (MarkJump N M) | (ω 0).1 ≠ MarkJump.discard} ∪ Acceptsᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases hacc' : ω ∈ Accepts
        · exact Or.inl (h ▸ (firstAccept_spec hacc').2)
        · exact Or.inr hacc'
      · rintro (h | h)
        · exact firstAccept_eq_of (fun i hi => absurd hi (by omega)) h
        · rw [firstAccept, dif_neg (show ¬ ∃ k, (ω k).1 ≠ MarkJump.discard from h)]
    rw [hset]
    exact (hacc 0).union measurableSet_Accepts.compl
  · have hset : firstAccept ⁻¹' ({k} : Set ℕ)
        = {ω : ℕ → Hold (MarkJump N M) |
            (∀ i < k, (ω i).1 = MarkJump.discard) ∧ (ω k).1 ≠ MarkJump.discard} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        by_cases hacc' : ω ∈ Accepts
        · exact ⟨fun i hi => (firstAccept_spec hacc').1 i (h ▸ hi), h ▸ (firstAccept_spec hacc').2⟩
        · rw [firstAccept,
            dif_neg (show ¬ ∃ k, (ω k).1 ≠ MarkJump.discard from hacc')] at h
          exact absurd h.symm hk
      · rintro ⟨h1, h2⟩
        exact firstAccept_eq_of h1 h2
    rw [hset]
    exact hbase

omit [NeZero N] [NeZero M] in
/-- A function of the path that reads the index of the first accepted mark is measurable. -/
theorem measurable_of_firstAccept {α : Type*} [MeasurableSpace α]
    {G : ℕ → (ℕ → Hold (MarkJump N M)) → α} (hG : ∀ k, Measurable (G k)) :
    Measurable fun ω => G (firstAccept ω) ω := by
  refine fun s hs => ?_
  have hset : (fun ω => G (firstAccept ω) ω) ⁻¹' s
      = ⋃ k : ℕ, (firstAccept ⁻¹' ({k} : Set ℕ)) ∩ (G k ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨firstAccept ω, rfl, h⟩, fun ⟨k, hk, h⟩ => hk ▸ h⟩
  rw [hset]
  exact MeasurableSet.iUnion fun k =>
    (measurable_firstAccept (measurableSet_singleton k)).inter (hG k hs)

/-- The pair carried by the first accepted mark, junk on the null event of no acceptance. -/
noncomputable def markJumpOf : MarkJump N M → Jump N M
  | .discard => default
  | .jump p => p

/-- The pair expressed at the first accepted mark. -/
noncomputable def acceptedJump (ω : ℕ → Hold (MarkJump N M)) : Jump N M :=
  markJumpOf (ω (firstAccept ω)).1

/-- The time of the first accepted mark: the marks of the band arrive after independent
exponential times of rate `λ + q^>(v)`, and this is the sum of the ones up to and including
the first that is not discarded. -/
noncomputable def acceptedTime (ω : ℕ → Hold (MarkJump N M)) : ℝ :=
  holdSum (firstAccept ω + 1) ω

/-- One step of the jump-hold process, read off the band. -/
noncomputable def collapseStep (ω : ℕ → Hold (MarkJump N M)) : Step N M :=
  (acceptedJump ω, acceptedTime ω)

/-- The marks of the band above the first accepted one. -/
noncomputable def restAfterAccept (ω : ℕ → Hold (MarkJump N M)) : ℕ → Hold (MarkJump N M) :=
  shiftHold^[firstAccept ω + 1] ω

theorem measurable_acceptedJump : Measurable (acceptedJump (N := N) (M := M)) :=
  measurable_of_firstAccept fun k =>
    Measurable.of_discrete.comp (measurable_fst.comp (measurable_pi_apply k))

omit [NeZero N] [NeZero M] in
theorem measurable_acceptedTime : Measurable (acceptedTime (N := N) (M := M)) :=
  measurable_of_firstAccept fun k => measurable_holdSum (k + 1)

theorem measurable_collapseStep : Measurable (collapseStep (N := N) (M := M)) :=
  measurable_acceptedJump.prodMk measurable_acceptedTime

omit [NeZero N] [NeZero M] in
theorem measurable_restAfterAccept : Measurable (restAfterAccept (N := N) (M := M)) :=
  measurable_of_firstAccept fun k => measurable_shiftHold_iterate (k + 1)

/-! ### The band a.s. expresses -/

/-- The first `n` marks are all discarded with probability `((Λ - q)/Λ)^n`: the matrix does not
move while marks are discarded, so the band is the same at every one of them. -/
theorem measure_allDiscard (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) (n : ℕ) :
    markPathMeasure hM hβ v {ω | ∀ i < n, (ω i).1 = MarkJump.discard}
      = ENNReal.ofReal (((bandRate β v - totalRate β v) / bandRate β v) ^ n) := by
  have hD : MeasurableSet {z : Hold (MarkJump N M) | z.1 = MarkJump.discard} :=
    measurable_fst (measurableSet_singleton MarkJump.discard)
  have hmass : markLaw hM hβ v {z : Hold (MarkJump N M) | z.1 = MarkJump.discard}
      = ENNReal.ofReal ((bandRate β v - totalRate β v) / bandRate β v) := by
    have hprob : IsProbabilityMeasure (expMeasure (bandRate β v)) :=
      isProbabilityMeasure_expMeasure (bandRate_pos β v)
    have h := lintegral_discard_markLaw hM hβ v (f := fun _ => (1 : ℝ≥0∞)) measurable_const
    simpa [bandRate_sub_totalRate β v] using h
  induction n with
  | zero =>
      have hset : {ω : ℕ → Hold (MarkJump N M) | ∀ i < 0, (ω i).1 = MarkJump.discard}
          = Set.univ := by
        ext ω; simp
      rw [hset, pow_zero, ENNReal.ofReal_one, measure_univ]
  | succ n ih =>
      have hmeas : MeasurableSet {ω : ℕ → Hold (MarkJump N M) |
          ∀ i < n, (ω i).1 = MarkJump.discard} := by
        have : {ω : ℕ → Hold (MarkJump N M) | ∀ i < n, (ω i).1 = MarkJump.discard}
            = ⋂ i ∈ Finset.range n, {ω : ℕ → Hold (MarkJump N M) |
                (ω i).1 = MarkJump.discard} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
        rw [this]
        exact MeasurableSet.biInter (Finset.range n).countable_toSet fun i _ =>
          (measurable_fst.comp (measurable_pi_apply i))
            (MeasurableSet.of_discrete (s := {MarkJump.discard}))
      have hset : {ω : ℕ → Hold (MarkJump N M) | ∀ i < n + 1, (ω i).1 = MarkJump.discard}
          = {ω : ℕ → Hold (MarkJump N M) | ω 0 ∈ {z : Hold (MarkJump N M) |
              z.1 = MarkJump.discard}}
            ∩ shiftHold ⁻¹' {ω | ∀ i < n, (ω i).1 = MarkJump.discard} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · intro h
          refine ⟨h 0 (by omega), fun i hi => ?_⟩
          show (ω (1 + i)).1 = MarkJump.discard
          exact h (1 + i) (by omega)
        · rintro ⟨h0, hrest⟩ i hi
          cases i with
          | zero => exact h0
          | succ i =>
              have := hrest i (by omega)
              show (ω (i + 1)).1 = MarkJump.discard
              rw [show i + 1 = 1 + i by omega]
              exact this
      have hcongr : ∀ z ∈ {z : Hold (MarkJump N M) | z.1 = MarkJump.discard},
          drivenMeasure markNext (markLaw hM hβ) (markNext v z.1)
              {ω | ∀ i < n, (ω i).1 = MarkJump.discard}
            = ENNReal.ofReal (((bandRate β v - totalRate β v) / bandRate β v) ^ n) := by
        intro z hz
        rw [show z.1 = MarkJump.discard from hz]
        exact ih
      rw [hset, markPathMeasure, drivenMeasure_restart markNext (markLaw hM hβ) v hD hmeas,
        setLIntegral_congr_fun hD hcongr, setLIntegral_const, hmass,
        ← ENNReal.ofReal_mul (pow_nonneg (discardRatio_nonneg hM hβ v) n), ← pow_succ]

/-- **The band a.s. expresses.**  Since the accepted marks carry the total rate `q(v) > 0`
whatever the matrix is, the chance that the first `n` marks are all discarded decays
geometrically. -/
theorem measure_Accepts_compl (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    markPathMeasure hM hβ v Acceptsᶜ = 0 := by
    set δ := (bandRate β v - totalRate β v) / bandRate β v with hδdef
    have hδ0 : 0 ≤ δ := discardRatio_nonneg hM hβ v
    have hδ1 : δ < 1 := discardRatio_lt_one β v
    have h0 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (δ ^ n)) Filter.atTop (nhds 0) := by
      simp_rw [ENNReal.ofReal_pow hδ0]
      exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hδ1)
    refine le_antisymm (ge_of_tendsto' h0 fun n => ?_) (zero_le)
    rw [← measure_allDiscard hM hβ v n]
    refine measure_mono fun ω hω => ?_
    simp only [Accepts, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not] at hω
    exact fun i _ => hω i

theorem measure_Accepts (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    markPathMeasure hM hβ v Accepts = 1 := by
  have h := measure_add_measure_compl (μ := markPathMeasure hM hβ v) measurableSet_Accepts
  rw [measure_Accepts_compl hM hβ v, add_zero] at h
  rw [h, measure_univ]

/-! ### The first expression follows `stepLaw` -/

theorem jumpPMF_eq_ofReal (β : ℝ) (v : Pressure N M) (p : Jump N M) :
    jumpPMF β v p = ENNReal.ofReal (jumpRate β v p.1 p.2 / totalRate β v) := by
  have hsum : ∑' q : Jump N M, jumpWeight β v q = ENNReal.ofReal (totalRate β v) := by
    rw [tsum_fintype, totalRate]
    exact (ENNReal.ofReal_sum_of_nonneg fun q _ => (jumpRate_pos β v q.1 q.2).le).symm
  rw [jumpPMF_apply, hsum, jumpWeight, ← ENNReal.ofReal_inv_of_pos (totalRate_pos β v),
    ← ENNReal.ofReal_mul (jumpRate_pos β v p.1 p.2).le, ← div_eq_mul_inv]

/-- The rectangle of `SocialNetwork.stepLaw`: the pair `p` is expressed, by time `t`. -/
theorem stepLaw_singleton_Iic (β : ℝ) (v : Pressure N M) (p : Jump N M) {t : ℝ} (ht : 0 ≤ t) :
    stepLaw β v (({p} : Set (Jump N M)) ×ˢ Set.Iic t)
      = ENNReal.ofReal (jumpRate β v p.1 p.2 / totalRate β v
          * (1 - Real.exp (-(totalRate β v * t)))) := by
  have hprob : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure (totalRate_pos β v)
  rw [stepLaw, Measure.prod_prod, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p),
    expMeasure_Iic_of_nonneg (totalRate_pos β v) ht, jumpPMF_eq_ofReal,
    ← ENNReal.ofReal_mul (div_nonneg (jumpRate_pos β v p.1 p.2).le (totalRate_pos β v).le)]

theorem stepLaw_singleton_Iic_of_neg (β : ℝ) (v : Pressure N M) (p : Jump N M) {t : ℝ}
    (ht : t < 0) : stepLaw β v (({p} : Set (Jump N M)) ×ˢ Set.Iic t) = 0 := by
  have hprob : IsProbabilityMeasure (expMeasure (totalRate β v)) :=
    isProbabilityMeasure_expMeasure (totalRate_pos β v)
  have hIic : expMeasure (totalRate β v) (Set.Iic t) = 0 :=
    le_antisymm ((measure_mono (Set.Iic_subset_Iic.2 ht.le)).trans_eq
      (expMeasure_Iic_zero (totalRate_pos β v))) (zero_le)
  rw [stepLaw, Measure.prod_prod, hIic, mul_zero]

omit [NeZero N] [NeZero M] in
theorem acceptedRest_mono (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) (t : ℝ) :
    Monotone fun n => acceptedRest p E n t := by
  intro m n hmn ω hω
  obtain ⟨k, hk, hrest⟩ := hω
  exact ⟨k, lt_of_lt_of_le hk hmn, hrest⟩

/-- **The first expression of the band, and everything above it.**  Discarding the null event
on which no mark is ever accepted, the first accepted mark carries the pair `p` by time `t`
exactly when one of the `acceptedRest` events holds. -/
theorem accepts_inter_collapse (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) (t : ℝ) :
    ({ω | acceptedJump ω = p} ∩ restAfterAccept ⁻¹' E ∩ acceptedTime ⁻¹' Set.Iic t) ∩ Accepts
      = ⋃ n, acceptedRest p E n t := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iic,
    Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨hjump, hrest⟩, htime⟩, hacc⟩
    obtain ⟨hdis, hne⟩ := firstAccept_spec hacc
    refine ⟨firstAccept ω + 1, firstAccept ω, by omega, hdis, ?_, htime, hrest⟩
    revert hjump hne
    cases h : (ω (firstAccept ω)).1 with
    | discard => intro _ hne; exact absurd rfl hne
    | jump q =>
        intro hjump _
        rw [acceptedJump, h] at hjump
        exact congrArg MarkJump.jump hjump
  · rintro ⟨n, k, hk, hdis, hjump, htime, hrest⟩
    have hne : (ω k).1 ≠ MarkJump.discard := by rw [hjump]; simp
    have hacc : ω ∈ Accepts := ⟨k, hne⟩
    have hfa : firstAccept ω = k := firstAccept_eq_of hdis hne
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hacc⟩
    · rw [acceptedJump, hfa, hjump]
      rfl
    · rw [restAfterAccept, hfa]; exact hrest
    · rw [acceptedTime, hfa]; exact htime

/-- **The law of the first expression, with the band above it.**  For every deadline, the
first accepted mark carries `p` by time `t` and is followed by a band in `E` with probability
`stepLaw (β, v) ({p} × Iic t)` times the chance that a fresh band from `express p v` lies in
`E`.  This is [GL24]'s construction identified with one step of the jump-hold process. -/
theorem measure_collapse_Iic (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (p : Jump N M)
    {E : Set (ℕ → Hold (MarkJump N M))} (hE : MeasurableSet E) (t : ℝ) (v : Pressure N M) :
    markPathMeasure hM hβ v
        ({ω | acceptedJump ω = p} ∩ restAfterAccept ⁻¹' E ∩ acceptedTime ⁻¹' Set.Iic t)
      = markPathMeasure hM hβ (express p.1 p.2 v) E
        * stepLaw β v (({p} : Set (Jump N M)) ×ˢ Set.Iic t) := by
  classical
  set X : Set (ℕ → Hold (MarkJump N M)) :=
    {ω | acceptedJump ω = p} ∩ restAfterAccept ⁻¹' E ∩ acceptedTime ⁻¹' Set.Iic t with hX
  have hnull : markPathMeasure hM hβ v (X \ Accepts) = 0 :=
    le_antisymm ((measure_mono (Set.sdiff_subset_compl X Accepts)).trans_eq
      (measure_Accepts_compl hM hβ v)) (zero_le)
  have hrewrite : markPathMeasure hM hβ v X = ⨆ n, markPathMeasure hM hβ v (acceptedRest p E n t) := by
    have hsplit := measure_inter_add_sdiff (μ := markPathMeasure hM hβ v) X measurableSet_Accepts
    rw [hnull, add_zero] at hsplit
    rw [← hsplit, hX, accepts_inter_collapse p E t,
      (acceptedRest_mono p E t).measure_iUnion]
  rw [hrewrite]
  have hfactor : ∀ n, markPathMeasure hM hβ v (acceptedRest p E n t)
      = markPathMeasure hM hβ (express p.1 p.2 v) E
        * markPathMeasure hM hβ v (acceptedWithin {p} n t) :=
    fun n => measure_acceptedRest hM hβ p hE n t v
  simp_rw [hfactor]
  rw [← ENNReal.mul_iSup]
  congr 1
  rcases lt_or_ge t 0 with ht | ht
  · rw [stepLaw_singleton_Iic_of_neg β v p ht]
    refine iSup_eq_bot.2 fun n => ?_
    exact measure_acceptedWithin_of_neg hM hβ ({p} : Finset (Jump N M)) n ht v
  · rw [iSup_measure_acceptedWithin hM hβ ({p} : Finset (Jump N M)) ht v,
      stepLaw_singleton_Iic β v p ht, Finset.sum_singleton]

/-! ### The joint law of the first expression and the band above it -/

/-- The kernel that restarts the band at the matrix the expression leads to. -/
noncomputable def collapseKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    Kernel (Step N M) (ℕ → Hold (MarkJump N M)) where
  toFun z := markPathMeasure hM hβ (express z.1.1 z.1.2 v)
  measurable' := (Measurable.of_discrete (f := fun p : Jump N M =>
    markPathMeasure hM hβ (express p.1 p.2 v))).comp measurable_fst

theorem collapseKernel_apply (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (z : Step N M) :
    collapseKernel hM hβ v z = markPathMeasure hM hβ (express z.1.1 z.1.2 v) := rfl

instance isMarkovKernel_collapseKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    IsMarkovKernel (collapseKernel hM hβ v) :=
  ⟨fun z => by rw [collapseKernel_apply]; infer_instance⟩

/-- The first accepted mark carries `p`, and the band above it lies in `E`. -/
def collapseEvent (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) :
    Set (ℕ → Hold (MarkJump N M)) :=
  {ω | acceptedJump ω = p} ∩ restAfterAccept ⁻¹' E

theorem measurableSet_collapseEvent (p : Jump N M) {E : Set (ℕ → Hold (MarkJump N M))}
    (hE : MeasurableSet E) : MeasurableSet (collapseEvent p E) :=
  (measurable_acceptedJump (measurableSet_singleton p)).inter (measurable_restAfterAccept hE)

/-- The law of the time of the first expression, on the event that it carries `p` and is
followed by a band in `E`. -/
noncomputable def acceptLaw (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) : Measure ℝ :=
  ((markPathMeasure hM hβ v).restrict (collapseEvent p E)).map acceptedTime

instance isFiniteMeasure_acceptLaw (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (p : Jump N M) (E : Set (ℕ → Hold (MarkJump N M))) :
    IsFiniteMeasure (acceptLaw hM hβ v p E) := by
  rw [acceptLaw]
  infer_instance

/-- The time marginal of `SocialNetwork.stepLaw` on the pair `p`. -/
noncomputable def stepLawSlice (β : ℝ) (v : Pressure N M) (p : Jump N M) : Measure ℝ :=
  ((stepLaw β v).restrict (({p} : Set (Jump N M)) ×ˢ (Set.univ : Set ℝ))).map Prod.snd

theorem acceptLaw_apply (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) (p : Jump N M)
    (E : Set (ℕ → Hold (MarkJump N M))) {A : Set ℝ} (hA : MeasurableSet A) :
    acceptLaw hM hβ v p E A
      = markPathMeasure hM hβ v (collapseEvent p E ∩ acceptedTime ⁻¹' A) := by
  rw [acceptLaw, Measure.map_apply measurable_acceptedTime hA,
    Measure.restrict_apply (measurable_acceptedTime hA), Set.inter_comm]

theorem stepLawSlice_apply (β : ℝ) (v : Pressure N M) (p : Jump N M) {A : Set ℝ}
    (hA : MeasurableSet A) :
    stepLawSlice β v p A = stepLaw β v (({p} : Set (Jump N M)) ×ˢ A) := by
  rw [stepLawSlice, Measure.map_apply measurable_snd hA,
    Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext z
  simp [and_comm]

/-- **The time of the first expression is exponential of rate `q(v)`.**  The two finite
measures agree on every `Iic t` by `SocialNetwork.measure_collapse_Iic`, hence everywhere. -/
theorem acceptLaw_eq (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) (p : Jump N M)
    {E : Set (ℕ → Hold (MarkJump N M))} (hE : MeasurableSet E) :
    acceptLaw hM hβ v p E
      = markPathMeasure hM hβ (express p.1 p.2 v) E • stepLawSlice β v p := by
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [acceptLaw_apply hM hβ v p E measurableSet_Iic, Measure.smul_apply, smul_eq_mul,
    stepLawSlice_apply β v p measurableSet_Iic]
  exact measure_collapse_Iic hM hβ p hE t v

theorem measure_collapseEvent (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (p : Jump N M) {E : Set (ℕ → Hold (MarkJump N M))} (hE : MeasurableSet E) {A : Set ℝ}
    (hA : MeasurableSet A) :
    markPathMeasure hM hβ v (collapseEvent p E ∩ acceptedTime ⁻¹' A)
      = markPathMeasure hM hβ (express p.1 p.2 v) E
        * stepLaw β v (({p} : Set (Jump N M)) ×ˢ A) := by
  rw [← acceptLaw_apply hM hβ v p E hA, acceptLaw_eq hM hβ v p hE, Measure.smul_apply,
    smul_eq_mul, stepLawSlice_apply β v p hA]

/-! ### One step of the process, read off the band -/

omit [NeZero N] [NeZero M] in
/-- Splitting an integral over the pairs, which are finitely many. -/
theorem setLIntegral_fst_finset (μ : Measure (Step N M)) (g : Jump N M → ℝ≥0∞)
    {S : Set (Step N M)} (hS : MeasurableSet S) :
    ∫⁻ z in S, g z.1 ∂μ
      = ∑ p : Jump N M, g p * μ (({p} : Set (Jump N M)) ×ˢ (Prod.mk p ⁻¹' S)) := by
  classical
  have hslice : ∀ p : Jump N M, S ∩ (({p} : Set (Jump N M)) ×ˢ (Set.univ : Set ℝ))
      = ({p} : Set (Jump N M)) ×ˢ (Prod.mk p ⁻¹' S) := by
    intro p
    ext z
    constructor
    · rintro ⟨hzS, hz1, -⟩
      refine ⟨hz1, ?_⟩
      show (p, z.2) ∈ S
      rw [show p = z.1 from hz1.symm]
      exact hzS
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, hz1, Set.mem_univ _⟩
      show z ∈ S
      rw [show z = (p, z.2) from by rw [show p = z.1 from hz1.symm]]
      exact hz2
  have hmeasT : ∀ p : Jump N M,
      MeasurableSet (S ∩ (({p} : Set (Jump N M)) ×ˢ (Set.univ : Set ℝ))) :=
    fun p => hS.inter ((measurableSet_singleton p).prod MeasurableSet.univ)
  have hpt : ∀ z : Step N M, S.indicator (fun z => g z.1) z
      = ∑ p : Jump N M, (S ∩ (({p} : Set (Jump N M)) ×ˢ (Set.univ : Set ℝ))).indicator
          (fun _ => g p) z := by
    intro z
    rw [Finset.sum_eq_single z.1]
    · by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz,
          Set.indicator_of_mem (show z ∈ S ∩ (({z.1} : Set (Jump N M)) ×ˢ (Set.univ : Set ℝ))
            from ⟨hz, rfl, Set.mem_univ _⟩)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz h.1)]
    · intro q _ hq
      exact Set.indicator_of_notMem (fun h => hq h.2.1.symm) _
    · intro h
      exact absurd (Finset.mem_univ z.1) h
  rw [← lintegral_indicator hS, lintegral_congr hpt,
    lintegral_finsetSum _ fun p _ => measurable_const.indicator (hmeasT p)]
  exact Finset.sum_congr rfl fun p _ => by
    rw [lintegral_indicator_const (hmeasT p), hslice p]

/-- **The first expression and the band above it, jointly.**  Both sides split over which pair
is expressed. -/
theorem measure_collapse_prod (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    {S : Set (Step N M)} (hS : MeasurableSet S) {E : Set (ℕ → Hold (MarkJump N M))}
    (hE : MeasurableSet E) :
    markPathMeasure hM hβ v (collapseStep ⁻¹' S ∩ restAfterAccept ⁻¹' E)
      = ∑ p : Jump N M, markPathMeasure hM hβ (express p.1 p.2 v) E
          * stepLaw β v (({p} : Set (Jump N M)) ×ˢ (Prod.mk p ⁻¹' S)) := by
  classical
  have hunion : collapseStep ⁻¹' S ∩ restAfterAccept ⁻¹' E
      = ⋃ p ∈ (Finset.univ : Finset (Jump N M)),
          (collapseEvent p E ∩ acceptedTime ⁻¹' (Prod.mk p ⁻¹' S)) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Finset.mem_univ,
      collapseEvent, Set.mem_ofPred_eq, exists_prop, true_and]
    constructor
    · rintro ⟨hS', hE'⟩
      exact ⟨acceptedJump ω, ⟨rfl, hE'⟩, hS'⟩
    · rintro ⟨p, ⟨hp, hE'⟩, hS'⟩
      refine ⟨?_, hE'⟩
      rw [collapseStep, hp]
      exact hS'
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Jump N M)) : Set (Jump N M))
      (fun p => collapseEvent p E ∩ acceptedTime ⁻¹' (Prod.mk p ⁻¹' S)) := by
    intro p _ q _ hpq
    show Disjoint _ _
    rw [Set.disjoint_left]
    rintro ω ⟨⟨hp, -⟩, -⟩ ⟨⟨hq, -⟩, -⟩
    exact hpq (hp ▸ hq)
  have hmeas : ∀ p ∈ (Finset.univ : Finset (Jump N M)),
      MeasurableSet (collapseEvent p E ∩ acceptedTime ⁻¹' (Prod.mk p ⁻¹' S)) :=
    fun p _ => (measurableSet_collapseEvent p hE).inter
      (measurable_acceptedTime (measurable_prodMk_left hS))
  rw [hunion, measure_biUnion_finset hdisj hmeas]
  exact Finset.sum_congr rfl fun p _ =>
    measure_collapseEvent hM hβ v p hE (measurable_prodMk_left hS)

theorem compProd_collapseKernel_prod (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    {S : Set (Step N M)} (hS : MeasurableSet S) {E : Set (ℕ → Hold (MarkJump N M))}
    (hE : MeasurableSet E) :
    ((stepLaw β v) ⊗ₘ collapseKernel hM hβ v) (S ×ˢ E)
      = ∑ p : Jump N M, markPathMeasure hM hβ (express p.1 p.2 v) E
          * stepLaw β v (({p} : Set (Jump N M)) ×ˢ (Prod.mk p ⁻¹' S)) := by
  rw [Measure.compProd_apply_prod hS hE]
  exact setLIntegral_fst_finset (stepLaw β v)
    (fun p => markPathMeasure hM hβ (express p.1 p.2 v) E) hS

/-- **[GL24]'s construction makes one step of the process.**  The pair carried by the first
accepted mark, the time it arrives, and the band above it have exactly the joint law the
jump-hold description of equation (3) prescribes: the pair and the time follow `stepLaw`, and
the band above is a fresh band started from the matrix the expression leads to, independent of
both.

Everything below the first accepted mark — the geometric number of marks that fell in the
strip and were discarded, and the exponential times between them — has been integrated away;
what is left is [GL24]'s Figure 2 read as one step. -/
theorem map_markPathMeasure_collapse (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    (markPathMeasure hM hβ v).map (fun ω => (collapseStep ω, restAfterAccept ω))
      = (stepLaw β v) ⊗ₘ collapseKernel hM hβ v := by
  have hmap : Measurable
      fun ω : ℕ → Hold (MarkJump N M) => (collapseStep ω, restAfterAccept ω) :=
    measurable_collapseStep.prodMk measurable_restAfterAccept
  have hprob : IsProbabilityMeasure
      ((markPathMeasure hM hβ v).map fun ω => (collapseStep ω, restAfterAccept ω)) :=
    Measure.isProbabilityMeasure_map hmap.aemeasurable
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨S, hS, E, hE, rfl⟩
    have hS' : MeasurableSet S := hS
    have hE' : MeasurableSet E := hE
    rw [Measure.map_apply hmap (hS'.prod hE')]
    have hpre : (fun ω : ℕ → Hold (MarkJump N M) =>
        (collapseStep ω, restAfterAccept ω)) ⁻¹' (S ×ˢ E)
        = collapseStep ⁻¹' S ∩ restAfterAccept ⁻¹' E := rfl
    rw [hpre, measure_collapse_prod hM hβ v hS' hE',
      compProd_collapseKernel_prod hM hβ v hS' hE']
  · rw [measure_univ, measure_univ]

/-! ### The jump-hold process is a driven chain -/

/-- One expression moves the matrix by `express`. -/
def jumpNext (v : Pressure N M) (p : Jump N M) : Pressure N M := express p.1 p.2 v

omit [NeZero N] [NeZero M] in
theorem state_ofPath_eq (u : Pressure N M) (j : ℕ → Jump N M) (n : ℕ) :
    (Trajectory.ofPath j).state u n = stateAfterJumps jumpNext u j n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Trajectory.state_succ, ih]; rfl

theorem ctsDrivingKernel_eq (β : ℝ) (u : Pressure N M) (n : ℕ) :
    ctsDrivingKernel β u n = drivenKernel jumpNext (stepLaw β) u n := by
  ext h : 1
  rw [ctsDrivingKernel_apply, drivenKernel_apply]
  congr 1
  exact state_ofPath_eq u _ (n + 1)

/-- The continuous-time path measure is the chain of `SocialNetwork.JumpHold` driven by
`express`.  This is a matter of unfolding: both are the Ionescu-Tulcea measure of the same
kernels. -/
theorem ctsPathMeasure_eq_drivenMeasure (β : ℝ) (u : Pressure N M) :
    ctsPathMeasure β u = drivenMeasure jumpNext (stepLaw β) u := by
  have hker : ctsDrivingKernel β u = drivenKernel jumpNext (stepLaw β) u :=
    funext (ctsDrivingKernel_eq β u)
  rw [ctsPathMeasure]
  simp only [hker]
  rfl

/-! ### Collapsing the whole band -/

/-- The realisation of the process that [GL24]'s band carries: the `n`-th step is the first
accepted mark of the band that is left after the first `n` expressions have been read off. -/
noncomputable def collapse (ω : ℕ → Hold (MarkJump N M)) : ℕ → Step N M :=
  fun n => collapseStep (restAfterAccept^[n] ω)

theorem collapse_zero (ω : ℕ → Hold (MarkJump N M)) : collapse ω 0 = collapseStep ω := rfl

theorem collapse_succ (ω : ℕ → Hold (MarkJump N M)) (n : ℕ) :
    collapse ω (n + 1) = collapse (restAfterAccept ω) n := by
  rw [collapse, collapse, Function.iterate_succ_apply]

theorem measurable_collapse : Measurable (collapse (N := N) (M := M)) :=
  measurable_pi_lambda _ fun n =>
    measurable_collapseStep.comp (measurable_restAfterAccept.iterate n)

theorem shiftHold_collapse (ω : ℕ → Hold (MarkJump N M)) :
    shiftHold (collapse ω) = collapse (restAfterAccept ω) := by
  funext n
  show collapse ω (1 + n) = collapse (restAfterAccept ω) n
  rw [Nat.add_comm, collapse_succ]

omit [NeZero N] [NeZero M] in
/-- The first `n` steps of a realisation. -/
theorem measurable_takeStep (n : ℕ) :
    Measurable fun ω : ℕ → Step N M => (fun i : Fin n => ω i) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Prefixing a step to the first `n` steps of a realisation. -/
def consStep {n : ℕ} (z : Step N M) (h : Fin n → Step N M) : Fin (n + 1) → Step N M :=
  fun i => if hi : (i : ℕ) = 0 then z else h ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

omit [NeZero N] [NeZero M] in
theorem measurable_consStep (n : ℕ) :
    Measurable fun q : Step N M × (Fin n → Step N M) => consStep q.1 q.2 := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : (i : ℕ) = 0
  · simp only [consStep, dif_pos hi]
    exact measurable_fst
  · simp only [consStep, dif_neg hi]
    exact (measurable_pi_apply _).comp measurable_snd

omit [NeZero N] [NeZero M] in
theorem takeStep_succ (n : ℕ) (ω : ℕ → Step N M) :
    (fun i : Fin (n + 1) => ω i) = consStep (ω 0) (fun i : Fin n => shiftHold ω i) := by
  funext i
  by_cases hi : (i : ℕ) = 0
  · simp only [consStep, dif_pos hi]
    rw [hi]
  · simp only [consStep, dif_neg hi]
    show ω (i : ℕ) = ω (1 + ((i : ℕ) - 1))
    congr 1
    omega

/-- **[GL24]'s construction is the process.**  The finite-dimensional laws of the realisation
carried by the band are those of the jump-hold process: the induction peels off one expression
at a time, using `SocialNetwork.map_markPathMeasure_collapse` on the band and the restart
lemma on the process. -/
theorem map_takeStep_collapse (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v : Pressure N M) :
    (markPathMeasure hM hβ v).map (fun ω => (fun i : Fin n => collapse ω i))
      = (ctsPathMeasure β v).map (fun ω : ℕ → Step N M => (fun i : Fin n => ω i)) := by
  induction n generalizing v with
  | zero =>
      have h1 : IsProbabilityMeasure ((markPathMeasure hM hβ v).map
          (fun ω => (fun i : Fin 0 => collapse ω i))) :=
        Measure.isProbabilityMeasure_map
          ((measurable_takeStep 0).comp measurable_collapse).aemeasurable
      have h2 : IsProbabilityMeasure ((ctsPathMeasure β v).map
          (fun ω : ℕ → Step N M => (fun i : Fin 0 => ω i))) :=
        Measure.isProbabilityMeasure_map (measurable_takeStep 0).aemeasurable
      refine Measure.ext fun s _ => ?_
      rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
      · simp
      · rw [show s = Set.univ from Set.eq_univ_of_forall fun y => by
          rwa [show y = x from Subsingleton.elim y x], measure_univ, measure_univ]
  | succ n ih =>
      have hmapL : Measurable fun ω : ℕ → Hold (MarkJump N M) =>
          (fun i : Fin (n + 1) => collapse ω i) :=
        (measurable_takeStep (n + 1)).comp measurable_collapse
      have hpairL : Measurable fun ω : ℕ → Hold (MarkJump N M) =>
          (collapseStep ω, restAfterAccept ω) :=
        measurable_collapseStep.prodMk measurable_restAfterAccept
      have hpairR : Measurable fun ω : ℕ → Step N M => (ω 0, shiftHold ω) :=
        (measurable_pi_apply 0).prodMk measurable_shiftHold
      refine Measure.ext fun T hT => ?_
      have hconsL : Measurable fun q : Step N M × (ℕ → Hold (MarkJump N M)) =>
          consStep q.1 (fun i : Fin n => collapse q.2 i) :=
        (measurable_consStep n).comp
          (measurable_fst.prodMk (((measurable_takeStep n).comp measurable_collapse).comp
            measurable_snd))
      have hconsR : Measurable fun q : Step N M × (ℕ → Step N M) =>
          consStep q.1 (fun i : Fin n => q.2 i) :=
        (measurable_consStep n).comp
          (measurable_fst.prodMk ((measurable_takeStep n).comp measurable_snd))
      have hL : (fun ω : ℕ → Hold (MarkJump N M) => (fun i : Fin (n + 1) => collapse ω i)) ⁻¹' T
          = (fun ω => (collapseStep ω, restAfterAccept ω)) ⁻¹'
              ((fun q : Step N M × (ℕ → Hold (MarkJump N M)) =>
                consStep q.1 (fun i : Fin n => collapse q.2 i)) ⁻¹' T) := by
        ext ω
        simp only [Set.mem_preimage]
        rw [takeStep_succ n (collapse ω), shiftHold_collapse]
        rfl
      have hR : (fun ω : ℕ → Step N M => (fun i : Fin (n + 1) => ω i)) ⁻¹' T
          = (fun ω : ℕ → Step N M => (ω 0, shiftHold ω)) ⁻¹'
              ((fun q : Step N M × (ℕ → Step N M) =>
                consStep q.1 (fun i : Fin n => q.2 i)) ⁻¹' T) := by
        ext ω
        simp only [Set.mem_preimage]
        rw [takeStep_succ n ω]
      rw [Measure.map_apply hmapL hT, Measure.map_apply (measurable_takeStep (n + 1)) hT,
        hL, hR, ← Measure.map_apply hpairL (hconsL hT),
        ← Measure.map_apply hpairR (hconsR hT), map_markPathMeasure_collapse,
        ctsPathMeasure_eq_drivenMeasure, map_drivenMeasure_firstRest,
        Measure.compProd_apply (hconsL hT), Measure.compProd_apply (hconsR hT)]
      refine lintegral_congr fun z => ?_
      have hsec : MeasurableSet {h : Fin n → Step N M | consStep z h ∈ T} :=
        (measurable_consStep n).comp (measurable_const.prodMk measurable_id) hT
      have hpreL : Prod.mk z ⁻¹' ((fun q : Step N M × (ℕ → Hold (MarkJump N M)) =>
            consStep q.1 (fun i : Fin n => collapse q.2 i)) ⁻¹' T)
          = (fun ω : ℕ → Hold (MarkJump N M) => (fun i : Fin n => collapse ω i)) ⁻¹'
              {h : Fin n → Step N M | consStep z h ∈ T} := rfl
      have hpreR : Prod.mk z ⁻¹' ((fun q : Step N M × (ℕ → Step N M) =>
            consStep q.1 (fun i : Fin n => q.2 i)) ⁻¹' T)
          = (fun ω : ℕ → Step N M => (fun i : Fin n => ω i)) ⁻¹'
              {h : Fin n → Step N M | consStep z h ∈ T} := rfl
      have hmL : Measurable fun ω : ℕ → Hold (MarkJump N M) =>
          (fun i : Fin n => collapse ω i) :=
        (measurable_takeStep n).comp measurable_collapse
      rw [hpreL, hpreR, collapseKernel_apply, restartKernel_apply,
        ← Measure.map_apply hmL hsec,
        ← Measure.map_apply (measurable_takeStep n) hsec,
        ← ctsPathMeasure_eq_drivenMeasure]
      exact congrFun (congrArg _ (ih (express z.1.1 z.1.2 v))) _

/-- **[GL24]'s construction is the process, in law.**  The realisation carried by the band of
Figure 2 has exactly the law of the jump-hold process of equation (3).

This is the identification the paper and [GL24] both assert and neither proves: [GL24] writes
"we will construct the process `(U_t)` with jump times `{T_n}` as the superposition …", and it
is what makes the non-explosion proved on the band a statement about the process.  The
argument itself is [GL24]'s, step for step; only the plumbing of the sample space is ours. -/
theorem map_markPathMeasure_collapse_eq (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    (markPathMeasure hM hβ v).map collapse = ctsPathMeasure β v := by
  have hprob : IsProbabilityMeasure ((markPathMeasure hM hβ v).map collapse) :=
    Measure.isProbabilityMeasure_map measurable_collapse.aemeasurable
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ (by rw [measure_univ, measure_univ])
  rintro t ht
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  have hlt : ∀ i ∈ s, i < s.sup id + 1 := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  set n := s.sup id + 1 with hn
  set φ : (Fin n → Step N M) → ((i : s) → Step N M) :=
    fun g j => g ⟨(j : ℕ), hlt j j.2⟩ with hφ
  have hφm : Measurable φ := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hcyl : cylinder s S
      = (fun ω : ℕ → Step N M => (fun i : Fin n => ω i)) ⁻¹' (φ ⁻¹' S) := rfl
  have hmL : Measurable fun ω : ℕ → Hold (MarkJump N M) =>
      (fun i : Fin n => collapse ω i) :=
    (measurable_takeStep n).comp measurable_collapse
  have hLHS : ((markPathMeasure hM hβ v).map collapse) (cylinder s S)
      = ((markPathMeasure hM hβ v).map fun ω => (fun i : Fin n => collapse ω i))
          (φ ⁻¹' S) := by
    rw [hcyl, Measure.map_apply measurable_collapse ((measurable_takeStep n) (hφm hS)),
      Measure.map_apply hmL (hφm hS)]
    rfl
  have hRHS : (ctsPathMeasure β v) (cylinder s S)
      = ((ctsPathMeasure β v).map fun ω : ℕ → Step N M => (fun i : Fin n => ω i))
          (φ ⁻¹' S) := by
    rw [hcyl, Measure.map_apply (measurable_takeStep n) (hφm hS)]
  rw [hLHS, hRHS, map_takeStep_collapse hM hβ n v]

/-! ### Non-explosion, read off the band -/

theorem holdSum_add {J : Type*} [MeasurableSpace J] [DiscreteMeasurableSpace J] [Countable J]
    [DecidableEq J] (k m : ℕ) (ω : ℕ → Hold J) :
    holdSum (k + m) ω = holdSum k ω + holdSum m (shiftHold^[k] ω) := by
  rw [holdSum, holdSum, holdSum, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show (ω (k + i)).2 = (shiftHold^[k] ω i).2
  rw [shiftHold_iterate]

theorem holdSum_mono_of_nonneg {J : Type*} [MeasurableSpace J] [DiscreteMeasurableSpace J]
    [Countable J] [DecidableEq J] {ω : ℕ → Hold J} (h : ∀ n, 0 ≤ (ω n).2) {k m : ℕ}
    (hkm : k ≤ m) : holdSum k ω ≤ holdSum m ω := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [holdSum_add]
  have hd : 0 ≤ holdSum d (shiftHold^[k] ω) := by
    refine Finset.sum_nonneg fun i _ => ?_
    show 0 ≤ (shiftHold^[k] ω i).2
    rw [shiftHold_iterate]
    exact h (k + i)
  linarith

/-- The `n`-th expression of the collapsed realisation is one of the marks of the band, and it
is at least the `n`-th of them: reading `n` expressions consumes at least `n` marks. -/
theorem exists_holdSum_collapse (n : ℕ) (ω : ℕ → Hold (MarkJump N M)) :
    ∃ m, n ≤ m ∧ holdSum n (collapse ω) = holdSum m ω := by
  induction n generalizing ω with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      obtain ⟨m, hm, hEq⟩ := ih (restAfterAccept ω)
      refine ⟨firstAccept ω + 1 + m, by omega, ?_⟩
      rw [holdSum_succ_shiftHold n (collapse ω), shiftHold_collapse, hEq, holdSum_add]
      rfl

theorem holdBlowUp_collapse {ω : ℕ → Hold (MarkJump N M)} (hnn : ∀ n, 0 ≤ (ω n).2)
    (h : holdBlowUp ω = ⊤) : holdBlowUp (collapse ω) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← h]
  refine iSup_le fun n => ?_
  obtain ⟨m, hm, hEq⟩ := exists_holdSum_collapse n ω
  calc ENNReal.ofReal (holdSum n ω)
      ≤ ENNReal.ofReal (holdSum n (collapse ω)) := by
        rw [hEq]
        exact ENNReal.ofReal_le_ofReal (holdSum_mono_of_nonneg hnn hm)
    _ ≤ holdBlowUp (collapse ω) :=
        le_iSup (fun k => ENNReal.ofReal (holdSum k (collapse ω))) n

theorem measurable_holdBlowUp {J : Type*} [MeasurableSpace J] [DiscreteMeasurableSpace J]
    [Countable J] [DecidableEq J] : Measurable (holdBlowUp (J := J)) :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_holdSum n)

/-- **Theorem 1.1, by [GL24]'s construction.**  For any `β ≥ 0` and any starting matrix
`u ∈ S`, the jump times satisfy `P (sup {Tₘ : m ≥ 1} = ∞) = 1`: the process does not explode.

The argument is [GL24]'s, pp. 12-14, step for step.  Lemma 10 gives one expression from an
actor carrying pressure below `N` in every `N`, and those expressions carry total rate at most
`λ = NMe^{βN}` whatever the rest of the matrix does; so they are a sub-family of the marks of
a Poisson process of rate `λ`, which do not accumulate
(`SocialNetwork.measure_markPathMeasure_blowUp`).  What this file adds is the identification
[GL24] asserts: the realisation carried by the band *is* the process
(`SocialNetwork.map_markPathMeasure_collapse_eq`).  The collapsed jump times are a subsequence
of the band's, so they are at least as large, and they are unbounded with it. -/
theorem nonExplosion_ofGraphical (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) :
    ctsPathMeasure β u {ω | explosionTime ω = ⊤} = 1 := by
  set A : Set (ℕ → Hold (MarkJump N M)) := {ω | ∀ n, 0 ≤ (ω n).2} with hAdef
  set B : Set (ℕ → Hold (MarkJump N M)) := {ω | holdBlowUp ω = ⊤} with hBdef
  have hAnull : markPathMeasure hM hβ u Aᶜ = 0 := by
    have hcover : Aᶜ ⊆ ⋃ n : ℕ, {ω : ℕ → Hold (MarkJump N M) | (ω n).2 < 0} := by
      intro ω hω
      simp only [hAdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨n, hn⟩ := hω
      exact Set.mem_iUnion.2 ⟨n, hn⟩
    refine le_antisymm ((measure_mono hcover).trans ?_) (zero_le)
    exact le_of_eq (measure_iUnion_null fun n => markPathMeasure_holdTime_nonneg hM hβ u n)
  have hBmeas : MeasurableSet B := measurable_holdBlowUp (measurableSet_singleton ⊤)
  have hBnull : markPathMeasure hM hβ u Bᶜ = 0 := by
    rw [prob_compl_eq_one_sub hBmeas, measure_markPathMeasure_blowUp hM hβ hu, tsub_self]
  have hmass : (1 : ℝ≥0∞) ≤ markPathMeasure hM hβ u (A ∩ B) := by
    have hle : markPathMeasure hM hβ u Set.univ
        ≤ markPathMeasure hM hβ u (A ∩ B) + markPathMeasure hM hβ u (A ∩ B)ᶜ := by
      rw [← Set.union_compl_self (A ∩ B)] at *
      exact measure_union_le _ _
    have hnull : markPathMeasure hM hβ u (A ∩ B)ᶜ = 0 := by
      rw [Set.compl_inter]
      refine le_antisymm ((measure_union_le _ _).trans ?_) (zero_le)
      rw [hAnull, hBnull, add_zero]
    rw [measure_univ, hnull, add_zero] at hle
    exact hle
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) ≤ markPathMeasure hM hβ u (A ∩ B) := hmass
    _ ≤ markPathMeasure hM hβ u (collapse ⁻¹' {ω : ℕ → Step N M | explosionTime ω = ⊤}) := by
        refine measure_mono fun ω hω => ?_
        exact holdBlowUp_collapse hω.1 hω.2
    _ ≤ ((markPathMeasure hM hβ u).map collapse) {ω : ℕ → Step N M | explosionTime ω = ⊤} :=
        Measure.le_map_apply measurable_collapse.aemeasurable _
    _ = ctsPathMeasure β u {ω : ℕ → Step N M | explosionTime ω = ⊤} := by
        rw [map_markPathMeasure_collapse_eq]

end SocialNetwork
