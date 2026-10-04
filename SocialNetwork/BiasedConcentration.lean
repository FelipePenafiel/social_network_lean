/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Appendix
import SocialNetwork.BiasedConsensusExit
import SocialNetwork.Kac

/-!
# Proposition 26: the biased skeleton off the biased steep ladders

Appendix C of arXiv:2607.19651 states Proposition 26 and says that its proof "follows exactly
as the proofs of Proposition 9, taking into account Remark 8 and recalling that `0 ∉ S^α`".
The proof of Proposition 9 (`SocialNetwork.measure_le_of_notMem_steepLadderSet`) has three
ingredients, and this file transposes each:

1. Kac's inequality, `SocialNetwork.kac_tsum_le`, which is stated for any Markov kernel on a
   countable space and so applies to the biased skeleton as it stands.  What has to be
   transposed is the bridge from its avoidance probabilities to the law of a realisation,
   `SocialNetwork.Bias.lintegral_kacAvoid_biasedSkeletonKernel`.
2. A run that leaves `u` and does not come back: a near-greedy run to `L_α` (Proposition 23,
   with the probability of Proposition 24), then expressions made from positive entries, which
   keep the process on `L̂_α` with probability at least `η` each (Remark 5, which Appendix C
   transposes in a paragraph).
3. The arithmetic: `∑_m η^m = 1/(1-η)` and `1 - η ≤ (1 + MN) e^{-β(N-1)}`.

## What the transposition supplies

That the run to `L_α` does not visit `u` is, as in Proposition 9, not part of Proposition 23,
which says where the run ends and nothing about where it passes.  It is proved as
`SocialNetwork.skeleton_ne_of_greedy` proves it: a run that came back to `u` could be repeated
for ever, the repeated run would be near-greedy at every step, hence on `L̂_α` at a multiple of
its period, where it sits at `u`.  What keeps the repeated run on `L̂_α` is that a near-greedy
expression there expresses the supported opinion: a steep ladder has an entry at least `1`, the
slack is `γ/2 < 1`, and every other opinion carries non-positive pressure.

Remark 8 and `0 ∉ S^α`, which the paper names, are not used by this proof.  They are what
Theorem 27.1 needs on top of it: Remark 8 bounds the jump rate below, and `0 ∉ S^α` removes the
zero matrix, for which the unbiased model needs Corollary 10.

## The constant

The paper's `C̃` depends on `M`, `N` and `α` and is not given.  Here it is `(1 + MN)^{K+1}`,
with `K` the horizon of Proposition 23: the run to `L_α` costs `ζ_{α,β}^{-K} ≤ (1 + MN)^K`,
since `ζ_{α,β} ≥ 1/(1+MN)` for every `β ≥ 0`, and the geometric series one more factor
`1 + MN`.  Proposition 9 needs to split according to whether `ζ_β ≥ 1/2` to reach the constant
it prints; with no printed constant to reach, there is no split here.

## Main statements

* `SocialNetwork.Bias.lintegral_kacAvoid_biasedSkeletonKernel` — the avoidance probabilities of
  Kac's inequality, read on realisations of the biased skeleton.
* `SocialNetwork.Bias.eta_le_biasedJumpPMF_biasedPosFinset` — **Remark 5** for the biased model:
  from `L̂_α` the next expression is made from a positive entry with probability at least `η`.
* `SocialNetwork.Bias.IsBiasedSteepLadder.opinion_eq_of_mem_nearArgmaxFinset` — a near-greedy
  expression on `L̂_α^o` expresses `o`.
* `SocialNetwork.Bias.stateAfter_ne_of_nearGreedy` — the near-greedy run to `L_α` does not visit
  a profile off `L̂_α`.
* `SocialNetwork.Bias.biasedReturnBound_prod_le` — the lower bound on the return time to `u`.
* `SocialNetwork.Bias.biasedMeasure_le_of_notMem_steepLadder` — **Proposition 26**, resting on
  Proposition 23.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The avoidance probabilities of Kac's lemma, read on realisations

`SocialNetwork.kacAvoid` is a recursion on the transition kernel; the lower bound of
Proposition 26 is a statement about realisations.  As for the unbiased skeleton
(`SocialNetwork.kacAvoid_skeletonKernel`), the two are identified by the Markov property at
time `1`, iterated. -/

section Avoid

variable [NeZero N] [NeZero M]

/-- The event that the biased skeleton started at `v` misses the profile `u` at each of the
times `0, 1, …, m-1`.  At `k = 0` this is the condition `v ≠ u`. -/
def biasedAvoidSet (v u : Profile N M) (m : ℕ) : Set (ℕ → Jump N M) :=
  {ω | ∀ k < m, stateAfter v ω k ≠ u}

omit [NeZero N] [NeZero M] in
theorem measurableSet_biasedAvoidSet (v u : Profile N M) (m : ℕ) :
    MeasurableSet (biasedAvoidSet v u m) := by
  have h : biasedAvoidSet v u m
      = ⋂ k ∈ (Finset.range m : Finset ℕ), (fun ω => stateAfter v ω k) ⁻¹' {u}ᶜ := by
    ext ω
    simp [biasedAvoidSet]
  rw [h]
  exact MeasurableSet.biInter (Finset.range m).countable_toSet fun k _ =>
    (measurable_stateAfter v k) (measurableSet_profile _)

/-- **The first expressed pair decomposes the event.**  Avoiding `u` at each of the times
`1, …, m` is, conditionally on the first expressed pair, avoiding `u` at each of the times
`0, …, m-1` from the profile that pair reaches.  This is the Markov property at time `1`. -/
theorem lintegral_biasedPathMeasure_avoidSet (γ β : ℝ) (v u : Profile N M) (m : ℕ) :
    ∫⁻ w, biasedPathMeasure γ β w (biasedAvoidSet w u m) ∂(biasedSkeletonKernel γ β v)
      = biasedPathMeasure γ β v {ω : ℕ → Jump N M | ∀ k < m, stateAfter v ω (k + 1) ≠ u} := by
  rw [lintegral_biasedSkeletonKernel]
  have hunion : {ω : ℕ → Jump N M | ∀ k < m, stateAfter v ω (k + 1) ≠ u}
      = ⋃ z ∈ (Finset.univ : Finset (Jump N M)),
          ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
            ∩ shiftPath 1 ⁻¹' biasedAvoidSet (Profile.express z.1 z.2 v) u m) := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, Set.mem_inter_iff,
      Set.mem_preimage, biasedAvoidSet, Set.mem_ofPred_eq]
    constructor
    · intro hω
      refine ⟨ω 0, fun k hk => by rw [Nat.lt_one_iff.1 hk], fun j hj => ?_⟩
      have hk := hω j hj
      rwa [show j + 1 = 1 + j by omega, stateAfter_add, stateAfter_succ, stateAfter_zero] at hk
    · rintro ⟨z, hz0, hz1⟩ k hk
      rw [show k + 1 = 1 + k by omega, stateAfter_add, stateAfter_succ, stateAfter_zero,
        hz0 0 (by omega)]
      exact hz1 k hk
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Jump N M)))
      fun z : Jump N M => ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
        ∩ shiftPath 1 ⁻¹' biasedAvoidSet (Profile.express z.1 z.2 v) u m) := by
    intro z _ z' _ hne
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    rw [← hω.1 0 (by omega), ← hω'.1 0 (by omega)]
  have hmeas : ∀ z ∈ (Finset.univ : Finset (Jump N M)),
      MeasurableSet ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
        ∩ shiftPath 1 ⁻¹' biasedAvoidSet (Profile.express z.1 z.2 v) u m) := fun z _ =>
    (measurableSet_cylinderPath (fun _ => z) 1).inter
      (measurable_shiftPath 1 (measurableSet_biasedAvoidSet _ _ _))
  rw [hunion, measure_biUnion_finset hdisj hmeas]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hstep := pathMeasure_restart (γ := γ) (β := β) v (fun _ => z) 1
    (measurableSet_biasedAvoidSet (Profile.express z.1 z.2 v) u m)
  have hone : stateAfter v (fun _ => z) 1 = Profile.express z.1 z.2 v := by
    rw [stateAfter_succ, stateAfter_zero]
  have hcyl : biasedPathMeasure γ β v {ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
      = biasedJumpPMF γ β v z := by
    have h := pathMeasure_cylinder (γ := γ) (β := β) (u := v) (fun _ => z) 1
    simpa using h
  rw [hstep, hone, hcyl]

/-- **The bridge.**  The avoidance probability that Kac's inequality is stated with is the
probability, under the law of the biased skeleton started at `v`, that the skeleton misses `u`
throughout the first `m` times. -/
theorem kacAvoid_biasedSkeletonKernel (γ β : ℝ) (u : Profile N M) :
    ∀ (m : ℕ) (v : Profile N M),
      kacAvoid (biasedSkeletonKernel γ β) u m v
        = biasedPathMeasure γ β v (biasedAvoidSet v u m) := by
  intro m
  induction m with
  | zero =>
      intro v
      have huniv : biasedAvoidSet v u 0 = Set.univ := by
        ext ω
        simp [biasedAvoidSet]
      rw [huniv, kacAvoid_zero, measure_univ]
  | succ m ih =>
      intro v
      by_cases hv : v = u
      · subst hv
        have hempty : biasedAvoidSet v v (m + 1) = ∅ := by
          ext ω
          simp only [biasedAvoidSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            not_forall]
          exact ⟨0, by omega, by simp⟩
        rw [hempty, measure_empty, kacAvoid_succ, Set.indicator_of_notMem (by simp)]
      · rw [kacAvoid_succ_of_ne _ hv, lintegral_congr fun w => ih w,
          lintegral_biasedPathMeasure_avoidSet]
        congr 1
        ext ω
        simp only [biasedAvoidSet, Set.mem_ofPred_eq]
        constructor
        · intro h k hk
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · simpa using hv
          · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            exact h j (by omega)
        · intro h k hk
          exact h (k + 1) (by omega)

/-- The quantity Kac's inequality sums, read on realisations: the probability that the biased
skeleton started at `u` does not come back to `u` within `m` steps. -/
theorem lintegral_kacAvoid_biasedSkeletonKernel (γ β : ℝ) (u : Profile N M) (m : ℕ) :
    ∫⁻ w, kacAvoid (biasedSkeletonKernel γ β) u m w ∂(biasedSkeletonKernel γ β u)
      = biasedPathMeasure γ β u {ω : ℕ → Jump N M | ∀ k < m, stateAfter u ω (k + 1) ≠ u} := by
  rw [lintegral_congr fun w => kacAvoid_biasedSkeletonKernel γ β u m w,
    lintegral_biasedPathMeasure_avoidSet]

end Avoid

/-! ### Remark 5 for the biased model

Appendix C transposes Remark 5 in one paragraph: `L_α ⊆ L̂_α`
(`SocialNetwork.Bias.biasedLadderSet_subset_biasedSteepLadderSet`), an expression from a
positive entry keeps `L̂_α`, and from `L̂_α` such an expression has probability at least the `η`
of the unbiased model.  On `L̂_α^o` the positive entries are the entries `u (a, o) ≥ 1`, since
every other opinion carries `-γ u (a, o) ≤ 0`; so an expression from a positive entry expresses
`o`, and `SocialNetwork.Bias.IsBiasedSteepLadder.express_self` keeps `L̂_α^o`. -/

section Remark5

variable {γ β : ℝ} {o : Opinion M}

/-- `Y⁺_α (P)`, the pairs carrying strictly positive social pressure at the profile `P`: the
pairs whose expression Remark 5 keeps on `L̂_α`. -/
noncomputable def biasedPosFinset (γ : ℝ) (P : Profile N M) : Finset (Jump N M) :=
  Finset.univ.filter fun p => 0 < P.pressure γ p.1 p.2

theorem mem_biasedPosFinset {P : Profile N M} {p : Jump N M} :
    p ∈ biasedPosFinset γ P ↔ 0 < P.pressure γ p.1 p.2 := by simp [biasedPosFinset]

/-- On `L̂_α^o` a pair carrying positive pressure expresses `o`. -/
theorem IsBiasedSteepLadder.opinion_eq_of_pos (hγ : 0 < γ) {v : Profile N M}
    (hv : IsBiasedSteepLadder γ o v) {a : Actor N} {p : Opinion M}
    (h : 0 < v.pressure γ a p) : p = o := by
  by_contra hp
  exact absurd (hv.nonpos hγ a hp) (not_le.2 h)

/-- **Remark 5 along a run.**  While every expression made from a profile of `L̂_α^o` expresses
`o`, a run that is on `L̂_α^o` stays there. -/
theorem isBiasedSteepLadder_stateAfter {u : Profile N M} {ω : ℕ → Jump N M} {m : ℕ}
    (hl : IsBiasedSteepLadder γ o (stateAfter u ω m)) (n : ℕ)
    (hstep : ∀ j, m ≤ j → j < m + n → IsBiasedSteepLadder γ o (stateAfter u ω j) →
      (ω j).2 = o) :
    IsBiasedSteepLadder γ o (stateAfter u ω (m + n)) := by
  induction n with
  | zero => simpa using hl
  | succ n ih =>
      have hcur : IsBiasedSteepLadder γ o (stateAfter u ω (m + n)) :=
        ih fun j hj hj' => hstep j hj (by omega)
      rw [show m + (n + 1) = m + n + 1 by omega, stateAfter_succ,
        hstep (m + n) (by omega) (by omega) hcur]
      exact hcur.express_self _

/-- On `L̂_α` the pairs carrying positive pressure have total rate at least
`∑_{j=1}^{N-1} e^{βj}`.

The comparison of Remark 5, transposed: the `o`-column of `L̂_α^o` is `N` pairwise distinct
non-negative integers, one of them `0`, so the `N-1` positive ones dominate `1, …, N-1` once
sorted; this is `SocialNetwork.sum_Ico_exp_le_sum_jumpRate` with the rate `e^{β u (a, o)}` of
equation (7) in place of `e^{β u (a, o)/(M-1)}`.

**Supplies a step the paper asserts**: Appendix C writes the bound down for `L̂_α` with a
"similarly" pointing back to Remark 5, which does not argue it either. -/
theorem IsBiasedSteepLadder.sum_Ico_exp_le (hγ : 0 < γ) (hβ : 0 ≤ β) {l : Profile N M}
    (hl : IsBiasedSteepLadder γ o l) :
    ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))
      ≤ ∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2 := by
  -- the `o`-column, as natural numbers
  have hexists : ∀ a : Actor N, ∃ k : ℕ, l.pressure γ a o = (k : ℝ) := by
    intro a
    obtain ⟨k, hk⟩ := hl.isInt a
    have h0 : (0 : ℝ) ≤ (k : ℝ) := hk ▸ hl.nonneg a
    have hk0 : 0 ≤ k := by exact_mod_cast h0
    refine ⟨k.toNat, ?_⟩
    rw [hk]
    exact_mod_cast (Int.toNat_of_nonneg hk0).symm
  choose c hc using hexists
  have hcinj : Function.Injective c := fun a b hab =>
    hl.injective (show l.pressure γ a o = l.pressure γ b o by rw [hc a, hc b, hab])
  have hrate : ∀ a : Actor N, biasedJumpRate γ β l a o = Real.exp (β * (c a : ℝ)) := by
    intro a
    unfold biasedJumpRate
    rw [hc a]
  -- the positive pairs are the actors off the bottom of the `o`-column
  obtain ⟨a₀, ha₀⟩ := hl.exists_zero
  have hpaeq : (Finset.univ.filter fun a : Actor N => 0 < l.pressure γ a o)
      = Finset.univ.erase a₀ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro hpos hcon
      rw [hcon, ha₀] at hpos
      exact lt_irrefl 0 hpos
    · intro hne
      rcases lt_or_eq_of_le (hl.nonneg a) with hlt | heq
      · exact hlt
      · exact absurd (hl.injective
          (show l.pressure γ a o = l.pressure γ a₀ o by rw [← heq, ha₀])) hne
  have hcard : (Finset.univ.filter fun a : Actor N => 0 < l.pressure γ a o).card = N - 1 := by
    rw [hpaeq, Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ,
      Fintype.card_fin]
  -- rewrite the sum over pairs as a sum over those actors
  have hposF : biasedPosFinset γ l
      = (Finset.univ.filter fun a : Actor N => 0 < l.pressure γ a o).image
          (fun a => (a, o)) := by
    ext p
    simp only [mem_biasedPosFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hp
      have h2 : p.2 = o := hl.opinion_eq_of_pos hγ hp
      exact ⟨p.1, by rw [← h2]; exact hp, by rw [← h2]⟩
    · rintro ⟨a, hapos, rfl⟩
      exact hapos
  have hstep : ∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2
      = ∑ a ∈ Finset.univ.filter (fun a : Actor N => 0 < l.pressure γ a o),
          Real.exp (β * (c a : ℝ)) := by
    rw [hposF, Finset.sum_image fun a _ b _ hab => by simpa using hab]
    exact Finset.sum_congr rfl fun a _ => hrate a
  -- the values `c a` are pairwise distinct naturals, all at least `1`
  have hsum : ∑ a ∈ Finset.univ.filter (fun a : Actor N => 0 < l.pressure γ a o),
        Real.exp (β * (c a : ℝ))
      = ∑ x ∈ (Finset.univ.filter fun a : Actor N => 0 < l.pressure γ a o).image c,
        Real.exp (β * (x : ℝ)) := by
    rw [Finset.sum_image fun a _ b _ hab => hcinj hab]
  have hcardimg :
      ((Finset.univ.filter fun a : Actor N => 0 < l.pressure γ a o).image c).card = N - 1 := by
    rw [Finset.card_image_of_injective _ hcinj, hcard]
  have hge1 : ∀ x ∈ (Finset.univ.filter fun a : Actor N => 0 < l.pressure γ a o).image c,
      1 ≤ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have hapos : 0 < l.pressure γ a o := (Finset.mem_filter.1 ha).2
    rcases Nat.eq_zero_or_pos (c a) with h0 | h0
    · exfalso
      rw [hc a, h0] at hapos
      simp at hapos
    · exact h0
  have hmono : Monotone fun j : ℕ => Real.exp (β * (j : ℝ)) := fun i j hij =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hβ)
  have hkey := sum_range_add_le_sum hmono 1 _ hge1
  rw [hcardimg] at hkey
  rw [hstep, hsum, Finset.sum_Ico_eq_sum_range]
  exact hkey

/-- The pairs that carry no positive pressure have total rate at most `MN`: each has rate at
most `1`, and there are at most `MN` of them. -/
theorem sum_biasedJumpRate_compl_le (hβ : 0 ≤ β) (v : Profile N M) :
    ∑ p ∈ Finset.univ \ biasedPosFinset γ v, biasedJumpRate γ β v p.1 p.2
      ≤ ((M * N : ℕ) : ℝ) := by
  have hle : ∀ p ∈ Finset.univ \ biasedPosFinset γ v, biasedJumpRate γ β v p.1 p.2 ≤ 1 :=
    fun p hp => biasedJumpRate_le_one hβ
      (not_lt.1 fun hcon => (Finset.mem_sdiff.1 hp).2 (mem_biasedPosFinset.2 hcon))
  have hcard : (((Finset.univ \ biasedPosFinset γ v).card : ℕ) : ℝ) ≤ ((M * N : ℕ) : ℝ) := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ \ biasedPosFinset γ v))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_comm] at h
    exact_mod_cast h
  calc ∑ p ∈ Finset.univ \ biasedPosFinset γ v, biasedJumpRate γ β v p.1 p.2
      ≤ (Finset.univ \ biasedPosFinset γ v).card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hle
    _ = (((Finset.univ \ biasedPosFinset γ v).card : ℕ) : ℝ) := by simp
    _ ≤ ((M * N : ℕ) : ℝ) := hcard

variable [NeZero N] [NeZero M]

/-- **Remark 5 for the biased model**, the bound `η`: from `L̂_α` the next expression is made
from a positive entry with probability at least `η`, the constant of the unbiased model.

**Follows the paper**, which transposes the bound from Remark 5 unchanged; the comparison it
rests on is `SocialNetwork.Bias.IsBiasedSteepLadder.sum_Ico_exp_le`. -/
theorem eta_le_biasedJumpPMF_biasedPosFinset (hN : 2 ≤ N) (hγ : 0 < γ) (hβ : 0 ≤ β)
    {l : Profile N M} (hl : IsBiasedSteepLadder γ o l) :
    ENNReal.ofReal (eta N M β) ≤ (biasedJumpPMF γ β l).toMeasure (biasedPosFinset γ l) := by
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β l p.1 p.2).le
  have hT0 : (0 : ℝ) ≤ ∑ p ∈ Finset.univ \ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β l p.1 p.2).le
  have hApos : 0 < ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨1, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
  have hAS := hl.sum_Ico_exp_le hγ hβ
  have hT := sum_biasedJumpRate_compl_le (γ := γ) hβ l
  have hreal : eta N M β
      ≤ (∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2)
        / ((∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2)
          + ∑ p ∈ Finset.univ \ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2) :=
    eta_le_div_of_le N M hApos hAS hT0 hT (sum_range_eq_one_add_sum_Ico (N := N) (by omega) β)
  -- transport the real inequality to the law of the expressed pair
  have hw : ∀ s : Finset (Jump N M),
      (∑ p ∈ s, biasedJumpWeight γ β l p)
        = ENNReal.ofReal (∑ p ∈ s, biasedJumpRate γ β l p.1 p.2) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (biasedJumpRate_pos γ β l p.1 p.2).le]
    rfl
  have hsplit : (∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2)
      + (∑ p ∈ Finset.univ \ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2)
      = ∑ p : Jump N M, biasedJumpRate γ β l p.1 p.2 := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ _)
  have hST : (0 : ℝ) < (∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2)
      + ∑ p ∈ Finset.univ \ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2 := by
    linarith [lt_of_lt_of_le hApos hAS]
  have htsum : (∑' q : Jump N M, biasedJumpWeight γ β l q)
      = ENNReal.ofReal ((∑ p ∈ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2)
        + ∑ p ∈ Finset.univ \ biasedPosFinset γ l, biasedJumpRate γ β l p.1 p.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp,
      hw Finset.univ, hsplit]
  rw [PMF.toMeasure_apply_finset]
  simp only [biasedJumpPMF_apply]
  rw [← Finset.sum_mul, hw (biasedPosFinset γ l), htsum, ← ENNReal.ofReal_inv_of_pos hST,
    ← ENNReal.ofReal_mul hS0, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **A near-greedy expression on `L̂_α^o` expresses `o`.**  Some actor carries at least `1`
for `o`, so the maximum is at least `1`; a near-greedy pair is within `γ/2 < 1` of it, so it
carries positive pressure, and on `L̂_α^o` only the `o`-column does. -/
theorem IsBiasedSteepLadder.opinion_eq_of_mem_nearArgmaxFinset (hN : 2 ≤ N) (hγ : 0 < γ)
    (hγ2 : γ < 2) {v : Profile N M} (hv : IsBiasedSteepLadder γ o v) {p : Jump N M}
    (hp : p ∈ nearArgmaxFinset γ v) : p.2 = o := by
  obtain ⟨a, ha⟩ := hv.exists_zero
  obtain ⟨b, hb⟩ : ∃ b : Actor N, b ≠ a := by
    have hcard : 1 < Fintype.card (Actor N) := by simp only [Fintype.card_fin]; omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  have h1 := hv.one_le ha hb
  have h2 := le_pressureSup γ v b o
  have h3 := mem_nearArgmaxFinset.1 hp
  exact hv.opinion_eq_of_pos hγ (by linarith)

end Remark5

/-! ### The run that does not come back -/

section Return

variable [NeZero N] [NeZero M] {γ β : ℝ}

/-- **The step the proof of Proposition 26 asserts**, transposed from the proof of
Proposition 9: the near-greedy run of Proposition 23 reaches `L_α` *without visiting `u`*.

**Follows the proof of `SocialNetwork.skeleton_ne_of_greedy`**, which follows Corollary 8 of
[GL24].  Suppose the run is back at `u` at step `k`.  Repeat its first `k` expressions for ever:
the near-greedy event at a step reads only the profile and the expression at that step, and
the profiles of the repeated realisation have period `k`, so the repeated realisation is
near-greedy at *every* step.  Proposition 23 puts it on `L_α` at step `K`, and a near-greedy
expression on `L̂_α^o` expresses `o`, which keeps it on `L̂_α^o` from there on — including at the
multiple `k K` of `k`, where it is at `u`.  Hence `u ∈ L̂_α`.

Stated for any horizon `K` at which the near-greedy run is on `L_α`, which is what Proposition 23
provides, so that this step is proved outright. -/
theorem stateAfter_ne_of_nearGreedy (hN : 2 ≤ N) (hγ : 0 < γ) (hγ2 : γ < 2) {K : ℕ}
    {u : Profile N M}
    (hK : nearGreedyEvents γ u K ⊆ {ω | stateAfter u ω K ∈ biasedLadderSet N M γ})
    (hu' : u ∉ biasedSteepLadderSet N M γ) {ω : ℕ → Jump N M} {k : ℕ} (hk1 : 1 ≤ k)
    (hgreedy : ∀ j < k, IsNearGreedyAt γ u ω j) :
    stateAfter u ω k ≠ u := by
  intro hreturn
  refine hu' ?_
  -- The realisation that repeats the first `k` expressions for ever.
  set ω' : ℕ → Jump N M := fun n => ω (n % k) with hω'
  have hmod : ∀ n : ℕ, (n + 1) % k = (n % k + 1) % k := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n k]
    rw [show k * (n / k) + n % k + 1 = (n % k + 1) + k * (n / k) by ring,
      Nat.add_mul_mod_self_left]
  -- Its profile at `n` is the profile of `ω` at `n % k`: the return at `k` closes the cycle.
  have hstate : ∀ n, stateAfter u ω' n = stateAfter u ω (n % k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : stateAfter u ω' (n + 1) = stateAfter u ω (n % k + 1) := by
          rw [stateAfter_succ, stateAfter_succ, ih]
        rw [hstep, hmod]
        rcases Nat.lt_or_ge (n % k + 1) k with hc | hc
        · rw [Nat.mod_eq_of_lt hc]
        · have hc' : n % k + 1 = k := by
            have := Nat.mod_lt n (show 0 < k by omega)
            omega
          rw [hc', Nat.mod_self, stateAfter_zero]
          exact hreturn
  -- The repeated realisation is near-greedy at every step, not only the first `k`.
  have hgreedy' : ∀ j, IsNearGreedyAt γ u ω' j := by
    intro j a o
    have hj := hgreedy (j % k) (Nat.mod_lt _ (by omega)) a o
    show (stateAfter u ω' j).pressure γ a o - γ / 2
      < (stateAfter u ω' j).pressure γ (ω' j).1 (ω' j).2
    rw [hstate j]
    exact hj
  -- Proposition 23 lands it on `L_α`, and near-greedy expressions keep it on `L̂_α` after.
  obtain ⟨o, hlad⟩ : stateAfter u ω' K ∈ biasedLadderSet N M γ := hK fun j _ => hgreedy' j
  have hsteep : IsBiasedSteepLadder γ o (stateAfter u ω' (K + (k * K - K))) :=
    isBiasedSteepLadder_stateAfter hlad.isBiasedSteepLadder (k * K - K) fun j _ _ hl =>
      hl.opinion_eq_of_mem_nearArgmaxFinset hN hγ hγ2
        ((isNearGreedyAt_iff_mem γ u ω' j).1 (hgreedy' j))
  -- That time is a multiple of `k`, so the profile there is `u` itself.
  have hle : K ≤ k * K := Nat.le_mul_of_pos_left K (by omega)
  rw [Nat.add_sub_cancel' hle, hstate, Nat.mul_mod_right, stateAfter_zero] at hsteep
  exact ⟨o, hsteep⟩

/-- The events the proof of Proposition 26 runs one after the other: the first `K` expressions
are near-greedy, as in Proposition 23, and every later one is made from a positive entry, as in
Remark 5. -/
noncomputable def biasedReturnStep (γ : ℝ) (K k : ℕ) (P : Profile N M) : Finset (Jump N M) :=
  if k < K then nearArgmaxFinset γ P else biasedPosFinset γ P

/-- The one-step probabilities of those events: `ζ_{α,β}` while the expressions are near-greedy,
then `η`. -/
noncomputable def biasedReturnBound (N M : ℕ) (γ β : ℝ) (K k : ℕ) : ℝ≥0∞ :=
  if k < K then ENNReal.ofReal (biasedZeta N M γ β) else ENNReal.ofReal (eta N M β)

/-- **Propositions 23 and Remark 5, composed.**  While the prescribed expressions are being
made, the biased skeleton is on `L̂_α` from time `K` on: the near-greedy run lands on
`L_α ⊆ L̂_α`, and the positive expressions keep it there.

**No counterpart in the paper**, which composes the two by restarting the chain at time `K`;
here they are composed on the realisation. -/
theorem stateAfter_mem_biasedSteepLadderSet_of_returnStep (hγ : 0 < γ) {K : ℕ}
    {u : Profile N M}
    (hK : nearGreedyEvents γ u K ⊆ {ω | stateAfter u ω K ∈ biasedLadderSet N M γ})
    {ω : ℕ → Jump N M} {k : ℕ} (hk : K ≤ k)
    (hω : ∀ j < k, ω j ∈ biasedReturnStep γ K j (stateAfter u ω j)) :
    stateAfter u ω k ∈ biasedSteepLadderSet N M γ := by
  have hgreedy : ω ∈ nearGreedyEvents γ u K := by
    intro j hj
    have hj' := hω j (by omega)
    rw [biasedReturnStep, if_pos hj] at hj'
    exact (isNearGreedyAt_iff_mem γ u ω j).2 hj'
  obtain ⟨o, hlad⟩ := hK hgreedy
  refine ⟨o, ?_⟩
  have h := isBiasedSteepLadder_stateAfter hlad.isBiasedSteepLadder (k - K)
    fun j hj hj' hl => by
      have hj'' := hω j (by omega)
      rw [biasedReturnStep, if_neg (by omega)] at hj''
      exact hl.opinion_eq_of_pos hγ (mem_biasedPosFinset.1 hj'')
  rwa [Nat.add_sub_cancel' hk] at h

/-- **The lower bound on the return time**, as Proposition 26 uses it: the probability of not
coming back to `u` within `n` steps is at least `ζ_{α,β}^K η^{n-K}`, for any horizon `K` at
which the near-greedy run is on `L_α`. -/
theorem biasedReturnBound_prod_le (hN : 2 ≤ N) (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : 0 ≤ β)
    {K : ℕ} {u : Profile N M} (hu' : u ∉ biasedSteepLadderSet N M γ)
    (hK : nearGreedyEvents γ u K ⊆ {ω | stateAfter u ω K ∈ biasedLadderSet N M γ}) (n : ℕ) :
    ∏ j ∈ Finset.range n, biasedReturnBound N M γ β K j
      ≤ biasedPathMeasure γ β u {ω : ℕ → Jump N M | ∀ k < n, stateAfter u ω (k + 1) ≠ u} := by
  have hone : IsStepBound γ β (biasedReturnStep γ K) u (biasedReturnBound N M γ β K) := by
    intro m ω hm
    by_cases hmK : m < K
    · rw [biasedReturnBound, if_pos hmK, biasedReturnStep, if_pos hmK]
      exact biasedZeta_le_biasedJumpPMF_nearArgmaxFinset hγ hβ _
    · rw [biasedReturnBound, if_neg hmK, biasedReturnStep, if_neg hmK]
      obtain ⟨o, hsteep⟩ :=
        stateAfter_mem_biasedSteepLadderSet_of_returnStep hγ hK (by omega) hm
      exact eta_le_biasedJumpPMF_biasedPosFinset hN hγ hβ hsteep
  refine le_trans (prod_le_pathMeasure_stepEvents hone n) (measure_mono ?_)
  intro ω hω k hk
  by_cases hkK : k + 1 ≤ K
  · refine stateAfter_ne_of_nearGreedy hN hγ hγ2 hK hu' (by omega) fun j hj => ?_
    have hj' := hω j (by omega)
    rw [biasedReturnStep, if_pos (by omega)] at hj'
    exact (isNearGreedyAt_iff_mem γ u ω j).2 hj'
  · intro hcon
    exact hu' (hcon ▸ stateAfter_mem_biasedSteepLadderSet_of_returnStep hγ hK (by omega)
      fun j hj => hω j (by omega))

end Return

/-! ### Proposition 26 -/

section Proposition26

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
/-- `1/ζ_{α,β} ≤ 1 + MN` for every `β ≥ 0`: the constant the near-greedy run costs per step. -/
theorem one_div_biasedZeta_le (N M : ℕ) {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 ≤ β) :
    1 / biasedZeta N M γ β ≤ 1 + ((M * N : ℕ) : ℝ) := by
  have hE : 1 ≤ Real.exp (β * γ / 2) :=
    Real.one_le_exp (div_nonneg (mul_nonneg hβ hγ) zero_le_two)
  have hE0 : 0 < Real.exp (β * γ / 2) := Real.exp_pos _
  have hc : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [biasedZeta, one_div, inv_div, div_le_iff₀ hE0]
  nlinarith

/-- **Proposition 26.**  For `0 < α < 1/(M-1)` there is a constant `C̃`, depending on `M`, `N`
and `α` only, such that for every `β ≥ 0` every invariant probability measure of the biased
skeleton satisfies `μ̃_{α,β} (u) ≤ C̃ e^{-β(N-1)}` at every `u ∈ S^α \ L̂_α`.

**Follows the paper's proof**, which is that of Proposition 9 transposed
(`SocialNetwork.measure_le_of_notMem_steepLadderSet`): Kac's inequality
(`SocialNetwork.kac_tsum_le`, which holds for any Markov kernel on a countable space), the
return time bounded below by a near-greedy run to `L_α` (Propositions 23 and 24) followed by
positive expressions (Remark 5), and the geometric series.  The constant is `(1 + MN)^{K+1}`,
with `K` the horizon of Proposition 23.

**Supplies the step the paper asserts**, as Proposition 9 does: that the run to `L_α` does not
visit `u` (`SocialNetwork.Bias.stateAfter_ne_of_nearGreedy`).

**Rests on** Proposition 23.

**Restated.**  The constant comes before `β`, `μ` and `u`, as "a positive constant depending on
`M`, `N` and `α`" says; with the constant chosen after them the statement was satisfied by
`C̃ = e^{β(N-1)}`, since `μ̃_{α,β}` is a probability measure.  The hypothesis `u ∈ S^α` is added,
as in Proposition 9: the paper works in `S^α` throughout.  Two things are stronger than the
paper's statement and cost nothing: it holds for every invariant probability measure, not only
for the one Theorem 25 names, and for `β ≥ 0` rather than `β > 0`. -/
theorem biasedMeasure_le_of_notMem_steepLadder (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ}
    (hγ : 0 < γ) (hγ' : γ < 1 / ((M : ℝ) - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ μ : Measure (Profile N M), IsProbabilityMeasure μ →
      IsBiasedInvariant γ β μ → ∀ u : Profile N M, IsBiasedState u →
        u ∉ biasedSteepLadderSet N M γ →
          μ {u} ≤ ENNReal.ofReal (C * Real.exp (-β * ((N : ℝ) - 1))) := by
  obtain ⟨K, -, hK⟩ := exists_horizon_isBiasedLadder hM hN hγ
  have hγ2 : γ < 2 := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have : 1 / ((M : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hM1
    linarith
  set c : ℝ := 1 + ((M * N : ℕ) : ℝ) with hc
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨c ^ (K + 1), pow_pos (by linarith) _, fun β hβ μ hμ hinv u hu hu' => ?_⟩
  have := hμ
  have hζpos : 0 < biasedZeta N M γ β := biasedZeta_pos N M γ β
  have hη0 : (0 : ℝ) ≤ eta N M β := eta_nonneg N M
  have hη1 : eta N M β < 1 := eta_lt_one (by omega) β
  set a := biasedZeta N M γ β ^ K / (1 - eta N M β) with ha
  have hapos : 0 < a := div_pos (pow_pos hζpos K) (by linarith)
  -- Kac's inequality, with the return time bounded below by Propositions 23, 24 and Remark 5.
  have hkac : μ {u} * ∑' n : ℕ, ∏ j ∈ Finset.range n, biasedReturnBound N M γ β K j ≤ 1 :=
    measure_singleton_le_of_avoid (biasedSkeletonKernel γ β) μ hinv u _ fun n => by
      rw [lintegral_kacAvoid_biasedSkeletonKernel]
      exact biasedReturnBound_prod_le (by omega) hγ hγ2 hβ hu' (hK u hu) n
  have hprodK : ∀ i : ℕ, ∏ j ∈ Finset.range (K + i), biasedReturnBound N M γ β K j
      = ENNReal.ofReal (biasedZeta N M γ β) ^ K * ENNReal.ofReal (eta N M β) ^ i := by
    intro i
    induction i with
    | zero =>
        rw [Nat.add_zero, pow_zero, mul_one,
          Finset.prod_congr rfl (fun j hj => by
            rw [biasedReturnBound, if_pos (Finset.mem_range.1 hj)]),
          Finset.prod_const, Finset.card_range]
    | succ i ih =>
        rw [show K + (i + 1) = (K + i) + 1 by ring, Finset.prod_range_succ, ih,
          biasedReturnBound, if_neg (by omega), pow_succ, mul_assoc]
  have hgeo : ENNReal.ofReal a
      ≤ ∑' n : ℕ, ∏ j ∈ Finset.range n, biasedReturnBound N M γ β K j := by
    have hinj : Function.Injective fun i : ℕ => K + i := fun i j h => Nat.add_left_cancel h
    refine le_trans (le_of_eq ?_)
      (ENNReal.tsum_comp_le_tsum_of_injective hinj
        fun n => ∏ j ∈ Finset.range n, biasedReturnBound N M γ β K j)
    simp only [hprodK]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ha,
      ENNReal.ofReal_div_of_pos (by linarith : (0 : ℝ) < 1 - eta N M β),
      ENNReal.ofReal_pow hζpos.le, ENNReal.ofReal_sub 1 hη0, ENNReal.ofReal_one,
      div_eq_mul_inv]
  have hmul : μ {u} * ENNReal.ofReal a ≤ 1 := le_trans (by gcongr) hkac
  refine le_trans (ENNReal.le_inv_iff_mul_le.2 hmul) ?_
  rw [← ENNReal.ofReal_inv_of_pos hapos]
  refine ENNReal.ofReal_le_ofReal ?_
  have hinva : a⁻¹ = (1 - eta N M β) * (1 / biasedZeta N M γ β) ^ K := by
    rw [ha, inv_div, div_eq_mul_inv, one_div, inv_pow]
  have hz : 1 / biasedZeta N M γ β ≤ c := one_div_biasedZeta_le N M hγ.le hβ
  have hz0 : (0 : ℝ) ≤ 1 / biasedZeta N M γ β := (one_div_pos.2 hζpos).le
  have hneg : -β * ((N : ℝ) - 1) = -(β * ((N : ℝ) - 1)) := by ring
  rw [hinva, hneg]
  have hA1 : 1 - eta N M β ≤ c * Real.exp (-(β * ((N : ℝ) - 1))) :=
    one_sub_eta_le hM hN hβ
  have hA2 : (1 / biasedZeta N M γ β) ^ K ≤ c ^ K := pow_le_pow_left₀ hz0 hz K
  calc (1 - eta N M β) * (1 / biasedZeta N M γ β) ^ K
      ≤ (c * Real.exp (-(β * ((N : ℝ) - 1)))) * c ^ K :=
        mul_le_mul hA1 hA2 (pow_nonneg hz0 K)
          (mul_nonneg (by linarith) (Real.exp_pos _).le)
    _ = c ^ (K + 1) * Real.exp (-(β * ((N : ℝ) - 1))) := by ring

end Proposition26

end Bias

end SocialNetwork
