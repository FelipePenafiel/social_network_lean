/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedResults
import SocialNetwork.Graphical

/-!
# Theorems 16 and 25.1: the biased process does not explode

`SocialNetwork.Bias.biasedNonExplosion` is Theorem 16 of arXiv:2607.19651, the twin of
Theorem 1.1 for the biased model with `α < 0`, and
`SocialNetwork.Bias.biasedNonExplosion_of_pos` is the same statement for every `γ > 0`, which
contains Theorem 25.1, the case `0 < α < 1/(M-1)`.  The argument does not see the sign of `α`.

Appendix C says the proof is that of Theorem 1 with Proposition 21 in place of Proposition 5,
and that is what this file is.  Theorem 1.1 goes through [GL24]'s band, which
`SocialNetwork.Band` and `SocialNetwork.BandCollapse` build for an arbitrary state space; this
file instantiates it for the biased model.  Two things are needed.

* The band's data: the rates of equation (7), the operators `π^{a,o}` on profiles, the pairs
  carrying pressure below `N`, and the bound `λ = NMe^{βN}` on the rate they carry
  (`SocialNetwork.Bias.profileBand`).
* **Lemma 10 of [GL24]** with Proposition 21 in place of Proposition 5: at least one mark in
  every `N` lands in the strip of height `λ`
  (`SocialNetwork.Bias.exists_isLambdaAt_block`).

Everything between them is shared with Theorem 1.1, word for word, because the band knows
nothing about which model it came from.
-/
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

namespace Bias

variable {N M : ℕ}

/-! ### The low-pressure family of a profile -/

/-- The pairs carrying social pressure below `N` at the profile `P`.  This is the family whose
clocks equation (11) bounds, in the biased model. -/
noncomputable def lowFinset (γ : ℝ) (P : Profile N M) : Finset (Jump N M) :=
  {p | P.pressure γ p.1 p.2 < (N : ℝ)}

theorem mem_lowFinset {γ : ℝ} {P : Profile N M} {p : Jump N M} :
    p ∈ lowFinset γ P ↔ P.pressure γ p.1 p.2 < (N : ℝ) := by
  simp [lowFinset]

/-- The total rate carried by the low-pressure family. -/
noncomputable def lowRate (γ β : ℝ) (P : Profile N M) : ℝ :=
  ∑ p ∈ lowFinset γ P, biasedJumpRate γ β P p.1 p.2

theorem lowRate_nonneg (γ β : ℝ) (P : Profile N M) : 0 ≤ lowRate γ β P :=
  Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le

theorem lowRate_le_biasedTotalRate (γ β : ℝ) (P : Profile N M) :
    lowRate γ β P ≤ biasedTotalRate γ β P :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (biasedJumpRate_pos γ β P p.1 p.2).le

/-- **The upper bound of equation (11)**, in the biased model: whatever the rest of the profile
does, the pairs carrying pressure below `N` have total rate at most `λ = NMe^{βN}`. -/
theorem lowRate_le_clockBound {β : ℝ} (hβ : 0 ≤ β) (γ : ℝ) (P : Profile N M) :
    lowRate γ β P ≤ clockBound N M β := by
  have hterm : ∀ p ∈ lowFinset γ P,
      biasedJumpRate γ β P p.1 p.2 ≤ Real.exp (β * (N : ℝ)) := by
    intro p hp
    rw [biasedJumpRate]
    exact Real.exp_le_exp.2 (by nlinarith [mem_lowFinset.1 hp])
  calc lowRate γ β P ≤ ∑ _p ∈ lowFinset γ P, Real.exp (β * (N : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (lowFinset γ P).card * Real.exp (β * (N : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ clockBound N M β := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have hcard : (lowFinset γ P).card ≤ N * M := by
          calc (lowFinset γ P).card ≤ (Finset.univ : Finset (Jump N M)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = N * M := by simp [Finset.card_univ, Fintype.card_prod]
        exact_mod_cast hcard

variable [NeZero N] [NeZero M]

/-! ### The band of the biased model -/

/-- [GL24]'s band for the biased model: the rates of equation (7), the operators `π^{a,o}` on
profiles, the pairs carrying pressure below `N`, and the bound `λ = NMe^{βN}` on the rate they
carry. -/
noncomputable def profileBand (γ : ℝ) {β : ℝ} (hβ : 0 ≤ β) : Band N M (Profile N M) where
  rate P p := biasedJumpRate γ β P p.1 p.2
  rate_pos P p := biasedJumpRate_pos γ β P p.1 p.2
  next P p := Profile.express p.1 p.2 P
  low := lowFinset γ
  lam := clockBound N M β
  lam_pos := clockBound_pos N M β
  low_le_lam P := lowRate_le_clockBound hβ γ P

@[simp]
theorem profileBand_totRate (γ : ℝ) {β : ℝ} (hβ : 0 ≤ β) (P : Profile N M) :
    (profileBand γ hβ).totRate P = biasedTotalRate γ β P := rfl

@[simp]
theorem profileBand_stepLaw (γ : ℝ) {β : ℝ} (hβ : 0 ≤ β) (P : Profile N M) :
    (profileBand γ hβ).stepLaw P = biasedStepLaw γ β P := rfl

/-- The band of the biased model carries the biased process.  Both sides are the
Ionescu-Tulcea measure of the same kernels; this is a matter of unfolding. -/
theorem profileBand_ctsPath (γ : ℝ) {β : ℝ} (hβ : 0 ≤ β) (u : Profile N M) :
    (profileBand γ hβ).ctsPath u = biasedCtsPathMeasure γ β u := by
  have hstate : ∀ (j : ℕ → Jump N M) (n : ℕ),
      stateAfterJumps (profileBand γ hβ).next u j n = stateAfter u j n := by
    intro j n
    induction n with
    | zero => rfl
    | succ n ih => rw [stateAfterJumps_succ, ih, stateAfter_succ]; rfl
  have hker : drivenKernel (profileBand γ hβ).next (profileBand γ hβ).stepLaw u
      = biasedCtsDrivingKernel γ β u := by
    funext n
    ext h : 1
    rw [drivenKernel_apply, biasedCtsDrivingKernel_apply, profileBand_stepLaw]
    exact congrArg _ (hstate _ (n + 1))
  rw [Band.ctsPath, drivenMeasure, jumpHoldMeasure, biasedCtsPathMeasure]
  simp only [hker, profileBand_stepLaw]
  rfl

/-! ### Proposition 21 at every block, read on the marks -/

/-- `S^α` is preserved along the mark chain: a discarded mark changes nothing, and an
expression is `π^{a,o}`. -/
theorem isBiasedState_markState (γ : ℝ) {β : ℝ} (hβ : 0 ≤ β) {u : Profile N M}
    (hu : IsBiasedState u) (j : ℕ → MarkJump N M) (n : ℕ) :
    IsBiasedState (markState (profileBand γ hβ) u j n) := by
  induction n with
  | zero => exact hu
  | succ n ih =>
      rw [markState_succ]
      cases hj : j n with
      | discard => exact ih
      | jump p => exact ih.express p.1 p.2

/-- A run of marks that all express follows the realisation they spell out. -/
theorem markState_add_of_jumps (γ : ℝ) {β : ℝ} (hβ : 0 ≤ β) {u : Profile N M}
    {j : ℕ → MarkJump N M} {m n : ℕ} {jj : ℕ → Jump N M}
    (h : ∀ i < n, j (m + i) = .jump (jj i)) :
    ∀ k ≤ n, markState (profileBand γ hβ) u j (m + k)
      = stateAfter (markState (profileBand γ hβ) u j m) jj k := by
  intro k
  induction k with
  | zero => intro _; rw [Nat.add_zero, stateAfter_zero]
  | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, markState_succ_jump _ u j (h k (by omega)), ih (by omega),
        stateAfter_succ]
      rfl

/-- **Lemma 10 of [GL24], transported to the marks of the biased band.**  Among any `N`
consecutive marks at least one lands in the strip of height `λ`: a discarded mark does, and if
all `N` express then Proposition 21 exhibits one whose actor carries pressure below `N`.  This
is the one line of the argument that is not shared with Theorem 1.1. -/
theorem exists_isLambdaAt_block (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) {β : ℝ}
    (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) (j : ℕ → MarkJump N M) (m : ℕ) :
    ∃ k, m * N ≤ k ∧ k < m * N + N ∧ IsLambdaAt (profileBand γ hβ) u k j := by
  classical
  by_cases hdis : ∃ i < N, j (m * N + i) = .discard
  · obtain ⟨i, hiN, hi⟩ := hdis
    exact ⟨m * N + i, by omega, by omega, by
      rw [IsLambdaAt, hi]; exact Finset.mem_insert_self _ _⟩
  · push Not at hdis
    -- every mark of the block expresses; read off the realisation it spells
    have hjump : ∀ i, i < N → ∃ p : Jump N M, j (m * N + i) = .jump p := by
      intro i hi
      cases hji : j (m * N + i) with
      | discard => exact absurd hji (hdis i hi)
      | jump p => exact ⟨p, rfl⟩
    choose p hp using hjump
    set jj : ℕ → Jump N M := fun i => if hi : i < N then p i hi else default with hjj
    have hstep : ∀ i < N, j (m * N + i) = .jump (jj i) := by
      intro i hi
      rw [hjj]
      simp only [dif_pos hi]
      exact hp i hi
    obtain ⟨k, hkN, hk⟩ := exists_pressure_lt hM hN hγ
      (isBiasedState_markState γ hβ hu j (m * N)) jj
    refine ⟨m * N + k, by omega, by omega, ?_⟩
    rw [IsLambdaAt, hstep k hkN, mem_lambdaFinset]
    refine Or.inr ⟨jj k, ?_, rfl⟩
    show _ ∈ lowFinset γ _
    rw [mem_lowFinset, markState_add_of_jumps γ hβ hstep k hkN.le]
    exact hk _

/-! ### Theorems 16 and 25.1 -/

/-- **The biased process does not explode, for any `γ > 0`**: for any `β ≥ 0` and any starting
profile `u ∈ S^α`, the jump times satisfy `P (sup {Tₘ : m ≥ 1} = ∞) = 1`.

This is **Theorem 25.1**, the regime `0 < α < 1/(M-1)` of Appendix C, and it contains
**Theorem 16**, the regime `α < 0` of Section 5.4: `γ = 1/(M-1) - α` is positive in both, and
nothing else about `α` is used.

**Follows Appendix C's prescription** for both, "as Theorem 1.1, with Proposition 21 in place of
Proposition 5", and hence [GL24] pp. 12–14: the pairs carrying pressure below `N` are again at
most `NM` of rate at most `e^{βN}` each, so again `λ = NMe^{βN}`; Proposition 21 puts one of
them in every `N` expressions; and the band of `SocialNetwork.Band`, which knows nothing about
which model it came from, does the rest. -/
theorem biasedNonExplosion_of_pos (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    biasedCtsPathMeasure γ β u {ω | explosionTime ω = ⊤} = 1 := by
  have h := measure_ctsPath_blowUp (profileBand γ hβ) (b := N)
    (exists_isLambdaAt_block hM hN hγ hβ hu)
  rwa [profileBand_ctsPath] at h

/-- **Theorem 16.**  For any `β ≥ 0`, any `α < 0` and any starting profile `u ∈ S^α`, the jump
times of the biased process satisfy `P (sup {Tₘ : m ≥ 1} = ∞) = 1`.

**Follows Appendix C's prescription**, "as Theorem 1.1, with Proposition 21 in place of
Proposition 5": it is `SocialNetwork.Bias.biasedNonExplosion_of_pos`, since `α < 0` makes
`γ = 1/(M-1) - α` positive. -/
theorem biasedNonExplosion (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    biasedCtsPathMeasure γ β u {ω | explosionTime ω = ⊤} = 1 := by
  have hγ0 : (0 : ℝ) < γ := by
    refine lt_trans (one_div_pos.2 ?_) hγ
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  exact biasedNonExplosion_of_pos hM hN hγ0 hβ hu

end Bias

end SocialNetwork
