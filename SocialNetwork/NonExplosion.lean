/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.JumpHold

/-!
# The bound `λ` of equation (11)

The proof of Theorem 1.1 at p. 16 of arXiv:2607.19651 splits the expressions into those coming
from an actor carrying pressure below `N` and the others, and sandwiches the first between two
Poisson processes, of rates `MN` and `λ = NMe^{βN}`.  Only the upper bound is used, and only
through its consequence.  This file supplies it:

* `SocialNetwork.lowFinset` — the pairs whose actor carries pressure below `N`.
* `SocialNetwork.lowRate_le_clockBound` — they carry total rate at most `λ = NMe^{βN}`,
  whatever the rest of the matrix does.  This is the content of (11): there are at most `NM`
  such pairs, and the scaled coordinates turn `‖u (a, ·)‖_∞ < N` into a rate at most `e^{βN}`.

`SocialNetwork.Graphical` builds [GL24]'s band out of `λ`, and `SocialNetwork.Collapse`
identifies the process with what the band carries; Theorem 1.1 itself is
`SocialNetwork.nonExplosion`, there.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ}

/-! ### The low-pressure family and the bound `λ` of equation (11) -/

/-- The pairs whose actor carries social pressure below `N`, in the scaled coordinates of
`SocialNetwork.Defs`.  This is the family whose clocks equation (11) bounds. -/
def lowFinset (v : Pressure N M) : Finset (Jump N M) :=
  {p | rowSup v p.1 < N * (M - 1)}

theorem mem_lowFinset {v : Pressure N M} {p : Jump N M} :
    p ∈ lowFinset v ↔ rowSup v p.1 < N * (M - 1) := by
  simp [lowFinset]

/-- The total rate carried by the low-pressure family. -/
noncomputable def lowRate (β : ℝ) (v : Pressure N M) : ℝ :=
  ∑ p ∈ lowFinset v, jumpRate β v p.1 p.2

theorem lowRate_nonneg (β : ℝ) (v : Pressure N M) : 0 ≤ lowRate β v :=
  Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le

/-- The constant `λ = NMe^{βN}` of equation (11). -/
noncomputable def clockBound (N M : ℕ) (β : ℝ) : ℝ := ((N * M : ℕ) : ℝ) * Real.exp (β * (N : ℝ))

theorem clockBound_pos (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ) : 0 < clockBound N M β := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hNM : (0 : ℝ) < ((N * M : ℕ) : ℝ) := by positivity
  unfold clockBound
  positivity

/-- **The upper bound of equation (11).**  Whatever the rest of the matrix does, the pairs
whose actor carries pressure below `N` have total rate at most `λ = NMe^{βN}`: there are at
most `NM` of them and each carries rate at most `e^{βN}`. -/
theorem lowRate_le_clockBound (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    lowRate β v ≤ clockBound N M β := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hterm : ∀ p ∈ lowFinset v, jumpRate β v p.1 p.2 ≤ Real.exp (β * (N : ℝ)) := by
    intro p hp
    have hrow : rowSup v p.1 < N * (M - 1) := mem_lowFinset.1 hp
    have habs : (v p.1 p.2).natAbs < N * (M - 1) := lt_of_le_of_lt (le_rowSup v p.1 p.2) hrow
    have hint : (v p.1 p.2) ≤ ((N * (M - 1) : ℕ) : ℤ) := by omega
    have hcast : (((N * (M - 1) : ℕ) : ℤ) : ℝ) = (N : ℝ) * ((M : ℝ) - 1) := by
      have h1 : 1 ≤ M := le_trans one_le_two hM
      push_cast [Nat.cast_sub h1]
      ring
    have hreal : (v p.1 p.2 : ℝ) ≤ (N : ℝ) * ((M : ℝ) - 1) := by
      rw [← hcast]; exact_mod_cast hint
    rw [jumpRate]
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ hM1]
    nlinarith
  calc lowRate β v ≤ ∑ _p ∈ lowFinset v, Real.exp (β * (N : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (lowFinset v).card * Real.exp (β * (N : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ clockBound N M β := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have hcard : (lowFinset v).card ≤ N * M := by
          calc (lowFinset v).card ≤ (Finset.univ : Finset (Jump N M)).card :=
                Finset.card_le_card (Finset.subset_univ _)
            _ = N * M := by simp [Finset.card_univ, Fintype.card_prod]
        exact_mod_cast hcard

theorem lowRate_le_totalRate (β : ℝ) (v : Pressure N M) : lowRate β v ≤ totalRate β v :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (jumpRate_pos β v p.1 p.2).le

variable [NeZero N] [NeZero M]

/-! ### The discount ratio -/

/-- The ratio `d = (λ + θ)/λ` that the supermartingale of
`SocialNetwork.measure_holdBlowUp_eq_one` discounts by at each low expression. -/
theorem one_lt_discountRatio {β θ : ℝ} (hθ : 0 < θ) :
    1 < ENNReal.ofReal ((clockBound N M β + θ) / clockBound N M β) := by
  have hL : 0 < clockBound N M β := clockBound_pos N M β
  refine ENNReal.one_lt_ofReal.2 ?_
  rw [lt_div_iff₀ hL]
  linarith

end SocialNetwork
