/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedExitTime
import Mathlib.Data.Fin.VecNotation

/-!
# Examples: the definitions on small cases, and the hypotheses of the main theorems met

Lean checks that every proof in this library is correct.  It cannot check that a definition
says what the paper says, nor that the hypotheses of a statement can be met: a theorem about
every element of an empty set is true and says nothing.  This file checks both, on what can be
computed or exhibited.  Nothing here is a result of the paper, and nothing else depends on it.

* **The definitions, on small cases.**  The operator `π^{a,o}` of equation (1), the staircase
  ladder of Definition 1, the state space `S` and Definitions 1 and 2, evaluated by `decide` on
  `3 × 2` and `3 × 3` matrices; the row formula of equation (6) on one memory.  Matrices are in
  the scaled coordinates of `CONVENTIONS.md` §3: an entry `k` stands for the pressure
  `k / (M - 1)`.
* **The hypotheses of the main theorems can be met.**  The sets of states that Theorems 1–4, 25,
  27 and 31 quantify over are inhabited, their ranges of bias are not empty, the invariant
  measures that Theorems 2.1 and 27.1 speak of exist, and the mean exit times whose ratio
  Theorems 3 and 31 bound are positive and finite.

## What is not checked here

**That a characteristic time exists.**  `SocialNetwork.IsCharacteristicTime β o c` asks for one
`c` with `P (R^{β,l} (C^{-o}) > c) = e^{-1}` for every ladder `l ∈ L^o`.  Corollary 15 bounds
every such `c` from below, and assumption (17) of Proposition 12 is a statement about every such
`c`; if none existed, Corollary 15 would hold vacuously and (17) would assume nothing.  The
paper takes `c_β` to exist.  That needs the law of the exit time to have no atom, which the
holding times give, and to be the same from every ladder of `L^o`, which is the symmetry
between actors; neither is proved in this library yet.  The same holds for
`SocialNetwork.Bias.IsBiasedCharacteristicTime` and Corollary 30.
-/

namespace SocialNetwork

open MeasureTheory

/-! ### Equation (1), on a `3 × 3` matrix -/

/-- The staircase ladder for opinion `0`, with `N = 3` actors and `M = 3` opinions: actor `a`
carries `a` for opinion `0` and `-a/2` for the two others, that is `2a` and `-a` scaled. -/
example : ladderOf 3 (0 : Opinion 3) = ![![0, 0, 0], ![2, -1, -1], ![4, -2, -2]] := by
  decide

/-- **Equation (1).**  Actor `2` expresses opinion `1` from that ladder.  Its own row is reset;
every other row gains `1` on column `1`, and loses `1/(M-1) = 1/2` on the two others: scaled,
`+2` and `-1`. -/
example : express (2 : Actor 3) (1 : Opinion 3) (ladderOf 3 0)
    = ![![-1, 2, -1], ![1, 1, -2], ![0, 0, 0]] := by
  decide

/-- The result is in `S` (equation (2)): every actor's trust is still zero (Remark 3), and the
actor that expressed has a null row. -/
example : IsState (express (2 : Actor 3) (1 : Opinion 3) (ladderOf 3 0)) :=
  ⟨by decide, ⟨2, by decide⟩⟩

/-! ### Definitions 1 and 2 tell states apart -/

/-- A consensus state for opinion `0` that is not a ladder: Definition 2 imposes signs only,
Definition 1 the values `0, 1, …, N - 1` on the favoured column. -/
example : IsConsensus (0 : Opinion 2) (![![0, 0], ![1, -1], ![1, -1]] : Pressure 3 2) :=
  ⟨⟨by decide, ⟨0, by decide⟩⟩, by decide, by decide, by decide⟩

example : ¬ IsLadder (0 : Opinion 2) (![![0, 0], ![1, -1], ![1, -1]] : Pressure 3 2) :=
  fun h => by
    have := h.column
    revert this
    decide

/-- The same state is no consensus for the other opinion. -/
example : ¬ IsConsensus (1 : Opinion 2) (![![0, 0], ![1, -1], ![1, -1]] : Pressure 3 2) :=
  fun h => by
    have := h.nonneg 1
    revert this
    decide

/-! ### Equation (6), on one memory -/

/-- **Equation (6).**  An actor that has heard opinion `0` twice and opinion `1` once since it
last expressed, with `M = 3` and `γ = 1/4` (so `α = 1/(M-1) - γ = 1/4`), carries
`u (a, p) = c_p (1 + γ) - γ n_a` with `n_a = 3`: that is `7/4` for opinion `0`, ... -/
example : (⟨![2, 1, 0]⟩ : Bias.Memory 3).pressure (1 / 4 : ℝ) 0 = 7 / 4 := by
  norm_num [Bias.Memory.pressure, Bias.Memory.heard, Fin.sum_univ_three, Matrix.cons_val_two]

/-- ... and `-3/4` for the opinion it has not heard. -/
example : (⟨![2, 1, 0]⟩ : Bias.Memory 3).pressure (1 / 4 : ℝ) 2 = -3 / 4 := by
  norm_num [Bias.Memory.pressure, Bias.Memory.heard, Fin.sum_univ_three, Matrix.cons_val_two]

/-- Its trust is `n_a (M - 1) α = 3 · 2 · 1/4 = 3/2`, the identity of Remark 1
(`SocialNetwork.Bias.Memory.sum_pressure_eq`): with a bias, trust no longer vanishes. -/
example : ∑ p, (⟨![2, 1, 0]⟩ : Bias.Memory 3).pressure (1 / 4 : ℝ) p = 3 / 2 := by
  norm_num [Bias.Memory.pressure, Bias.Memory.heard, Fin.sum_univ_three, Matrix.cons_val_two]

/-! ### The hypotheses of the main theorems can be met -/

section Hypotheses

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- `L^o`, `C^o` and `S \ {0}` are inhabited, for every opinion: Theorem 1 quantifies over `S`,
Theorem 2.2 over `S \ {0}`, Theorem 3 over `C^o`. -/
example (hM : 2 ≤ M) (hN : 2 ≤ N) (o : Opinion M) :
    ∃ u : Pressure N M, IsLadder o u ∧ IsConsensus o u ∧ IsState u ∧ u ≠ 0 :=
  ⟨ladderOf N o, isLadder_ladderOf o, (isLadder_ladderOf o).isConsensus hM hN,
    (isLadder_ladderOf o).isState, ((isLadder_ladderOf o).isConsensus hM hN).ne_zero⟩

/-- The invariant measure that Theorem 2.1 is about exists: Theorem 1.2. -/
example (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ μ : Measure (Pressure N M), IsProbabilityMeasure μ ∧ IsCarriedByState μ ∧
      IsInvariantCts β μ :=
  (existsUnique_invariantCts hM hN hβ).exists

/-- The mean exit times whose ratio Theorem 3 bounds are positive and finite, so the ratio is
one of two positive reals, as the paper reads it. -/
example (hM : 2 ≤ M) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {o : Opinion M} {u : Pressure N M}
    (hu : IsConsensus o u) : 0 < (expHittingTimeCts β u (consensusSetOther N o)).toReal :=
  ENNReal.toReal_pos (expHittingTimeCts_consensusSetOther_pos β hu).ne'
    (expHittingTimeCts_consensusSetOther_lt_top hM hN hβ hu.isState o).ne

/-- The ranges of bias are not empty.  Part 1 of Theorem 4 and Theorem 16 take `α < 0`, that is
`γ > 1/(M-1)`; Theorems 25 and 31 take `0 < α < 1/(M-1)`, that is `0 < γ < 1/(M-1)`; and
Theorem 27 is stated with `α` and `γ` linked by `(M-1) γ = 1 - (M-1) α`. -/
example (hM : 2 ≤ M) :
    (∃ γ : ℝ, 1 / ((M : ℝ) - 1) < γ) ∧ (∃ γ : ℝ, 0 < γ ∧ γ < 1 / ((M : ℝ) - 1)) ∧
      ∃ γ α : ℝ, 0 < γ ∧ 0 < α ∧ ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  refine ⟨⟨2 / ((M : ℝ) - 1), ?_⟩, ⟨1 / (2 * ((M : ℝ) - 1)), by positivity, ?_⟩,
    1 / (2 * ((M : ℝ) - 1)), 1 / (2 * ((M : ℝ) - 1)), by positivity, by positivity, ?_⟩
  · exact div_lt_div_of_pos_right (by norm_num) hM1
  · rw [one_div_lt_one_div (by positivity) hM1]
    linarith
  · field_simp
    ring

/-- `L_α^o`, `C_α^o` and `S^α` are inhabited for every `γ > 0`: Theorem 4 quantifies over
`S^α`, Theorem 31 over `C_α^o`. -/
example {γ : ℝ} (hγ : 0 < γ) (hN : 2 ≤ N) (o : Opinion M) :
    ∃ P : Bias.Profile N M,
      Bias.IsBiasedLadder γ o P ∧ Bias.IsBiasedConsensus γ o P ∧ Bias.IsBiasedState P :=
  ⟨Bias.biasedLadderOf N o, Bias.isBiasedLadder_biasedLadderOf γ o,
    (Bias.isBiasedLadder_biasedLadderOf γ o).isBiasedConsensus hγ hN,
    (Bias.isBiasedLadder_biasedLadderOf γ o).isBiasedState⟩

/-- The invariant measure that Theorem 27.1 is about exists: Theorem 25.2. -/
example (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ) (hγ' : γ < 1 / ((M : ℝ) - 1))
    (hβ : 0 < β) :
    ∃ μ : Measure (Bias.Profile N M), IsProbabilityMeasure μ ∧ Bias.IsCarriedByBiasedState μ ∧
      Bias.IsBiasedInvariantCts γ β μ :=
  (Bias.existsUnique_biasedInvariantCts hM hN hγ hγ' hβ).exists

/-- The mean exit times whose ratio Theorem 31 bounds are positive and finite. -/
example (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ) (hγ' : γ < 1 / ((M : ℝ) - 1))
    (hβ : 0 ≤ β) {o : Opinion M} {u : Bias.Profile N M} (hu : Bias.IsBiasedConsensus γ o u) :
    0 < (Bias.biasedExpHittingTimeCts γ β u (Bias.biasedConsensusSetOther N γ o)).toReal :=
  ENNReal.toReal_pos (Bias.biasedExpHittingTimeCts_consensusSetOther_pos hM hγ' β hu).ne'
    (Bias.biasedExpHittingTimeCts_consensusSetOther_lt_top hM hN hγ hγ' hβ
      hu.isBiasedState o).ne

end Hypotheses

end SocialNetwork
