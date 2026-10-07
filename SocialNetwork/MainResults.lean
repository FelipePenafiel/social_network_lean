/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedConcentration
import SocialNetwork.BiasedExistence
import SocialNetwork.BiasedMetastability
import SocialNetwork.Concentration
import SocialNetwork.Existence
import SocialNetwork.Metastability

/-!
# The main results of arXiv:2607.19651, in one place

Theorems 1–4, 16, 25, 27 and 31 of the paper, restated in full and each proved by the
declaration of the library that formalises it, so that what is claimed can be read against the
paper without the rest of the library.  Lean checks that each statement below is exactly the
library's: the proof is the library declaration itself.

**What each one rests on.**  A statement here is proved outright when the library declaration
is, and `STATUS.md` records which are.  At present:

* Theorems 1.1, 1.2, 16, 25.1, 25.2 and part 1 of Theorem 4 are proved outright.
* Theorems 2.1, 2.2 and 3 rest on Lemma 20, which is false as printed for `M ≥ 4`
  (`FOR-THE-AUTHORS.md` §1.1); Theorems 27.1, 27.2 and 31 rest on Proposition 23
  (`FOR-THE-AUTHORS.md` §1.2).  Their proofs are written, and `#print axioms` shows the
  `sorryAx` they inherit.
* Theorems 3 and 31 also take Proposition 12, which is Theorem 5.3 of [LM22] and not a result
  of the paper, as the hypothesis `hLM22`.

Part 2 of Theorem 4 says that Theorems 1, 2 and 3 hold in adapted form for `0 ≤ α < 1/(M-1)`:
it is Theorems 25, 27 and 31.

**How to read the statements.**  Matrices of social pressures are in the scaled coordinates of
`CONVENTIONS.md` §3, so `e^{β u (a, o)}` reads `e^{β v (a, o)/(M-1)}`, and the biased model is
written with `γ = 1/(M-1) - α`: `α < 0` is `γ > 1/(M-1)`, and `0 < α < 1/(M-1)` is
`0 < γ < 1/(M-1)`.  `SocialNetwork/Examples.lean` checks that the hypotheses below can be met.
-/

namespace SocialNetwork

namespace MainResults

open MeasureTheory

open scoped ENNReal

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- **Theorem 1.1.**  For every `β ≥ 0` and every `u ∈ S`, the jump times of the process have no
finite accumulation point: `P (sup_m T_m = ∞) = 1`. -/
theorem theorem1_1 (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) :
    ctsPathMeasure β u {ω | explosionTime ω = ⊤} = 1 :=
  nonExplosion hM hN hβ hu

/-- **Theorem 1.2.**  For every `β ≥ 0` the process has exactly one invariant probability
measure carried by `S`. -/
theorem theorem1_2 (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ∃! μ : Measure (Pressure N M),
      IsProbabilityMeasure μ ∧ IsCarriedByState μ ∧ IsInvariantCts β μ :=
  existsUnique_invariantCts hM hN hβ

/-- **Theorem 2.1.**  There is `C > 0` such that for every `β ≥ 0` the invariant measure gives
the ladder set mass at least `1 - C e^{-β/(M-1)}`. -/
theorem theorem2_1 (hM : 2 ≤ M) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ μ : Measure (Pressure N M),
      IsProbabilityMeasure μ → IsCarriedByState μ → IsInvariantCts β μ →
        ENNReal.ofReal (1 - C * Real.exp (-β / ((M : ℝ) - 1))) ≤ μ (ladderSet N M) :=
  measure_ladderSet_ge hM hN

/-- **Theorem 2.2.**  For every `δ > 0`, uniformly over `u ∈ S \ {0}`, the probability that the
process has not reached the ladder set by time `e^{-β(1-δ)/(M-1)}` tends to `0` as `β → ∞`. -/
theorem theorem2_2 (hM : 2 ≤ M) (hN : 3 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ u ∈ (stateSet N M \ {0} : Set (Pressure N M)),
        probHittingGT β u (ladderSet N M)
          (ENNReal.ofReal (Real.exp (-β / ((M : ℝ) - 1) * (1 - δ)))))
      Filter.atTop (nhds 0) :=
  tendsto_hittingTime_ladderSet hM hN hδ

/-- **Theorem 3**, assuming Proposition 12 (`hLM22`).  There are `β₀, C₁ > 0` and
`C₂ ∈ (0, 1/2)` such that for `β ≥ β₀`, every opinion `o` and every `u ∈ C^o`, the exit time
from `C^o` rescaled by its mean is exponential of parameter one up to `C₁ β³ e^{-C₂ β}`, and the
mean exit times from two states of `C^o` agree to the same order. -/
theorem theorem3 (hM : 2 ≤ M) (hN : 3 ≤ N) (hLM22 : ExitTimeApproxExponential N M) :
    ∃ β₀ C₁ C₂ : ℝ, 0 < β₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧ C₂ < 1 / 2 ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ o : Opinion M, ∀ u : Pressure N M, IsConsensus o u →
        (∀ t : ℝ, 0 ≤ t →
          |(probHittingGT β u (consensusSetOther N o)
              (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
            - Real.exp (-t)| ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β)) ∧
        ∀ v : Pressure N M, IsConsensus o v →
          |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
              (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
            ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β) :=
  metastability hM hN hLM22

/-- **Theorem 4, part 1.**  For `β > 0` and `α < 0`, from every `u ∈ S^α`, almost surely the
same actor expresses the same opinion from some time on. -/
theorem theorem4_1 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 < β) {u : Bias.Profile N M} (hu : Bias.IsBiasedState u) :
    Bias.biasedPathMeasure γ β u {ω | ∃ n, ∀ m, n ≤ m → (ω m).1 = (ω n).1} = 1 :=
  Bias.biasedAbsorption hM hN hγ hβ hu

/-- **Theorem 16.**  For `β ≥ 0` and `α < 0`, the biased process does not explode. -/
theorem theorem16 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 ≤ β) {u : Bias.Profile N M} (hu : Bias.IsBiasedState u) :
    Bias.biasedCtsPathMeasure γ β u {ω | explosionTime ω = ⊤} = 1 :=
  Bias.biasedNonExplosion hM hN hγ hβ hu

/-- **Theorem 25.1.**  For `β ≥ 0` and `α < 1/(M-1)`, the biased process does not explode. -/
theorem theorem25_1 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    {u : Bias.Profile N M} (hu : Bias.IsBiasedState u) :
    Bias.biasedCtsPathMeasure γ β u {ω | explosionTime ω = ⊤} = 1 :=
  Bias.biasedNonExplosion_of_pos hM hN hγ hβ hu

/-- **Theorem 25.2.**  For `β > 0` and `0 < α < 1/(M-1)`, the biased process has exactly one
invariant probability measure carried by `S^α`. -/
theorem theorem25_2 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β) :
    ∃! μ : Measure (Bias.Profile N M),
      IsProbabilityMeasure μ ∧ Bias.IsCarriedByBiasedState μ ∧ Bias.IsBiasedInvariantCts γ β μ :=
  Bias.existsUnique_biasedInvariantCts hM hN hγ hγ' hβ

/-- **Theorem 27.1.**  For `0 < α < 1/(M-1)` there is `C > 0` such that for every `β ≥ 0` the
invariant measure gives the biased ladder set mass at least `1 - C e^{-β(M-1)α}`. -/
theorem theorem27_1 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ α : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ μ : Measure (Bias.Profile N M),
      IsProbabilityMeasure μ → Bias.IsCarriedByBiasedState μ → Bias.IsBiasedInvariantCts γ β μ →
        ENNReal.ofReal (1 - C * Real.exp (-β * (((M : ℝ) - 1) * α)))
          ≤ μ (Bias.biasedLadderSet N M γ) :=
  Bias.biasedMeasure_ladderSet_ge hM hN hγ h hα

/-- **Theorem 27.2.**  For `0 < α < 1/(M-1)` and every `δ > 0`, uniformly over `u ∈ S^α`, the
probability that the biased process has not reached the biased ladder set by time
`e^{-β(M-1)α(1-δ)}` tends to `0` as `β → ∞`. -/
theorem theorem27_2 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ α : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ u ∈ Bias.biasedStateSet N M,
        Bias.biasedProbHittingGT γ β u (Bias.biasedLadderSet N M γ)
          (ENNReal.ofReal (Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ)))))
      Filter.atTop (nhds 0) :=
  Bias.tendsto_biasedHittingTime hM hN hγ h hα hδ

/-- **Theorem 31**, assuming the biased Proposition 12 (`hLM22`).  For `0 < α < 1/(M-1)` there
are `β₀, C₁, C₂ > 0` such that for `β ≥ β₀`, every opinion `o` and every `u ∈ C_α^o`, the exit
time from `C_α^o` rescaled by its mean is exponential of parameter one up to `C₁ β³ e^{-C₂ β}`,
and the mean exit times from two states of `C_α^o` agree to the same order. -/
theorem theorem31 (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hLM22 : Bias.BiasedExitTimeApproxExponential N M γ) :
    ∃ β₀ C₁ C₂ : ℝ, 0 < β₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ o : Opinion M, ∀ u : Bias.Profile N M,
        Bias.IsBiasedConsensus γ o u →
        (∀ t : ℝ, 0 ≤ t →
          |(Bias.biasedProbHittingGT γ β u (Bias.biasedConsensusSetOther N γ o)
              (ENNReal.ofReal t *
                Bias.biasedExpHittingTimeCts γ β u (Bias.biasedConsensusSetOther N γ o))).toReal
            - Real.exp (-t)| ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β)) ∧
        ∀ v : Bias.Profile N M, Bias.IsBiasedConsensus γ o v →
          |(Bias.biasedExpHittingTimeCts γ β u (Bias.biasedConsensusSetOther N γ o)).toReal /
              (Bias.biasedExpHittingTimeCts γ β v
                (Bias.biasedConsensusSetOther N γ o)).toReal - 1|
            ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β) :=
  Bias.biasedMetastability hM hN hγ hγ' hLM22

end MainResults

end SocialNetwork
