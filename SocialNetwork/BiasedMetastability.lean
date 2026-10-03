/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedConsensusExit

/-!
# Corollary 30 and Theorem 31: metastability of the biased model

Corollary 30 and Theorem 31 of arXiv:2607.19651, Appendix C, from Lemmas 28 and 29 and the
biased twin of Proposition 12, which is declared as an axiom.

## Main statements

* `SocialNetwork.Bias.le_biasedCharacteristicTime` — **Corollary 30**.
* `SocialNetwork.Bias.biasedMetastability` — **Theorem 31**, modulo the biased Proposition 12.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

section PositiveBias

variable [NeZero N] [NeZero M]

/-- The characteristic time `c_{α,β}` of Appendix C. -/
def IsBiasedCharacteristicTime (γ β : ℝ) (o : Opinion M) (c : ℝ) : Prop :=
  0 < c ∧ ∀ l : Profile N M, IsBiasedLadder γ o l →
    biasedProbHittingGT γ β l (biasedConsensusSetOther N γ o) (ENNReal.ofReal c)
      = ENNReal.ofReal (Real.exp (-1))

/-- **Corollary 30.**  `c_{α,β} ≥ (1/2) N^{-3} (M+1)^{-3} e^{βγ/2}`. -/
theorem le_biasedCharacteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {c : ℝ}
    (hc : IsBiasedCharacteristicTime (N := N) γ β o c) :
    (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ * Real.exp (β * γ / 2) ≤ c := by
  obtain ⟨hcpos, hchar⟩ := hc
  have hKpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast Nat.mul_pos (Nat.pow_pos hN0) (Nat.pow_pos (Nat.succ_pos M))
  have h29 := le_biasedProbHittingGT hM hN hγ hγ' hβ
    (isBiasedLadder_biasedLadderOf (N := N) γ o) hcpos
  rw [hchar _ (isBiasedLadder_biasedLadderOf (N := N) γ o)] at h29
  have h' := Real.exp_le_exp.mp
    ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h29)
  rw [show -β * γ / 2 = -(β * γ / 2) by ring, Real.exp_neg] at h'
  have hFpos : (0 : ℝ) < Real.exp (β * γ / 2) := Real.exp_pos _
  have key : (1 : ℝ) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) *
      (Real.exp (β * γ / 2))⁻¹ := by linarith
  have hFle : Real.exp (β * γ / 2) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right key hFpos.le
    rwa [one_mul, inv_mul_cancel_right₀ hFpos.ne'] at this
  have hKne : ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) ≠ 0 := hKpos.ne'
  have hstep := mul_le_mul_of_nonneg_left hFle
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹)
  rwa [show (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ *
    (2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) = c by field_simp] at hstep

/-! ### The four assumptions of the biased Proposition 12

Appendix C says only that "the proof of Theorem 31 follows exactly as the proof of Theorem 3",
and does not name the constants.  They are the ones Section 5.3 produces once `1/(M-1)` is
replaced by `γ/2`: the exponent `γ/2` of Lemmas 28 and 29 is halved to `γ/4` to absorb
the factor `β` of step (20), so `δ = θ = γ/4` here, where the unbiased proof had two
different values.
-/

/-- Assumption **(16)** of the biased Proposition 12, with `s₂ = 2β`.

As in the unbiased model, Lemma 28 is about `L_α` and the assumption is about
`L_α^o ∪ C_α^{-o}`; the two are related by `L_α ⊆ L_α^o ∪ C_α^{-o}`, a biased ladder for
`p ≠ o` being a biased consensus state for `p`. -/
theorem biasedProbHittingGT_ladderOther_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (o : Opinion M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ u : Profile N M, IsBiasedState u →
      biasedProbHittingGT γ β u
          ({v | IsBiasedLadder γ o v} ∪ biasedConsensusSetOther N γ o)
          (ENNReal.ofReal (2 * β))
        ≤ ENNReal.ofReal (C * Real.exp (-β * γ / 2)) := by
  obtain ⟨C, hC, h28⟩ := biasedProbHitting_le hM hN hγ hγ'
  refine ⟨C, hC, fun β hβ u hu => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_) (h28 β hβ u hu)
  have hsub : biasedLadderSet N M γ
      ⊆ {v | IsBiasedLadder γ o v} ∪ biasedConsensusSetOther N γ o := by
    rintro v ⟨p, hp⟩
    by_cases hpo : p = o
    · exact Or.inl (hpo ▸ hp)
    · exact Or.inr ⟨p, hpo, hp.isBiasedConsensus hγ (by omega)⟩
  exact lt_of_lt_of_le hω (biasedHittingTimeCts_mono u hsub ω)

/-- Assumption **(15)** of the biased Proposition 12, with `s₁ = 1` and
`ε₁ = 2N³(M+1)³e^{-βγ/2}`.

Part 1 of Lemma 29 at `t = 1`, read on the complementary event, with `1 - e^{-x} ≤ x`. -/
theorem biasedMeasure_hittingTime_le_one (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β)
    {o : Opinion M} {l : Profile N M} (hl : IsBiasedLadder γ o l) :
    biasedCtsPathMeasure γ β l
        {ω | biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal 1}
      ≤ ENNReal.ofReal (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β * γ / 2)) := by
  set E : ℝ := Real.exp (-β * γ / 2) with hE
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hE0 : 0 < E := Real.exp_pos _
  have hmeas : MeasurableSet {ω : ℕ → Step N M |
      ENNReal.ofReal 1 < biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω} :=
    measurableSet_lt measurable_const (measurable_biasedHittingTimeCts l _)
  have hcompl : {ω : ℕ → Step N M |
      biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal 1}
      = {ω : ℕ → Step N M |
        ENNReal.ofReal 1 < biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω}ᶜ := by
    ext ω; simp [not_lt]
  have h29 := le_biasedProbHittingGT hM hN hγ hγ' hβ hl (t := 1) one_pos
  rw [show (-2 * (1 : ℝ) * Kc * E) = -(2 * Kc * E) by ring] at h29
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  refine le_trans (tsub_le_tsub_left h29 1) ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.add_one_le_exp (-(2 * Kc * E))
  linarith

/-- Assumption **(18)** of the biased Proposition 12, with `s₂ = 2β`, `θ = γ/4` and
`K = N²M + 16e⁻¹/γN³(M+1)³`.

Part 2 of Lemma 29 at `t = 2β` gives `(N²M + 4βN³(M+1)³) e^{-βγ/2}`; splitting the exponent
in half and absorbing `β e^{-βγ/4} ≤ (4/γ) e^{-1}` is step (20) of Section 5.3. -/
theorem biasedMeasure_hittingTime_le_two_mul (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β)
    {o : Opinion M} {u : Profile N M} (hu : IsBiasedConsensus γ o u) :
    biasedCtsPathMeasure γ β u
        {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω
          ≤ ENNReal.ofReal (2 * β)}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ)
            + 16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ))
          * Real.exp (-(γ / 4) * β)) := by
  refine le_trans
    (biasedProbHittingLE_le hM hN hγ hγ' hβ.le hu (by linarith : (0 : ℝ) < 2 * β))
    (ENNReal.ofReal_le_ofReal ?_)
  have ha : (0 : ℝ) < 4 / γ := by positivity
  have hγ0 : (γ : ℝ) ≠ 0 := hγ.ne'
  set E : ℝ := Real.exp (-β * γ / 4) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by norm_num)
  have hexpeq : -β * γ / 4 + -β * γ / 4 = -β * γ / 2 := by ring
  have hhalf : Real.exp (-β * γ / 2) = E * E := by rw [hE, ← Real.exp_add, hexpeq]
  have hgoal : Real.exp (-(γ / 4) * β) = E := by
    rw [hE, show -(γ / 4) * β = -β * γ / 4 by ring]
  rw [hhalf, hgoal]
  have hβE : β * E ≤ (4 / γ) * Real.exp (-1) := by
    have h := mul_exp_neg_div_le ha β
    rwa [show -β / (4 / γ) = -β * γ / 4 by field_simp] at h
  have hKc : (0 : ℝ) ≤ ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hNM : (0 : ℝ) ≤ ((N ^ 2 * M : ℕ) : ℝ) := by positivity
  have hstep : (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E
      ≤ ((N ^ 2 * M : ℕ) : ℝ)
        + 16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have hexp : 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (β * E)
        ≤ 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((4 / γ) * Real.exp (-1)) :=
      mul_le_mul_of_nonneg_left hβE (by linarith)
    calc (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E
        = ((N ^ 2 * M : ℕ) : ℝ) * E + 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (β * E) := by ring
      _ ≤ ((N ^ 2 * M : ℕ) : ℝ) * 1
          + 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((4 / γ) * Real.exp (-1)) :=
          add_le_add (mul_le_mul_of_nonneg_left hE1 hNM) hexp
      _ = ((N ^ 2 * M : ℕ) : ℝ)
          + 16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by ring
  calc (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * (E * E)
      = ((((N ^ 2 * M : ℕ) : ℝ)
          + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E) * E := by ring
    _ ≤ (((N ^ 2 * M : ℕ) : ℝ)
        + 16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E :=
        mul_le_mul_of_nonneg_right hstep hE0.le

/-- Assumption **(17)** of the biased Proposition 12, with `s₂ = 2β`, `δ = γ/4` and
`C = 16e⁻¹/γN³(M+1)³ + C₂₈`.

This is where Corollary 30 enters: it turns `s₂ / c_{α,β}` into `4βN³(M+1)³e^{-βγ/2}`, and
half of the exponent absorbs the factor `β`. -/
theorem biasedMax_le_of_isCharacteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {c : ℝ}
    (hc : IsBiasedCharacteristicTime (N := N) γ β o c) {C : ℝ} (hC : 0 ≤ C) :
    max (2 * β / c) (C * Real.exp (-β * γ / 2))
      ≤ (16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + C)
          * Real.exp (-(γ / 4) * β) := by
  have ha : (0 : ℝ) < 4 / γ := by positivity
  have hγ0 : (γ : ℝ) ≠ 0 := hγ.ne'
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  set E : ℝ := Real.exp (-β * γ / 4) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by norm_num)
  have hexpeq : -β * γ / 4 + -β * γ / 4 = -β * γ / 2 := by ring
  have hhalf : Real.exp (-β * γ / 2) = E * E := by rw [hE, ← Real.exp_add, hexpeq]
  have hgoal : Real.exp (-(γ / 4) * β) = E := by
    rw [hE, show -(γ / 4) * β = -β * γ / 4 by ring]
  have hbig : (0 : ℝ) ≤ 16 / γ * Real.exp (-1) * Kc := by positivity
  rw [hgoal]
  refine max_le ?_ ?_
  · have hcpos : 0 < c := hc.1
    have h30 := le_biasedCharacteristicTime hM hN hγ hγ' hβ hc
    set F : ℝ := Real.exp (β * γ / 2) with hF
    have hFpos : 0 < F := Real.exp_pos _
    have hbpos : (0 : ℝ) < 1 / 2 * Kc⁻¹ * F := by positivity
    have hdiv : 2 * β / c ≤ 2 * β / (1 / 2 * Kc⁻¹ * F) :=
      div_le_div_of_nonneg_left (by linarith) hbpos h30
    have hfe : 2 * β / (1 / 2 * Kc⁻¹ * F) = 4 * Kc * (β * E) * E := by
      rw [show 4 * Kc * (β * E) * E = 4 * Kc * β * (E * E) by ring, ← hhalf,
        show -β * γ / 2 = -(β * γ / 2) by ring, Real.exp_neg, ← hF]
      field_simp
      ring
    calc 2 * β / c ≤ 4 * Kc * (β * E) * E := hdiv.trans_eq hfe
      _ ≤ 4 * Kc * ((4 / γ) * Real.exp (-1)) * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by
              have h := mul_exp_neg_div_le ha β
              rwa [show -β / (4 / γ) = -β * γ / 4 by field_simp] at h) (by positivity)) hE0.le
      _ = 16 / γ * Real.exp (-1) * Kc * E := by ring
      _ ≤ (16 / γ * Real.exp (-1) * Kc + C) * E := by nlinarith
  · calc C * Real.exp (-β * γ / 2) = C * E * E := by rw [hhalf]; ring
      _ ≤ C * E := by
          have h := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hC hE0.le)
          linarith
      _ ≤ (16 / γ * Real.exp (-1) * Kc + C) * E := by nlinarith

/-- **Proposition 12 for the biased process**, the consequence for this model of Theorem 5.3
of [LM22].

**This is an axiom, not a theorem, and it is the second one this repository asks you to
trust.**  It is the exact twin of `SocialNetwork.exitTime_approx_exponential`, over
`Profile N M` instead of `Pressure N M`.  Appendix C never states it: it says only that "the
proof of Theorem 31 follows exactly as the proof of Theorem 3", and the proof of Theorem 3
runs through Proposition 12, which is stated for the unbiased process alone.

**One axiom cannot serve both models.**  Stated abstractly — over an arbitrary family of
measures and an arbitrary hitting time — the statement is *inconsistent*: the zero measure
with an empty ladder set satisfies the four assumptions vacuously and falsifies the conclusion
at `t = 0`.  What rules that out is the strong Markov property, which is the content of [LM22]
and is not expressible here, so the statement has to be attached to a concrete process.  The
unbiased axiom is attached to the unbiased one, and this is the price: a second thing to
trust.  See `FOR-THE-AUTHORS.md` §3.

The hypotheses are named after the equations of the paper, and `ε₁ ε₂ s₁ s₂` are functions of
`β` for the reason recorded at the unbiased axiom. -/
axiom biasedExitTime_approx_exponential (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (o : Opinion M)
    (ε₁ ε₂ s₁ s₂ : ℝ → ℝ) {C δ K θ β₁ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hK : 0 < K) (hθ : 0 < θ)
    (hpos : ∀ β : ℝ, β₁ ≤ β → 0 < ε₁ β ∧ 0 < ε₂ β ∧ 0 < s₁ β ∧ 0 < s₂ β)
    (hsum : ∀ β : ℝ, β₁ ≤ β → ε₁ β + ε₂ β ≤ 1 / 2)
    (h15 : ∀ β : ℝ, β₁ ≤ β → ∀ l : Profile N M, IsBiasedLadder γ o l →
      biasedCtsPathMeasure γ β l
          {ω | biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω
            ≤ ENNReal.ofReal (s₁ β)}
        ≤ ENNReal.ofReal (ε₁ β))
    (h16 : ∀ β : ℝ, β₁ ≤ β → ∀ u : Profile N M, IsBiasedState u →
      biasedProbHittingGT γ β u
          ({v | IsBiasedLadder γ o v} ∪ biasedConsensusSetOther N γ o)
          (ENNReal.ofReal (s₂ β))
        ≤ ENNReal.ofReal (ε₂ β))
    (h17 : ∀ β : ℝ, β₁ ≤ β → ∀ c : ℝ, IsBiasedCharacteristicTime (N := N) γ β o c →
      max (s₂ β / c) (ε₂ β) ≤ C * Real.exp (-δ * β))
    (h18 : ∀ β : ℝ, β₁ ≤ β → ∀ u : Profile N M, IsBiasedConsensus γ o u →
      biasedCtsPathMeasure γ β u
          {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω
            ≤ ENNReal.ofReal (s₂ β)}
        ≤ ENNReal.ofReal (K * Real.exp (-θ * β))) :
    ∃ β₀ K' : ℝ, β₁ ≤ β₀ ∧ 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Profile N M, IsBiasedConsensus γ o u →
      (∀ t : ℝ, 0 ≤ t →
        |(biasedProbHittingGT γ β u (biasedConsensusSetOther N γ o)
            (ENNReal.ofReal t *
              biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)) ∧
      ∀ v : Profile N M, IsBiasedConsensus γ o v →
        |(biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o)).toReal /
            (biasedExpHittingTimeCts γ β v (biasedConsensusSetOther N γ o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)

/-- **Theorem 31.**  Metastability for the biased model: for `0 < α < 1/(M-1)` there are
`β₀, C₁ > 0` and `C₂ > 0`, depending only on `α`, `M` and `N`, such that the rescaled exit
time from a biased consensus set is exponential of parameter one up to `C₁ β³ e^{-C₂ β}`. -/
theorem biasedMetastability (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) :
    ∃ β₀ C₁ C₂ : ℝ, 0 < β₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ o : Opinion M, ∀ u : Profile N M, IsBiasedConsensus γ o u →
        (∀ t : ℝ, 0 ≤ t →
          |(biasedProbHittingGT γ β u (biasedConsensusSetOther N γ o)
              (ENNReal.ofReal t *
                biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o))).toReal
            - Real.exp (-t)| ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β)) ∧
        ∀ v : Profile N M, IsBiasedConsensus γ o v →
          |(biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o)).toReal /
              (biasedExpHittingTimeCts γ β v (biasedConsensusSetOther N γ o)).toReal - 1|
            ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β) := by
  have hKcpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  have hNMpos : (0 : ℝ) < ((N ^ 2 * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (by omega : 0 < M)
  have hδpos : (0 : ℝ) < γ / 4 := by positivity
  have hepos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  -- Proposition 12 for the biased process, opinion by opinion
  have key : ∀ o : Opinion M, ∃ β₀ K' : ℝ, 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Profile N M, IsBiasedConsensus γ o u →
      (∀ t : ℝ, 0 ≤ t →
        |(biasedProbHittingGT γ β u (biasedConsensusSetOther N γ o)
            (ENNReal.ofReal t *
              biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min ((γ / 4) / 3) (1 / 2)) (γ / 4) * β)) ∧
      ∀ v : Profile N M, IsBiasedConsensus γ o v →
        |(biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o)).toReal /
            (biasedExpHittingTimeCts γ β v (biasedConsensusSetOther N γ o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min ((γ / 4) / 3) (1 / 2)) (γ / 4) * β) := by
    intro o
    -- Lemma 28, in the form assumption (16) needs
    obtain ⟨Cl, hCl, h16⟩ := biasedProbHittingGT_ladderOther_le hM hN hγ hγ' o
    -- the threshold above which `ε₁ + ε₂ ≤ 1/2`
    set β₁ : ℝ := max 1 (4 / γ * (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl)) with hβ₁def
    have hβ₁one : (1 : ℝ) ≤ β₁ := le_max_left _ _
    have hpos' : ∀ β : ℝ, β₁ ≤ β → (0 : ℝ) < β := fun β hβ =>
      lt_of_lt_of_le zero_lt_one (le_trans hβ₁one hβ)
    have hsum : ∀ β : ℝ, β₁ ≤ β →
        2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β * γ / 2)
          + Cl * Real.exp (-β * γ / 2) ≤ 1 / 2 := by
      intro β hβ
      have hβpos := hpos' β hβ
      have hb : 4 / γ * (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) ≤ β :=
        le_trans (le_max_right _ _) hβ
      have hexp : Real.exp (-β * γ / 2) ≤ (2 / γ) / β := by
        have h := exp_neg_div_le (by positivity : (0 : ℝ) < 2 / γ) hβpos
        rwa [show -β / (2 / γ) = -β * γ / 2 by field_simp] at h
      have hmul : (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * Real.exp (-β * γ / 2)
          ≤ (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * ((2 / γ) / β) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
      have hfin : (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * ((2 / γ) / β) ≤ 1 / 2 := by
        rw [show (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * ((2 / γ) / β)
            = ((2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * (2 / γ)) / β by ring,
          div_le_iff₀ hβpos]
        have hhalf : (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * (2 / γ)
            = 1 / 2 * (4 / γ * (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl)) := by ring
        rw [hhalf]
        linarith
      linarith
    have hCpos : (0 : ℝ)
        < 16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl := by positivity
    have hKpos : (0 : ℝ) < ((N ^ 2 * M : ℕ) : ℝ)
        + 16 / γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by positivity
    obtain ⟨b, K', -, hbpos, hK'pos, hmain⟩ :=
      biasedExitTime_approx_exponential hM hN hγ hγ' o
        (fun β => 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β * γ / 2))
        (fun β => Cl * Real.exp (-β * γ / 2))
        (fun _ => 1) (fun β => 2 * β)
        hCpos hδpos hKpos hδpos
        (fun β hβ => ⟨mul_pos (by linarith) (Real.exp_pos _), mul_pos hCl (Real.exp_pos _),
          one_pos, by linarith [hpos' β hβ]⟩)
        hsum
        (fun β hβ l hl =>
          biasedMeasure_hittingTime_le_one hM hN hγ hγ' (hpos' β hβ).le hl)
        (fun β hβ u hu => h16 β (hpos' β hβ).le u hu)
        (fun β hβ c hc =>
          biasedMax_le_of_isCharacteristicTime hM hN hγ hγ' (hpos' β hβ).le hc hCl.le)
        (fun β hβ u hu =>
          biasedMeasure_hittingTime_le_two_mul hM hN hγ hγ' (hpos' β hβ) hu)
    exact ⟨b, K', hbpos, hK'pos, hmain⟩
  -- the constants are uniform over the finitely many opinions
  choose b k hbpos hkpos hmain using key
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ o : Opinion M, b o ≤ B := Finite.exists_le b
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, ∀ o : Opinion M, k o ≤ Kb := Finite.exists_le k
  refine ⟨max B 1, max Kb 1, min (min ((γ / 4) / 3) (1 / 2)) (γ / 4),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_min (lt_min (by positivity) (by norm_num)) hδpos, ?_⟩
  intro β hβ o u hu
  have hbβ : b o ≤ β := le_trans (hB o) (le_trans (le_max_left _ _) hβ)
  obtain ⟨h1, h2⟩ := hmain o β hbβ u hu
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le (hbpos o) hbβ
  have hfac : (0 : ℝ) ≤ β ^ 3 *
      Real.exp (-min (min ((γ / 4) / 3) (1 / 2)) (γ / 4) * β) := by positivity
  have hup : k o * β ^ 3 *
        Real.exp (-min (min ((γ / 4) / 3) (1 / 2)) (γ / 4) * β)
      ≤ max Kb 1 * β ^ 3 *
        Real.exp (-min (min ((γ / 4) / 3) (1 / 2)) (γ / 4) * β) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_trans (hKb o) (le_max_left _ _)) hfac
  exact ⟨fun t ht => le_trans (h1 t ht) hup, fun v hv => le_trans (h2 v hv) hup⟩

end PositiveBias

end Bias

end SocialNetwork
