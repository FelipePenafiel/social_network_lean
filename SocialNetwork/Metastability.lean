/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.ConsensusExit

/-!
# Theorem 3: metastability

Corollary 15 and Theorem 3 of arXiv:2607.19651, from Lemma 14
(`SocialNetwork.ConsensusExit`) and Proposition 12, which is Theorem 5.3 of [LM22] and which
Theorem 3 takes as a hypothesis.

## Main statements

* `SocialNetwork.le_characteristicTime` — **Corollary 15**.
* `SocialNetwork.ExitTimeApproxExponential` — **Proposition 12**, the citation of [LM22],
  stated and not proved.
* `SocialNetwork.metastability` — **Theorem 3**, assuming Proposition 12.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### Theorem 3: metastability -/

section Theorem3

variable [NeZero N] [NeZero M]

/-- The characteristic time `c_β` of Section 5.3: the time at which the probability of not
having left the consensus set for `o` equals `e^{-1}`.  The paper notes that by symmetry it
does not depend on which ladder `l ∈ L^o` the process starts from. -/
def IsCharacteristicTime (β : ℝ) (o : Opinion M) (c : ℝ) : Prop :=
  0 < c ∧ ∀ l : Pressure N M, IsLadder o l →
    probHittingGT β l (consensusSetOther N o) (ENNReal.ofReal c)
      = ENNReal.ofReal (Real.exp (-1))

/-- **Corollary 15.** `c_β ≥ (1/2) N^{-3} (M+1)^{-3} e^{β/(M-1)}`: the characteristic time
grows exponentially in `β`, which is what makes the exit asymptotically exponential. -/
theorem le_characteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {o : Opinion M}
    {c : ℝ} (hc : IsCharacteristicTime (N := N) β o c) :
    (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ * Real.exp (β / ((M : ℝ) - 1)) ≤ c := by
  obtain ⟨hcpos, hchar⟩ := hc
  have hKpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast Nat.mul_pos (Nat.pow_pos hN0) (Nat.pow_pos (Nat.succ_pos M))
  have h14 := le_probHittingGT_consensusOther hM hN hβ (isLadder_ladderOf (N := N) o) hcpos
  rw [hchar _ (isLadder_ladderOf (N := N) o)] at h14
  have h' := Real.exp_le_exp.mp
    ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h14)
  rw [neg_div, Real.exp_neg] at h'
  have hFpos : (0 : ℝ) < Real.exp (β / ((M : ℝ) - 1)) := Real.exp_pos _
  have key : (1 : ℝ) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) *
      (Real.exp (β / ((M : ℝ) - 1)))⁻¹ := by linarith
  have hFle : Real.exp (β / ((M : ℝ) - 1)) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right key hFpos.le
    rwa [one_mul, inv_mul_cancel_right₀ hFpos.ne'] at this
  have hKne : ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) ≠ 0 := hKpos.ne'
  have hstep := mul_le_mul_of_nonneg_left hFle
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹)
  rwa [show (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ *
    (2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) = c by field_simp] at hstep

omit [NeZero N] [NeZero M] in
/-- Hitting a larger set happens no later. -/
theorem hittingTimeCts_mono (u : Pressure N M) {θ₁ θ₂ : Set (Pressure N M)} (h : θ₁ ⊆ θ₂)
    (ω : ℕ → Step N M) : hittingTimeCts u θ₂ ω ≤ hittingTimeCts u θ₁ ω :=
  sInf_le_sInf (Set.image_mono fun _ ht => ⟨ht.1, h ht.2⟩)

/-! #### The four assumptions of Proposition 12, for this model

Section 5.3 of the paper checks (15)–(18) in half a page, with the constants
`s₁ = 1`, `ε₁ = 2N³(M+1)³e^{-β/(M-1)}`, `s₂ = 2β`, `ε₂ = (M+1)²N²e^{-β/((M+1)N)}`,
`δ = 1/((M+1)N)`, `C = K = 8e^{-1}(M+1)⁴N³` and `θ = 1/(2(M-1))`.  Each is one lemma here. -/

/-- `x e^{-x} ≤ e^{-1}`: the calculus fact behind the paper's
`sup_{β ≥ 0} β e^{-β/(2(M-1))} = 2e^{-1}(M-1)`, used for (17) and (18).

**Supplies a step the paper asserts**, which states the supremum without proof. -/
theorem mul_exp_neg_le_exp_neg_one (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h : x ≤ Real.exp (x - 1) := by have := Real.add_one_le_exp (x - 1); linarith
  calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- The scaled form: `β e^{-β/a} ≤ a e^{-1}` for `a > 0`. -/
theorem mul_exp_neg_div_le {a : ℝ} (ha : 0 < a) (β : ℝ) :
    β * Real.exp (-β / a) ≤ a * Real.exp (-1) := by
  have h := mul_exp_neg_le_exp_neg_one (β / a)
  have ha' : a ≠ 0 := ha.ne'
  have hmul := mul_le_mul_of_nonneg_left h ha.le
  rw [show a * (β / a * Real.exp (-(β / a))) = β * Real.exp (-(β / a)) by field_simp] at hmul
  rw [show -β / a = -(β / a) by ring]
  exact hmul

/-- Assumption **(16)** of Proposition 12, with `s₂ = 2β`.

The paper cites Lemma 13, which is about `L`, for a condition about `L^o ∪ C^{-o}`.
**Supplies a step the paper asserts**: the two are related by `L ⊆ L^o ∪ C^{-o}` — a ladder
for `p ≠ o` is a consensus state for `p` — so the hitting time of the larger set is smaller. -/
theorem probHittingGT_ladderOther_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (o : Opinion M) {u : Pressure N M} (hu : IsState u) :
    probHittingGT β u ({v | IsLadder o v} ∪ consensusSetOther N o) (ENNReal.ofReal (2 * β))
      ≤ ENNReal.ofReal ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) *
          Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))) := by
  refine le_trans (measure_mono fun ω hω => ?_) (probHittingGT_ladderSet_le hM hN hβ hu)
  have hsub : ladderSet N M ⊆ {v | IsLadder o v} ∪ consensusSetOther N o := by
    rintro v ⟨p, hp⟩
    by_cases hpo : p = o
    · exact Or.inl (hpo ▸ hp)
    · exact Or.inr ⟨p, hpo, hp.isConsensus hM (by omega)⟩
  exact lt_of_lt_of_le hω (hittingTimeCts_mono u hsub ω)

/-- Assumption **(15)** of Proposition 12, with `s₁ = 1` and `ε₁ = 2N³(M+1)³e^{-β/(M-1)}`.

Part 1 of Lemma 14 at `t = 1` bounds the probability of *not* having left, so the bound on
`ε₁` is the complementary event; `1 - e^{-x} ≤ x` turns the exponential into the linear form
the paper quotes. -/
theorem measure_hittingTime_le_one (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsLadder o l) :
    ctsPathMeasure β l
        {ω | hittingTimeCts l (consensusSetOther N o) ω ≤ ENNReal.ofReal 1}
      ≤ ENNReal.ofReal (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) *
          Real.exp (-β / ((M : ℝ) - 1))) := by
  set E : ℝ := Real.exp (-β / ((M : ℝ) - 1)) with hE
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hE0 : 0 < E := Real.exp_pos _
  have hx0 : 0 ≤ 2 * Kc * E := by positivity
  -- the event and its complement
  have hmeas : MeasurableSet {ω : ℕ → Step N M |
      ENNReal.ofReal 1 < hittingTimeCts l (consensusSetOther N o) ω} :=
    measurableSet_lt measurable_const (measurable_hittingTimeCts l _)
  have hcompl : {ω : ℕ → Step N M |
      hittingTimeCts l (consensusSetOther N o) ω ≤ ENNReal.ofReal 1}
      = {ω : ℕ → Step N M |
        ENNReal.ofReal 1 < hittingTimeCts l (consensusSetOther N o) ω}ᶜ := by
    ext ω; simp [not_lt]
  -- Lemma 14.1 at t = 1
  have h14 := le_probHittingGT_consensusOther hM hN hβ hl (t := 1) one_pos
  rw [show (-2 * (1 : ℝ) * Kc * E) = -(2 * Kc * E) by ring] at h14
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  refine le_trans (tsub_le_tsub_left h14 1) ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.add_one_le_exp (-(2 * Kc * E))
  linarith

/-- `e^{-β/a} ≤ a/β`, from `x ≤ e^x`.  Used to pin down a threshold `β₁` above which
`ε₁ + ε₂ ≤ 1/2`, the constraint the paper only asks to hold "for `β` sufficiently big". -/
theorem exp_neg_div_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : Real.exp (-β / a) ≤ a / β := by
  have hpos : 0 < β / a := div_pos hβ ha
  have h : β / a ≤ Real.exp (β / a) := by have := Real.add_one_le_exp (β / a); linarith
  have hinv : (Real.exp (β / a))⁻¹ ≤ (β / a)⁻¹ := inv_anti₀ hpos h
  rw [show -β / a = -(β / a) by ring, Real.exp_neg]
  rwa [inv_div] at hinv

/-- `1 ≤ 8 e^{-1}`, the only numeric fact the paper's constants rest on. -/
theorem one_le_eight_mul_exp_neg_one : (1 : ℝ) ≤ 8 * Real.exp (-1) := by
  have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 < 8 := lt_trans Real.exp_one_lt_three (by norm_num)
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ h2]
  linarith

omit [NeZero N] [NeZero M] in
/-- The size comparison behind the paper's constants: `N² M` and `(M+1)² N²` are both
dominated by `8 e^{-1} (M+1)⁴ N³`, with room to spare for the `(M-1)` term of (18). -/
theorem const_bounds (hM : 2 ≤ M) (hN : 3 ≤ N) :
    ((N ^ 2 * M : ℕ) : ℝ)
        + 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ)
    ∧ 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ)
    ∧ (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ)
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set e : ℝ := Real.exp (-1) with he'
  have he : (1 : ℝ) ≤ 8 * e := one_le_eight_mul_exp_neg_one
  have he0 : 0 < e := Real.exp_pos _
  have hP : (0 : ℝ) < (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by positivity
  have hcube : (M : ℝ) ≤ ((M : ℝ) + 1) ^ 3 := by
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ (M:ℝ)) 3, sq_nonneg (M:ℝ)]
  have hpow : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith
  have hdom : (N : ℝ) ^ 2 * (M : ℝ) ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by nlinarith
  have hsq : ((M : ℝ) + 1) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    have hsplit : 8 * e * ((M : ℝ) + 1) ^ 4 * (N : ℝ) ^ 3
        - 8 * e * ((N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3) * ((M : ℝ) - 1)
        = 16 * e * ((N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3) := by ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * e - 2) hP.le]
  · push_cast
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * e) hP.le)
      (by linarith : (0 : ℝ) ≤ 2)]
  · push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * e - 1) hP.le]

/-- Assumption **(18)** of Proposition 12, with `s₂ = 2β`, `θ = 1/(2(M-1))` and
`K = 8 e^{-1} (M+1)⁴ N³`.

Part 2 of Lemma 14 at `t = 2β` gives `(N²M + 4βN³(M+1)³) e^{-β/(M-1)}`; splitting the
exponent in half and absorbing `β e^{-β/(2(M-1))} ≤ 2(M-1)e^{-1}` is the paper's step (20). -/
theorem measure_hittingTime_le_two_mul (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {o : Opinion M} {u : Pressure N M} (hu : IsConsensus o u) :
    ctsPathMeasure β u
        {ω | hittingTimeCts u (consensusSetOther N o) ω ≤ ENNReal.ofReal (2 * β)}
      ≤ ENNReal.ofReal (8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) *
          Real.exp (-(1 / (2 * ((M : ℝ) - 1))) * β)) := by
  refine le_trans (probHittingLE_consensusOther_le hM hN hβ.le hu (by linarith : (0:ℝ) < 2 * β))
    (ENNReal.ofReal_le_ofReal ?_)
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  set a : ℝ := 2 * ((M : ℝ) - 1) with ha'
  have ha : 0 < a := by rw [ha']; linarith
  set E : ℝ := Real.exp (-β / a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  -- split the exponent in half
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hexpeq : -β / a + -β / a = -β / ((M : ℝ) - 1) := by
    rw [ha', ← add_div, div_eq_div_iff (ne_of_gt (by linarith : (0:ℝ) < 2 * ((M:ℝ) - 1)))
      (ne_of_gt hM1)]
    ring
  have hhalf : Real.exp (-β / ((M : ℝ) - 1)) = E * E := by
    rw [hE, ← Real.exp_add, hexpeq]
  have hgoal : Real.exp (-(1 / (2 * ((M : ℝ) - 1))) * β) = E := by
    rw [hE, ha', show -(1 / (2 * ((M : ℝ) - 1))) * β = -β / (2 * ((M : ℝ) - 1)) by ring]
  rw [hhalf, hgoal]
  -- absorb `β E ≤ a e^{-1}`
  have hβE : β * E ≤ a * Real.exp (-1) := mul_exp_neg_div_le ha β
  have hKc : (0 : ℝ) ≤ ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hNM : (0 : ℝ) ≤ ((N ^ 2 * M : ℕ) : ℝ) := by positivity
  have hstep : (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E
      ≤ ((N ^ 2 * M : ℕ) : ℝ)
        + 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1) := by
    have hexp : 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (β * E)
        ≤ 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (a * Real.exp (-1)) := by
      exact mul_le_mul_of_nonneg_left hβE (by linarith)
    rw [ha'] at hexp
    nlinarith [mul_le_mul_of_nonneg_left hE1 hNM]
  calc (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * (E * E)
      = ((((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E) * E := by
        ring
    _ ≤ (((N ^ 2 * M : ℕ) : ℝ)
        + 8 * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)) * E :=
        mul_le_mul_of_nonneg_right hstep hE0.le
    _ ≤ (8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ)) * E :=
        mul_le_mul_of_nonneg_right (const_bounds hM hN).1 hE0.le

/-- Assumption **(17)** of Proposition 12, with `s₂ = 2β`, `δ = 1/((M+1)N)` and
`C = 8 e^{-1} (M+1)⁴ N³`.

This is where Corollary 15 enters: it turns `s₂ / c_β` into `4β N³(M+1)³ e^{-β/(M-1)}`, and
step (20) of the paper absorbs the factor `β` into half of the exponent. -/
theorem max_le_of_isCharacteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {c : ℝ} (hc : IsCharacteristicTime (N := N) β o c) :
    max (2 * β / c) ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) *
        Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)))
      ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) *
          Real.exp (-(1 / (((M + 1) * N : ℕ) : ℝ)) * β) := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  set D : ℝ := (((M + 1) * N : ℕ) : ℝ) with hD
  have hDpos : 0 < D := by
    rw [hD]; exact_mod_cast Nat.mul_pos (Nat.succ_pos M) (by omega : 0 < N)
  set a : ℝ := 2 * ((M : ℝ) - 1) with ha'
  have ha : 0 < a := by rw [ha']; linarith
  set E : ℝ := Real.exp (-β / a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the target exponential, and the comparison `E ≤ e^{-β/D}`
  have hrw : -(1 / D) * β = -β / D := by ring
  have hDa : a ≤ D := by
    rw [ha', hD]; push_cast; nlinarith
  have hdd : β / D ≤ β / a := div_le_div_of_nonneg_left hβ ha hDa
  have hEle : E ≤ Real.exp (-β / D) := by
    rw [hE, Real.exp_le_exp, show -β / a = -(β / a) by ring, show -β / D = -(β / D) by ring]
    linarith
  have hEle' : E ≤ Real.exp (-(1 / D) * β) := by rwa [hrw]
  refine max_le ?_ ?_
  · -- (a) the `s₂ / c` half, through Corollary 15
    have hcpos : 0 < c := hc.1
    have h15' := le_characteristicTime hM hN hβ hc
    set F : ℝ := Real.exp (β / ((M : ℝ) - 1)) with hF
    have hFpos : 0 < F := Real.exp_pos _
    have hbpos : (0 : ℝ) < 1 / 2 * Kc⁻¹ * F := by positivity
    have hdiv : 2 * β / c ≤ 2 * β / (1 / 2 * Kc⁻¹ * F) :=
      div_le_div_of_nonneg_left (by linarith) hbpos h15'
    have hfe : 2 * β / (1 / 2 * Kc⁻¹ * F) = 4 * Kc * (β * E) * E := by
      have hexpeq : -β / a + -β / a = -β / ((M : ℝ) - 1) := by
        rw [ha', ← add_div,
          div_eq_div_iff (ne_of_gt (by linarith : (0:ℝ) < 2 * ((M:ℝ) - 1))) (ne_of_gt hM1)]
        ring
      have hEE : E * E = Real.exp (-β / ((M : ℝ) - 1)) := by
        rw [hE, ← Real.exp_add, hexpeq]
      rw [show 4 * Kc * (β * E) * E = 4 * Kc * β * (E * E) by ring, hEE,
        show -β / ((M : ℝ) - 1) = -(β / ((M : ℝ) - 1)) by ring, Real.exp_neg, ← hF]
      field_simp
      ring
    calc 2 * β / c ≤ 4 * Kc * (β * E) * E := hdiv.trans_eq hfe
      _ ≤ 4 * Kc * (a * Real.exp (-1)) * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_exp_neg_div_le ha β) (by positivity)) hE0.le
      _ = 8 * Real.exp (-1) * Kc * ((M : ℝ) - 1) * E := by rw [ha']; ring
      _ ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) * E :=
          mul_le_mul_of_nonneg_right (const_bounds hM hN).2.1 hE0.le
      _ ≤ 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / D) * β) :=
          mul_le_mul_of_nonneg_left hEle' (by positivity)
  · -- (b) the `ε₂` half: the exponentials already agree
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (const_bounds hM hN).2.2 (Real.exp_pos _).le

variable (N M) in
/-- **Proposition 12**, the consequence for this model of Theorem 5.3 of [LM22]: under the
four assumptions (15)–(18), the rescaled exit time from a consensus set is exponential up to
an error `K' β³ e^{-min(δ/3, 1/2, θ) β}`, and the mean exit time barely depends on the
starting state.

**This is an assumption, not a theorem.**  It is not a result of arXiv:2607.19651: the paper
derives it from Theorem 5.3 of [LM22], whose proof is a metastability argument for a general
time-homogeneous strong Markov process, and nothing in this repository proves it.  So it is
stated as a proposition, and Theorem 3 takes it as the hypothesis `hLM22`: the citation is
part of the statement of every result that uses it, and no result can use it without saying
so.

It is stated for *this* process on purpose.  Stated abstractly — for an arbitrary family of
measures and an arbitrary hitting time — it would be **false**: taking the zero measure with
an empty ladder set satisfies (15)–(18) vacuously while falsifying the conclusion at `t = 0`,
and a theorem assuming it would assume nothing it could use.  What rules that out is the
strong Markov property, which is exactly the content of [LM22] and is not expressible here.
So Theorem 31 needs its own twin for the biased process; one statement cannot serve both.

The four assumptions are marked with the equations of the paper.  Unlike the paper's
numbered display, `ε₁`, `ε₂`, `s₁` and `s₂` are *functions of* `β`: the proof of Theorem 3
instantiates them at `s₂ = 2β` and `ε₂ = (M+1)² N² e^{-β/((M+1)N)}`, and the constraint
`ε₁ + ε₂ ≤ 1/2` holds, in the paper's words, only "for `β` sufficiently big".  Bound as
constants ahead of `β`, as the paper's display reads, the hypotheses are unsatisfiable. -/
def ExitTimeApproxExponential : Prop :=
  2 ≤ M → 3 ≤ N → ∀ (o : Opinion M) (ε₁ ε₂ s₁ s₂ : ℝ → ℝ) {C δ K θ β₁ : ℝ},
    0 < C → 0 < δ → 0 < K → 0 < θ →
    (∀ β : ℝ, β₁ ≤ β → 0 < ε₁ β ∧ 0 < ε₂ β ∧ 0 < s₁ β ∧ 0 < s₂ β) →
    (∀ β : ℝ, β₁ ≤ β → ε₁ β + ε₂ β ≤ 1 / 2) →
    -- (15)
    (∀ β : ℝ, β₁ ≤ β → ∀ l : Pressure N M, IsLadder o l →
      ctsPathMeasure β l
          {ω | hittingTimeCts l (consensusSetOther N o) ω ≤ ENNReal.ofReal (s₁ β)}
        ≤ ENNReal.ofReal (ε₁ β)) →
    -- (16)
    (∀ β : ℝ, β₁ ≤ β → ∀ u : Pressure N M, IsState u →
      probHittingGT β u ({v | IsLadder o v} ∪ consensusSetOther N o)
          (ENNReal.ofReal (s₂ β))
        ≤ ENNReal.ofReal (ε₂ β)) →
    -- (17)
    (∀ β : ℝ, β₁ ≤ β → ∀ c : ℝ, IsCharacteristicTime (N := N) β o c →
      max (s₂ β / c) (ε₂ β) ≤ C * Real.exp (-δ * β)) →
    -- (18)
    (∀ β : ℝ, β₁ ≤ β → ∀ u : Pressure N M, IsConsensus o u →
      ctsPathMeasure β u
          {ω | hittingTimeCts u (consensusSetOther N o) ω ≤ ENNReal.ofReal (s₂ β)}
        ≤ ENNReal.ofReal (K * Real.exp (-θ * β))) →
    ∃ β₀ K' : ℝ, β₁ ≤ β₀ ∧ 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Pressure N M, IsConsensus o u →
      (∀ t : ℝ, 0 ≤ t →
        |(probHittingGT β u (consensusSetOther N o)
            (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)) ∧
      ∀ v : Pressure N M, IsConsensus o v →
        |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
            (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)

/-- **Theorem 3 (Metastability).** There are `β₀, C₁ > 0` and `C₂ ∈ (0, 1/2)`, depending only
on `M` and `N`, such that for `β ≥ β₀`, every opinion `o` and every consensus state `u ∈ C^o`,
the rescaled exit time from `C^o` is exponential of parameter one up to `C₁ β³ e^{-C₂ β}`, and
the mean exit times from two consensus states agree to the same order.

This is Proposition 12 applied with the bounds of Lemmas 13 and 14, and Proposition 12 is
the hypothesis `hLM22`: it is Theorem 5.3 of [LM22], which nothing in this repository proves
(`SocialNetwork.ExitTimeApproxExponential`). -/
theorem metastability (hM : 2 ≤ M) (hN : 3 ≤ N) (hLM22 : ExitTimeApproxExponential N M) :
    ∃ β₀ C₁ C₂ : ℝ, 0 < β₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧ C₂ < 1 / 2 ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ o : Opinion M, ∀ u : Pressure N M, IsConsensus o u →
        (∀ t : ℝ, 0 ≤ t →
          |(probHittingGT β u (consensusSetOther N o)
              (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
            - Real.exp (-t)| ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β)) ∧
        ∀ v : Pressure N M, IsConsensus o v →
          |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
              (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
            ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β) := by
  have hn : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hm : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hKcpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  have hQpos : (0 : ℝ) < (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (Nat.succ_pos M)) (Nat.pow_pos (by omega : 0 < N))
  have hDpos : (0 : ℝ) < (((M + 1) * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos M) (by omega : 0 < N)
  have hC4 : (0 : ℝ) < (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (Nat.succ_pos M)) (Nat.pow_pos (by omega : 0 < N))
  have hCpos : (0 : ℝ) < 8 * Real.exp (-1) * (((M + 1) ^ 4 * N ^ 3 : ℕ) : ℝ) := by positivity
  have hδpos : (0 : ℝ) < 1 / (((M + 1) * N : ℕ) : ℝ) := by positivity
  have hθpos : (0 : ℝ) < 1 / (2 * ((M : ℝ) - 1)) := by positivity
  -- the threshold above which `ε₁ + ε₂ ≤ 1/2`
  set β₁ : ℝ := max 1 (max (8 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1))
    (4 * (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * (((M + 1) * N : ℕ) : ℝ))) with hβ₁def
  have hβ₁one : (1 : ℝ) ≤ β₁ := le_max_left _ _
  have hpos' : ∀ β : ℝ, β₁ ≤ β → (0 : ℝ) < β := fun β hβ =>
    lt_of_lt_of_le zero_lt_one (le_trans hβ₁one hβ)
  have hsum : ∀ β : ℝ, β₁ ≤ β →
      2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))
        + (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))
      ≤ 1 / 2 := by
    intro β hβ
    have hβpos := hpos' β hβ
    have b1 : 8 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1) ≤ β :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hβ
    have b2 : 4 * (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * (((M + 1) * N : ℕ) : ℝ) ≤ β :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hβ
    have e1 : 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))
        ≤ 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (((M : ℝ) - 1) / β) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le hM1 hβpos) (by positivity)
    have e2 : (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ))
        ≤ (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * ((((M + 1) * N : ℕ) : ℝ) / β) :=
      mul_le_mul_of_nonneg_left (exp_neg_div_le hDpos hβpos) (by positivity)
    have f1 : 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (((M : ℝ) - 1) / β) ≤ 1 / 4 := by
      rw [show 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (((M : ℝ) - 1) / β)
          = (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((M : ℝ) - 1)) / β by ring,
        div_le_iff₀ hβpos]
      linarith
    have f2 : (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * ((((M + 1) * N : ℕ) : ℝ) / β) ≤ 1 / 4 := by
      rw [show (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * ((((M + 1) * N : ℕ) : ℝ) / β)
          = ((((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * (((M + 1) * N : ℕ) : ℝ)) / β by ring,
        div_le_iff₀ hβpos]
      linarith
    linarith
  -- Proposition 12, opinion by opinion
  have key : ∀ o : Opinion M, ∃ β₀ K' : ℝ, β₁ ≤ β₀ ∧ 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Pressure N M, IsConsensus o u →
      (∀ t : ℝ, 0 ≤ t →
        |(probHittingGT β u (consensusSetOther N o)
            (ENNReal.ofReal t * expHittingTimeCts β u (consensusSetOther N o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
            (1 / (2 * ((M : ℝ) - 1))) * β)) ∧
      ∀ v : Pressure N M, IsConsensus o v →
        |(expHittingTimeCts β u (consensusSetOther N o)).toReal /
            (expHittingTimeCts β v (consensusSetOther N o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
              (1 / (2 * ((M : ℝ) - 1))) * β) := by
    intro o
    exact hLM22 hM hN o
      (fun β => 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1)))
      (fun β => (((M + 1) ^ 2 * N ^ 2 : ℕ) : ℝ) * Real.exp (-β / (((M + 1) * N : ℕ) : ℝ)))
      (fun _ => 1) (fun β => 2 * β)
      hCpos hδpos hCpos hθpos
      (fun β hβ => ⟨by positivity, by positivity, one_pos, by linarith [hpos' β hβ]⟩)
      hsum
      (fun β hβ l hl => measure_hittingTime_le_one hM hN (hpos' β hβ).le hl)
      (fun β hβ u hu => probHittingGT_ladderOther_le hM hN (hpos' β hβ).le o hu)
      (fun β hβ c hc => max_le_of_isCharacteristicTime hM hN (hpos' β hβ).le hc)
      (fun β hβ u hu => measure_hittingTime_le_two_mul hM hN (hpos' β hβ) hu)
  choose b k hbβ₁ hbpos hkpos hmain using key
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ o : Opinion M, b o ≤ B := Finite.exists_le b
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, ∀ o : Opinion M, k o ≤ Kb := Finite.exists_le k
  refine ⟨max B 1, max Kb 1, min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
    (1 / (2 * ((M : ℝ) - 1))), lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), lt_min (lt_min (by positivity) (by norm_num))
    hθpos, ?_, ?_⟩
  · -- `C₂ < 1/2`, because `δ/3 = 1/(3(M+1)N) ≤ 1/27`
    refine lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) ?_
    have hD9 : (9 : ℝ) ≤ (((M + 1) * N : ℕ) : ℝ) := by push_cast; nlinarith
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3), one_div]
    rw [inv_lt_iff_one_lt_mul₀ hDpos]
    nlinarith
  · intro β hβ o u hu
    have hbβ : b o ≤ β := le_trans (hB o) (le_trans (le_max_left _ _) hβ)
    obtain ⟨h1, h2⟩ := hmain o β hbβ u hu
    have hfac : (0 : ℝ) ≤ β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3)
        (1 / 2)) (1 / (2 * ((M : ℝ) - 1))) * β) := by
      have : (0 : ℝ) < β := lt_of_lt_of_le (lt_of_lt_of_le (hbpos o) (le_refl _)) hbβ
      positivity
    have hup : k o * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
          (1 / (2 * ((M : ℝ) - 1))) * β)
        ≤ max Kb 1 * β ^ 3 * Real.exp (-min (min ((1 / (((M + 1) * N : ℕ) : ℝ)) / 3) (1 / 2))
          (1 / (2 * ((M : ℝ) - 1))) * β) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_trans (hKb o) (le_max_left _ _)) hfac
    exact ⟨fun t ht => le_trans (h1 t ht) hup, fun v hv => le_trans (h2 v hv) hup⟩

end Theorem3

end SocialNetwork
