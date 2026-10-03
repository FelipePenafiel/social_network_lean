/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedResults
import SocialNetwork.JumpHold

/-!
# Lemma 29: leaving a biased consensus set (Appendix C)

Both parts of Lemma 29 of arXiv:2607.19651, with the paper's constant
`2 N³ (M+1)³ e^{-βγ/2}`, for `0 < γ < 1/(M-1)`, that is `0 < α < 1/(M-1)`.

## Main statements

* `SocialNetwork.Bias.le_biasedProbHittingGT` — **Lemma 29.1**: from `L_α^o`, `C_α^{-o}` is not
  reached before `t` with probability at least `exp (-2 t N³ (M+1)³ e^{-βγ/2})`.
* `SocialNetwork.Bias.biasedProbHittingLE_le` — **Lemma 29.2**: from `C_α^o`, it is reached
  before `t` with probability at most `(N² M + 2 t N³ (M+1)³) e^{-βγ/2}`.

## The argument

Appendix C says that Lemma 29 "follows as the proof of Lemma 14".  It does, and this file is
`SocialNetwork.ConsensusExit` transposed, departures included: the first-step comparison in
place of Appendix B's conditioning, a block of `N` expressions, and no Theorem 1.1.  The greedy
event becomes the near-greedy one of Remark 7, so the gap `1/(M-1)` becomes the slack `γ/2`,
and Proposition 24 takes the place of Proposition 8.

Two steps have to be supplied, because the slack changes them.

* **A near-greedy expression from `C_α^o` expresses `o`.**  In `C_α^o` a positive pressure for
  `o` is at least `(1+γ)/2` (`SocialNetwork.Bias.IsBiasedConsensus.half_le_of_pos`): against
  each other opinion the row is ahead by a positive multiple of `1 + γ`, and the row sums of
  equation (6) are `(M-1) α nₐ ≥ 0`.  So the maximum is at least `(1+γ)/2 > γ/2`, and the
  non-positive pressures for the other opinions are out of reach.
* **A near-greedy run from such a set sweeps onto `L_α^o`** (`SocialNetwork.Bias.IsBiasedSweepable`).
  An actor that already expressed in the block carries at most `k - 1` at step `k`, one that has
  not carries at least `k`, and the slack `γ/2` is below `1`, so the `N` expressions come from
  `N` distinct actors, exactly as in Proposition 5.

The extended consensus set `Ĉ_α^o` (`SocialNetwork.Bias.IsBiasedExtendedConsensus`) is
Appendix B's `Ĉ^o` with the threshold for the other opinions lowered from `1` to `1 - γ/2`,
which is what a near-greedy expression needs; an expression of `p ≠ o` by the null row of
`L̂_α^o` lands in it, since it leaves the others at `1 - γ k ≤ 1 - γ` for `p`.

The biased process is `SocialNetwork.drivenMeasure` of its step law, so the restart at the first
jump is `SocialNetwork.map_drivenMeasure_firstRest`.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The sets of the comparison

The argument is that of `SocialNetwork.ConsensusExit`, with greedy expressions replaced by the
near-greedy ones of Remark 7.  Two facts make the replacement work.  In `C_α^o` a positive
pressure for `o` is at least `(1+γ)/2`, so a near-greedy expression expresses `o`; and an actor
that already expressed in a block carries at most `k - 1` when one that has not carries at least
`k`, a gap of `1 > γ/2`, so a near-greedy expression comes from an actor that has not. -/

section Sets

variable {γ : ℝ} {o : Opinion M}

/-- Appendix C's regime `0 < α` gives `γ < 1`. -/
theorem lt_one_of_lt_inv (hM : 2 ≤ M) (hγ' : γ < 1 / ((M : ℝ) - 1)) : γ < 1 := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  exact lt_of_lt_of_le hγ' (by rw [div_le_one (by linarith)]; exact hM1)

/-- In Appendix C's regime the row sums `(M-1) α nₐ` of equation (6) are non-negative. -/
theorem sum_pressure_nonneg (hM : 2 ≤ M) (hγ' : γ < 1 / ((M : ℝ) - 1)) (P : Profile N M)
    (a : Actor N) : 0 ≤ ∑ p, P.pressure γ a p := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hγM : ((M : ℝ) - 1) * γ ≤ 1 := by
    have := (lt_div_iff₀ hM1).1 hγ'
    linarith
  rw [sum_pressure]
  exact mul_nonneg (by linarith) (Nat.cast_nonneg _)

/-- In `C_α^o` some actor carries positive pressure for `o`: otherwise every row would be
non-positive with a non-negative sum, hence null. -/
theorem IsBiasedConsensus.exists_pos (hM : 2 ≤ M) (hγ' : γ < 1 / ((M : ℝ) - 1))
    {v : Profile N M} (hv : IsBiasedConsensus γ o v) : ∃ a, 0 < v.pressure γ a o := by
  by_contra hno
  push Not at hno
  obtain ⟨a, p, hap⟩ := hv.ne_zero
  have hle : ∀ q, v.pressure γ a q ≤ 0 := fun q => by
    by_cases hq : q = o
    · subst hq; exact hno a
    · exact hv.nonpos a q hq
  have hneg : v.pressure γ a p < 0 := lt_of_le_of_ne (hle p) hap
  have hsplit := Finset.add_sum_erase Finset.univ (fun q => v.pressure γ a q) (Finset.mem_univ p)
  have hrest : ∑ q ∈ Finset.univ.erase p, v.pressure γ a q ≤ 0 :=
    Finset.sum_nonpos fun q _ => hle q
  have hrow := sum_pressure_nonneg hM hγ' v a
  linarith

/-- In `C_α^o` a positive pressure for `o` is at least `(1+γ)/2`.  Against each other opinion
the row is ahead by a positive multiple of `1 + γ`, and the row sum is non-negative, so
`M u (a, o) ≥ (M-1)(1+γ)`. -/
theorem IsBiasedConsensus.half_le_of_pos (hM : 2 ≤ M) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) {v : Profile N M} (hv : IsBiasedConsensus γ o v)
    {a : Actor N} (ha : 0 < v.pressure γ a o) : (1 + γ) / 2 ≤ v.pressure γ a o := by
  set x := v.pressure γ a o with hx
  have hgap : ∀ p ∈ Finset.univ.erase o, 1 + γ ≤ x - v.pressure γ a p := by
    intro p hp
    have hpo := Finset.ne_of_mem_erase hp
    have hy := hv.nonpos a p hpo
    have hd : x - v.pressure γ a p
        = (((v a).count o : ℝ) - ((v a).count p : ℝ)) * (1 + γ) := by
      simp only [hx, Profile.pressure, Memory.pressure]; ring
    have hlt : (v a).count p < (v a).count o := by
      by_contra hle
      push Not at hle
      have h1 : ((v a).count o : ℝ) - ((v a).count p : ℝ) ≤ 0 := by
        have : ((v a).count o : ℝ) ≤ ((v a).count p : ℝ) := by exact_mod_cast hle
        linarith
      have h2 : x - v.pressure γ a p ≤ 0 := by
        rw [hd]; exact mul_nonpos_of_nonpos_of_nonneg h1 (by linarith)
      linarith
    have h1 : (1 : ℝ) ≤ ((v a).count o : ℝ) - ((v a).count p : ℝ) := by
      have h : (v a).count p + 1 ≤ (v a).count o := hlt
      have : ((v a).count p : ℝ) + 1 ≤ ((v a).count o : ℝ) := by exact_mod_cast h
      linarith
    rw [hd]
    nlinarith
  have hsum := Finset.sum_le_sum hgap
  rw [Finset.sum_const, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one] at hsum
  have hsplit := Finset.add_sum_erase Finset.univ (fun q => v.pressure γ a q) (Finset.mem_univ o)
  have hrow := sum_pressure_nonneg hM hγ' v a
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  -- `M x ≥ (M - 1)(1 + γ) ≥ M (1 + γ) / 2`
  have hMx : ((M : ℝ) - 1) * (1 + γ) ≤ (M : ℝ) * x := by
    linarith
  have h2 : (M : ℝ) * (1 + γ) ≤ 2 * ((M : ℝ) * x) := by nlinarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have h3 : (M : ℝ) * ((1 + γ) / 2) ≤ (M : ℝ) * x := by linarith
  exact le_of_mul_le_mul_left h3 hMpos

/-- In `C_α^o` some actor carries at least `(1+γ)/2` for `o`. -/
theorem IsBiasedConsensus.exists_half_le (hM : 2 ≤ M) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) {v : Profile N M} (hv : IsBiasedConsensus γ o v) :
    ∃ a, (1 + γ) / 2 ≤ v.pressure γ a o := by
  obtain ⟨a, ha⟩ := hv.exists_pos hM hγ'
  exact ⟨a, hv.half_le_of_pos hM hγ hγ' ha⟩

/-- In `C_α^o` a near-greedy expression expresses `o`. -/
theorem IsBiasedConsensus.opinion_eq_of_nearGreedy (hM : 2 ≤ M) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) {v : Profile N M} (hv : IsBiasedConsensus γ o v)
    {b : Actor N} {p : Opinion M}
    (h : ∀ a q, v.pressure γ a q - γ / 2 < v.pressure γ b p) : p = o := by
  by_contra hp
  obtain ⟨a, ha⟩ := hv.exists_half_le hM hγ hγ'
  have h1 := h a o
  have h2 := hv.nonpos b p hp
  linarith

/-- Expressing `o` keeps a state in `C_α^o`. -/
theorem IsBiasedConsensus.express (hN : 2 ≤ N) (hγ : 0 < γ) {v : Profile N M}
    (hv : IsBiasedConsensus γ o v) (a : Actor N) :
    IsBiasedConsensus γ o (Profile.express a o v) := by
  obtain ⟨b, hb⟩ : ∃ b : Actor N, b ≠ a := by
    have hcard : 1 < Fintype.card (Actor N) := by simp only [Fintype.card_fin]; omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  refine ⟨hv.isBiasedState.express a o, ⟨b, o, ?_⟩, fun c => ?_, fun c q hq => ?_⟩
  · rw [Profile.pressure_express, if_neg hb, if_pos rfl]
    have := hv.nonneg b
    exact ne_of_gt (by linarith)
  · rw [Profile.pressure_express, if_pos rfl]
    split_ifs
    · exact le_rfl
    · have := hv.nonneg c; linarith
  · rw [Profile.pressure_express]
    split_ifs
    · exact le_rfl
    · have := hv.nonpos c q hq; linarith

/-- `C_α^o` avoids `C_α^{-o}`. -/
theorem IsBiasedConsensus.notMem (hM : 2 ≤ M) (hγ' : γ < 1 / ((M : ℝ) - 1))
    {v : Profile N M} (hv : IsBiasedConsensus γ o v) : v ∉ biasedConsensusSetOther N γ o := by
  rintro ⟨p, hpo, hp⟩
  obtain ⟨a, ha⟩ := hv.exists_pos hM hγ'
  have := hp.nonpos a o (Ne.symm hpo)
  linarith

/-- The extended consensus set `Ĉ_α^o` of Appendix C, in which a block opened from `L̂_α^o`
starts: the `o`-column is non-negative, some actor carries at least `1` for `o`, and every
pressure for another opinion is below `1 - γ/2`. -/
structure IsBiasedExtendedConsensus (γ : ℝ) (o : Opinion M) (v : Profile N M) : Prop where
  isBiasedState : IsBiasedState v
  nonneg : ∀ a, 0 ≤ v.pressure γ a o
  exists_ge : ∃ b, 1 ≤ v.pressure γ b o
  lt : ∀ a, ∀ p ≠ o, v.pressure γ a p < 1 - γ / 2

/-- In `Ĉ_α^o` a near-greedy expression expresses `o`. -/
theorem IsBiasedExtendedConsensus.opinion_eq_of_nearGreedy {v : Profile N M}
    (hv : IsBiasedExtendedConsensus γ o v) {b : Actor N} {p : Opinion M}
    (h : ∀ a q, v.pressure γ a q - γ / 2 < v.pressure γ b p) : p = o := by
  by_contra hp
  obtain ⟨c, hc⟩ := hv.exists_ge
  have h1 := h c o
  have h2 := hv.lt b p hp
  linarith

/-- Expressing `o` keeps a state in `Ĉ_α^o`. -/
theorem IsBiasedExtendedConsensus.express (hN : 2 ≤ N) (hγ : 0 < γ) (hγ2 : γ < 2)
    {v : Profile N M} (hv : IsBiasedExtendedConsensus γ o v) (a : Actor N) :
    IsBiasedExtendedConsensus γ o (Profile.express a o v) := by
  obtain ⟨b, hb⟩ : ∃ b : Actor N, b ≠ a := by
    have hcard : 1 < Fintype.card (Actor N) := by simp only [Fintype.card_fin]; omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  refine ⟨hv.isBiasedState.express a o, fun c => ?_, ⟨b, ?_⟩, fun c q hq => ?_⟩
  · rw [Profile.pressure_express, if_pos rfl]
    split_ifs
    · exact le_rfl
    · have := hv.nonneg c; linarith
  · rw [Profile.pressure_express, if_neg hb, if_pos rfl]
    have := hv.nonneg b
    linarith
  · rw [Profile.pressure_express]
    split_ifs
    · linarith
    · have := hv.lt c q hq; linarith

/-- `Ĉ_α^o` avoids `C_α^{-o}`. -/
theorem IsBiasedExtendedConsensus.notMem {v : Profile N M}
    (hv : IsBiasedExtendedConsensus γ o v) : v ∉ biasedConsensusSetOther N γ o := by
  rintro ⟨p, hpo, hp⟩
  obtain ⟨b, hb⟩ := hv.exists_ge
  have := hp.nonpos b o (Ne.symm hpo)
  linarith

/-- In `L̂_α^o` every actor but the null one carries at least `1` for `o`. -/
theorem IsBiasedSteepLadder.one_le {v : Profile N M} (hv : IsBiasedSteepLadder γ o v)
    {a b : Actor N} (ha : v.pressure γ a o = 0) (hb : b ≠ a) : 1 ≤ v.pressure γ b o := by
  obtain ⟨k, hk⟩ := hv.isInt b
  have hne : v.pressure γ b o ≠ 0 := fun h => hb (hv.injective (by simp only; rw [h, ha]))
  have hpos : 0 < v.pressure γ b o := lt_of_le_of_ne (hv.nonneg b) (Ne.symm hne)
  rw [hk] at hpos ⊢
  have : (0 : ℤ) < k := by exact_mod_cast hpos
  have : (1 : ℤ) ≤ k := this
  exact_mod_cast this

/-- `L̂_α^o` avoids `C_α^{-o}`: its `o`-column has a positive entry. -/
theorem IsBiasedSteepLadder.notMem (hN : 2 ≤ N) {v : Profile N M}
    (hv : IsBiasedSteepLadder γ o v) : v ∉ biasedConsensusSetOther N γ o := by
  rintro ⟨p, hpo, hp⟩
  obtain ⟨a, ha⟩ := hv.exists_zero
  obtain ⟨b, hb⟩ : ∃ b : Actor N, b ≠ a := by
    have hcard : 1 < Fintype.card (Actor N) := by simp only [Fintype.card_fin]; omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  have h1 := hv.one_le ha hb
  have h2 := hp.nonpos b o (Ne.symm hpo)
  linarith

/-- In `L̂_α^o` only the null row carries a non-negative pressure for another opinion. -/
theorem IsBiasedSteepLadder.eq_zero_of_nonneg (hγ : 0 < γ) {v : Profile N M}
    (hv : IsBiasedSteepLadder γ o v) {a : Actor N} {p : Opinion M} (hp : p ≠ o)
    (h : 0 ≤ v.pressure γ a p) : v.pressure γ a o = 0 := by
  have h1 := hv.other a p hp
  have h2 := hv.nonneg a
  nlinarith

/-- In `L̂_α^o` every pressure for another opinion is non-positive. -/
theorem IsBiasedSteepLadder.nonpos (hγ : 0 < γ) {v : Profile N M}
    (hv : IsBiasedSteepLadder γ o v) (a : Actor N) {p : Opinion M} (hp : p ≠ o) :
    v.pressure γ a p ≤ 0 := by
  have h1 := hv.other a p hp
  have h2 := hv.nonneg a
  nlinarith

/-- In `L̂_α^o` a negative pressure is at most `-γ`: it is `-γ` times a positive integer. -/
theorem IsBiasedSteepLadder.le_neg_of_neg (hγ : 0 < γ) {v : Profile N M}
    (hv : IsBiasedSteepLadder γ o v) {a : Actor N} {p : Opinion M}
    (h : v.pressure γ a p < 0) : v.pressure γ a p ≤ -γ := by
  have hp : p ≠ o := by
    rintro rfl
    exact absurd (hv.nonneg a) (not_le.2 h)
  obtain ⟨k, hk⟩ := hv.isInt a
  rw [hv.other a p hp, hk] at h ⊢
  have hk0 : (0 : ℝ) < (k : ℝ) := by nlinarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : (0 : ℤ) < k := by exact_mod_cast hk0
    exact_mod_cast (show (1 : ℤ) ≤ k from this)
  nlinarith

/-- Expressing `o` keeps a state in `L̂_α^o`. -/
theorem IsBiasedSteepLadder.express_self {v : Profile N M} (hv : IsBiasedSteepLadder γ o v)
    (a : Actor N) : IsBiasedSteepLadder γ o (Profile.express a o v) := by
  have hval : ∀ b, (Profile.express a o v).pressure γ b o
      = if b = a then 0 else v.pressure γ b o + 1 := fun b => by
    rw [Profile.pressure_express, if_pos rfl]
  refine ⟨hv.isBiasedState.express a o, fun b => ?_, fun b c hbc => ?_, ⟨a, ?_⟩,
    fun b => ?_, fun b p hp => ?_⟩
  · rw [hval]
    split_ifs
    · exact ⟨0, by simp⟩
    · obtain ⟨k, hk⟩ := hv.isInt b
      exact ⟨k + 1, by rw [hk]; push_cast; ring⟩
  · simp only [hval] at hbc
    have hb0 := hv.nonneg b
    have hc0 := hv.nonneg c
    split_ifs at hbc with hb hc hc
    · rw [hb, hc]
    · linarith
    · linarith
    · exact hv.injective (show v.pressure γ b o = v.pressure γ c o by linarith)
  · rw [hval, if_pos rfl]
  · rw [hval]
    split_ifs
    · exact le_rfl
    · have := hv.nonneg b; linarith
  · rw [Profile.pressure_express, hval, if_neg hp]
    split_ifs
    · ring
    · rw [hv.other b p hp]; ring

/-- **Leaving `L̂_α^o` without a negative expression lands in `Ĉ_α^o`.**  The actor with the
null row expresses `p ≠ o`: it is reset; the others carry positive integers `k` for `o`, which
become `k - γ ≥ 1 - γ ≥ 0`, and `-γ k` for `p`, which becomes `1 - γ k ≤ 1 - γ`.  With `N ≥ 3`
two other actors carry distinct positive integers for `o`, so one still carries `2 - γ ≥ 1`.

**Supplies a step the paper asserts**: Appendix C transports Appendix B, which says the
expression "leads the process to `Ĉ^o`" and stops there. -/
theorem IsBiasedSteepLadder.express_isBiasedExtendedConsensus (hN : 3 ≤ N) (hγ : 0 < γ)
    (hγ1 : γ < 1) {v : Profile N M} (hv : IsBiasedSteepLadder γ o v) {a : Actor N}
    (ha : v.pressure γ a o = 0) {p : Opinion M} (hp : p ≠ o) :
    IsBiasedExtendedConsensus γ o (Profile.express a p v) := by
  have hop : o ≠ p := Ne.symm hp
  have hval : ∀ b, b ≠ a → (Profile.express a p v).pressure γ b o = v.pressure γ b o - γ :=
    fun b hb => by rw [Profile.pressure_express, if_neg hb, if_neg hop]; ring
  refine ⟨hv.isBiasedState.express a p, fun b => ?_, ?_, fun b q hq => ?_⟩
  · by_cases hb : b = a
    · rw [Profile.pressure_express, if_pos hb]
    · rw [hval b hb]
      have := hv.one_le ha hb
      linarith
  · obtain ⟨b, hb, c, hc, hbc⟩ : ∃ b, b ≠ a ∧ ∃ c, c ≠ a ∧ b ≠ c := by
      have hcard : 1 < (Finset.univ.erase a).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨b, hbm, c, hcm, hbc⟩ := Finset.one_lt_card.1 hcard
      exact ⟨b, Finset.ne_of_mem_erase hbm, c, Finset.ne_of_mem_erase hcm, hbc⟩
    obtain ⟨kb, hkb⟩ := hv.isInt b
    obtain ⟨kc, hkc⟩ := hv.isInt c
    have hb1 := hv.one_le ha hb
    have hc1 := hv.one_le ha hc
    have hne : v.pressure γ b o ≠ v.pressure γ c o := fun h => hbc (hv.injective h)
    rw [hkb] at hb1 hne
    rw [hkc] at hc1 hne
    have hkb1 : (1 : ℤ) ≤ kb := by exact_mod_cast hb1
    have hkc1 : (1 : ℤ) ≤ kc := by exact_mod_cast hc1
    have hkne : kb ≠ kc := fun h => hne (by rw [h])
    have hbig : (2 : ℤ) ≤ kb ∨ (2 : ℤ) ≤ kc := by omega
    rcases hbig with h | h
    · refine ⟨b, ?_⟩
      rw [hval b hb, hkb]
      have : (2 : ℝ) ≤ (kb : ℝ) := by exact_mod_cast h
      linarith
    · refine ⟨c, ?_⟩
      rw [hval c hc, hkc]
      have : (2 : ℝ) ≤ (kc : ℝ) := by exact_mod_cast h
      linarith
  · by_cases hb : b = a
    · rw [Profile.pressure_express, if_pos hb]
      linarith
    · have h1 := hv.one_le ha hb
      have h2 := hv.other b q hq
      rw [Profile.pressure_express, if_neg hb]
      split_ifs with hqp
      · rw [h2]; nlinarith
      · rw [h2]; nlinarith

end Sets

/-! ### The last stage of Proposition 7, with near-greedy expressions

`SocialNetwork.IsSweepable` for the biased model: a set in which a near-greedy expression
expresses `o`, preserved by expressing `o`.  From such a set `N` near-greedy expressions land
on `L_α^o`, because they come from `N` distinct actors. -/

section Sweep

/-- A set of profiles from which `N` near-greedy expressions sweep onto `L_α^o`. -/
structure IsBiasedSweepable (γ : ℝ) (P : Profile N M → Prop) (o : Opinion M) : Prop where
  isBiasedState : ∀ ⦃v⦄, P v → IsBiasedState v
  nonneg : ∀ ⦃v⦄, P v → ∀ a, 0 ≤ v.pressure γ a o
  opinion_eq : ∀ ⦃v⦄, P v → ∀ ⦃b : Actor N⦄ ⦃p : Opinion M⦄,
    (∀ a q, v.pressure γ a q - γ / 2 < v.pressure γ b p) → p = o
  express : ∀ ⦃v⦄, P v → ∀ a, P (Profile.express a o v)

/-- Hearing `k` expressions of `o` from others moves the row by `+k` on `o` and `-γ k`
elsewhere. -/
theorem pressure_stateAfter_add_of_hearing (γ : ℝ) (u : Profile N M) (ω : ℕ → Jump N M)
    (b : Actor N) (o : Opinion M) (m k : ℕ)
    (hne : ∀ i, m ≤ i → i < m + k → (ω i).1 ≠ b)
    (hop : ∀ i, m ≤ i → i < m + k → (ω i).2 = o) :
    (stateAfter u ω (m + k)).pressure γ b o = (stateAfter u ω m).pressure γ b o + k ∧
      ∀ p, p ≠ o →
        (stateAfter u ω (m + k)).pressure γ b p = (stateAfter u ω m).pressure γ b p - γ * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun i h1 h2 => hne i h1 (by omega))
        (fun i h1 h2 => hop i h1 (by omega))
      have hb : b ≠ (ω (m + k)).1 := Ne.symm (hne (m + k) (by omega) (by omega))
      have ho : (ω (m + k)).2 = o := hop (m + k) (by omega) (by omega)
      rw [show m + (k + 1) = m + k + 1 by ring, stateAfter_succ]
      refine ⟨?_, fun p hp => ?_⟩
      · rw [Profile.pressure_express, if_neg hb, if_pos ho.symm, ih1]; push_cast; ring
      · rw [Profile.pressure_express, if_neg hb, if_neg (fun h => hp (h.trans ho)), ih2 p hp]
        push_cast; ring

namespace IsBiasedSweepable

variable {γ : ℝ} {P : Profile N M → Prop} {o : Opinion M} {v : Profile N M}
  {ω : ℕ → Jump N M}

/-- `P` is preserved along a near-greedy run. -/
theorem state (hP : IsBiasedSweepable γ P o) (hv : P v) {m : ℕ}
    (hg : ∀ k, k < m → IsNearGreedyAt γ v ω k) : ∀ k, k ≤ m → P (stateAfter v ω k) := by
  intro k
  induction k with
  | zero => intro _; exact hv
  | succ k ih =>
      intro hk
      have hck := ih (by omega)
      have hop : (ω k).2 = o := hP.opinion_eq hck (hg k (by omega))
      rw [stateAfter_succ, hop]
      exact hP.express hck _

/-- Every expression of a near-greedy run expresses `o`. -/
theorem opinion_eq_of_nearGreedy (hP : IsBiasedSweepable γ P o) (hv : P v) {m : ℕ}
    (hg : ∀ k, k < m → IsNearGreedyAt γ v ω k) {k : ℕ} (hk : k < m) : (ω k).2 = o :=
  hP.opinion_eq (hP.state hv hg k hk.le) (hg k hk)

/-- No actor expresses twice among the first `N` expressions of a near-greedy run: one that
already expressed carries at most `k - 1` at step `k`, one that has not carries at least `k`,
and the slack `γ/2` is below `1`. -/
theorem actor_ne_actor (hγ : 0 < γ) (hγ2 : γ < 2) (hP : IsBiasedSweepable γ P o) (hv : P v)
    (hg : ∀ k, k < N → IsNearGreedyAt γ v ω k) {j k : ℕ} (hjk : j < k) (hk : k < N) :
    (ω j).1 ≠ (ω k).1 := by
  intro hEq
  have hop : ∀ l, l < N → (ω l).2 = o := fun l hl => hP.opinion_eq_of_nearGreedy hv hg hl
  -- an actor that has not expressed before step `k`
  obtain ⟨b, hb⟩ : ∃ b : Actor N, ∀ i, i < k → (ω i).1 ≠ b := by
    have hex : ∃ b : Actor N, b ∉ (Finset.range k).image fun i => (ω i).1 := by
      by_contra hno
      have hsub : (Finset.univ : Finset (Actor N))
          ⊆ (Finset.range k).image fun i => (ω i).1 := by
        intro c _
        by_contra hc
        exact hno ⟨c, hc⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := Finset.range k) (f := fun i => (ω i).1)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      rw [Finset.card_range] at h2
      omega
    obtain ⟨b, hbmem⟩ := hex
    exact ⟨b, fun i hi hEq' => hbmem (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, hEq'⟩)⟩
  -- `b` has heard `k` expressions of `o`
  obtain ⟨hb1, -⟩ := pressure_stateAfter_add_of_hearing γ v ω b o 0 k
    (fun i _ h2 => hb i (by omega)) (fun i _ h2 => hop i (by omega))
  rw [Nat.zero_add, stateAfter_zero] at hb1
  have hbge : (k : ℝ) ≤ (stateAfter v ω k).pressure γ b o := by
    rw [hb1]; have := hP.nonneg hv b; linarith
  -- the actor expressing at step `k` expressed already at step `j`
  have h0 := heard_stateAfter_expressed v ω j
  have h1 := heard_stateAfter_le v ω (ω j).1 (j + 1) (k - j - 1)
  rw [h0, Nat.zero_add, show j + 1 + (k - j - 1) = k by omega, hEq] at h1
  have hsmall : (stateAfter v ω k).pressure γ (ω k).1 (ω k).2 ≤ ((k - j - 1 : ℕ) : ℝ) :=
    le_trans (Profile.pressure_le_heard hγ _ _ _) (by exact_mod_cast h1)
  have hcast : ((k - j - 1 : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
    have h1k : 1 ≤ k := by omega
    have : (k - j - 1 : ℕ) ≤ k - 1 := by omega
    have h' : ((k - j - 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast this
    rwa [Nat.cast_sub h1k, Nat.cast_one] at h'
  have hgk := hg k hk b o
  linarith

/-- **The last stage of Proposition 7, with near-greedy expressions.**  `N` near-greedy
expressions from a state of `P` land on `L_α^o`. -/
theorem isBiasedLadder_stateAfter (hγ : 0 < γ) (hγ2 : γ < 2) (hP : IsBiasedSweepable γ P o)
    (hv : P v) (hg : ∀ k, k < N → IsNearGreedyAt γ v ω k) :
    IsBiasedLadder γ o (stateAfter v ω N) := by
  have hop : ∀ l, l < N → (ω l).2 = o := fun l hl => hP.opinion_eq_of_nearGreedy hv hg hl
  have hdist : ∀ j k, j < k → k < N → (ω j).1 ≠ (ω k).1 := fun _ _ hjk hk =>
    hP.actor_ne_actor hγ hγ2 hv hg hjk hk
  have hfinj : Function.Injective fun i : Fin N => (ω (i : ℕ)).1 := by
    intro i j hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact absurd hij (hdist _ _ h j.isLt)
    · exact Fin.val_injective h
    · exact absurd hij.symm (hdist _ _ h i.isLt)
  -- the row of the actor that expressed at step `i`, read at step `N`
  have hval : ∀ i : Fin N,
      (stateAfter v ω N).pressure γ (ω (i : ℕ)).1 o = ((N - 1 - (i : ℕ) : ℕ) : ℝ) ∧
        ∀ p, p ≠ o → (stateAfter v ω N).pressure γ (ω (i : ℕ)).1 p
          = -γ * ((N - 1 - (i : ℕ) : ℕ) : ℝ) := by
    intro i
    have hiN := i.isLt
    have hzero : ∀ p, (stateAfter v ω ((i : ℕ) + 1)).pressure γ (ω (i : ℕ)).1 p = 0 := by
      intro p
      rw [stateAfter_succ, Profile.pressure_express, if_pos rfl]
    obtain ⟨h1, h2⟩ := pressure_stateAfter_add_of_hearing γ v ω (ω (i : ℕ)).1 o ((i : ℕ) + 1)
      (N - 1 - (i : ℕ))
      (fun l hl1 hl2 => (hdist (i : ℕ) l (by omega) (by omega)).symm)
      (fun l hl1 hl2 => hop l (by omega))
    rw [show (i : ℕ) + 1 + (N - 1 - (i : ℕ)) = N by omega] at h1 h2
    exact ⟨by rw [h1, hzero o, zero_add], fun p hp => by rw [h2 p hp, hzero p]; ring⟩
  have hsurj : ∀ a : Actor N, ∃ i : Fin N, (ω (i : ℕ)).1 = a := fun a =>
    Finite.surjective_of_injective hfinj a
  refine ⟨isBiasedState_stateAfter (hP.isBiasedState hv) ω N, ?_, ?_⟩
  · ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨i, hi⟩ := hsurj a
      have hiN := i.isLt
      refine ⟨⟨N - 1 - (i : ℕ), by omega⟩, ?_⟩
      rw [← ha, ← hi, (hval i).1]
    · rintro ⟨j, hj⟩
      have hjN := j.isLt
      have hlt : N - 1 - (j : ℕ) < N := by omega
      refine ⟨(ω (N - 1 - (j : ℕ))).1, ?_⟩
      have h1 := (hval ⟨N - 1 - (j : ℕ), hlt⟩).1
      simp only at h1
      rw [h1, show N - 1 - (N - 1 - (j : ℕ)) = (j : ℕ) by omega, hj]
  · intro a p hp
    obtain ⟨i, hi⟩ := hsurj a
    rw [← hi, (hval i).1, (hval i).2 p hp]

end IsBiasedSweepable

variable {γ : ℝ} {o : Opinion M}

/-- `Ĉ_α^o` is sweepable. -/
theorem isBiasedSweepable_extendedConsensus (hN : 2 ≤ N) (hγ : 0 < γ) (hγ2 : γ < 2)
    (o : Opinion M) : IsBiasedSweepable γ (IsBiasedExtendedConsensus (N := N) γ o) o :=
  ⟨fun _ hv => hv.isBiasedState, fun _ hv => hv.nonneg,
    fun _ hv _ _ h => hv.opinion_eq_of_nearGreedy h, fun _ hv a => hv.express hN hγ hγ2 a⟩

/-- `C_α^o` is sweepable. -/
theorem isBiasedSweepable_consensus (hM : 2 ≤ M) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (o : Opinion M) :
    IsBiasedSweepable γ (IsBiasedConsensus (N := N) γ o) o :=
  ⟨fun _ hv => hv.isBiasedState, fun _ hv => hv.nonneg,
    fun _ hv _ _ h => hv.opinion_eq_of_nearGreedy hM hγ hγ' h, fun _ hv a => hv.express hN hγ a⟩

end Sweep

/-! ### Prepending an expression to a realisation -/

section Cons

/-- The realisation that expresses `x` first and then runs `ω`. -/
def consPath (x : Jump N M) (ω : ℕ → Jump N M) : ℕ → Jump N M
  | 0 => x
  | k + 1 => ω k

theorem stateAfter_consPath_succ (u : Profile N M) (x : Jump N M) (ω : ℕ → Jump N M) (k : ℕ) :
    stateAfter u (consPath x ω) (k + 1) = stateAfter (Profile.express x.1 x.2 u) ω k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stateAfter_succ, ih, stateAfter_succ]; rfl

theorem isNearGreedyAt_consPath_zero (γ : ℝ) (u : Profile N M) (x : Jump N M)
    (ω : ℕ → Jump N M) :
    IsNearGreedyAt γ u (consPath x ω) 0 ↔ ∀ a q, u.pressure γ a q - γ / 2 < u.pressure γ x.1 x.2 :=
  Iff.rfl

theorem isNearGreedyAt_consPath_succ (γ : ℝ) (u : Profile N M) (x : Jump N M)
    (ω : ℕ → Jump N M) (k : ℕ) :
    IsNearGreedyAt γ u (consPath x ω) (k + 1) ↔
      IsNearGreedyAt γ (Profile.express x.1 x.2 u) ω k := by
  unfold IsNearGreedyAt
  rw [stateAfter_consPath_succ]
  rfl

end Cons

/-! ### The invariant carried along the comparison

As in `SocialNetwork.ConsensusExit`: phase `0` is `L̂_α^o`, and an expression of `p ≠ o` by the
null row opens a block of `N` expressions, phases `N, N - 1, …, 1`, through which every
expression has to be near-greedy. -/

section Invariant

variable {γ : ℝ} {o : Opinion M}

/-- The invariant of the phase-`j` profiles. -/
def BiasedExitInv (γ : ℝ) (o : Opinion M) (v : Profile N M) : ℕ → Prop
  | 0 => IsBiasedSteepLadder γ o v
  | j + 1 => (IsBiasedExtendedConsensus γ o v ∨ IsBiasedConsensus γ o v) ∧
      ∀ ω : ℕ → Jump N M, (∀ k, k < j + 1 → IsNearGreedyAt γ v ω k) →
        IsBiasedSteepLadder γ o (stateAfter v ω (j + 1))

theorem BiasedExitInv.notMem (hM : 2 ≤ M) (hN : 2 ≤ N) (hγ' : γ < 1 / ((M : ℝ) - 1))
    {v : Profile N M} {j : ℕ} (h : BiasedExitInv γ o v j) :
    v ∉ biasedConsensusSetOther N γ o := by
  cases j with
  | zero => exact IsBiasedSteepLadder.notMem hN h
  | succ j => exact h.1.elim (fun h => h.notMem) fun h => h.notMem hM hγ'

/-- The block phases, for a phase given as a variable. -/
theorem biasedExitInv_of_pos {v : Profile N M} {k : ℕ} (hk : 0 < k)
    (hset : IsBiasedExtendedConsensus γ o v ∨ IsBiasedConsensus γ o v)
    (hrun : ∀ ω : ℕ → Jump N M, (∀ i, i < k → IsNearGreedyAt γ v ω i) →
      IsBiasedSteepLadder γ o (stateAfter v ω k)) : BiasedExitInv γ o v k := by
  cases k with
  | zero => omega
  | succ j => exact ⟨hset, hrun⟩

/-- A biased ladder is in phase `0`. -/
theorem biasedExitInv_zero_of_isBiasedLadder [NeZero N] {v : Profile N M}
    (hv : IsBiasedLadder γ o v) : BiasedExitInv γ o v 0 :=
  hv.isBiasedSteepLadder

/-- A biased consensus state is in phase `N`. -/
theorem biasedExitInv_of_isBiasedConsensus (hM : 2 ≤ M) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) {v : Profile N M} (hv : IsBiasedConsensus γ o v) :
    BiasedExitInv γ o v N := by
  have : NeZero N := ⟨by omega⟩
  have hγ2 : γ < 2 := by linarith [lt_one_of_lt_inv hM hγ']
  exact biasedExitInv_of_pos (by omega) (Or.inr hv) fun ω hω =>
    ((isBiasedSweepable_consensus hM hN hγ hγ' o).isBiasedLadder_stateAfter hγ hγ2 hv
      hω).isBiasedSteepLadder

/-- In phase `0`, an expression of `o` stays in phase `0`. -/
theorem BiasedExitInv.express_self {v : Profile N M} (hv : BiasedExitInv γ o v 0)
    (a : Actor N) : BiasedExitInv γ o (Profile.express a o v) 0 :=
  IsBiasedSteepLadder.express_self hv a

/-- In phase `0`, an expression of `p ≠ o` against a non-negative pressure opens a block. -/
theorem BiasedExitInv.express_other [NeZero N] (hM : 2 ≤ M) (hN : 3 ≤ N) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) {v : Profile N M} (hv : BiasedExitInv γ o v 0)
    {a : Actor N} {p : Opinion M} (hp : p ≠ o) (h : 0 ≤ v.pressure γ a p) :
    BiasedExitInv γ o (Profile.express a p v) N := by
  have hv' : IsBiasedSteepLadder γ o v := hv
  have hγ1 := lt_one_of_lt_inv hM hγ'
  have hext := hv'.express_isBiasedExtendedConsensus hN hγ hγ1
    (hv'.eq_zero_of_nonneg hγ hp h) hp
  exact biasedExitInv_of_pos (by omega) (Or.inl hext) fun ω hω =>
    ((isBiasedSweepable_extendedConsensus (by omega) hγ (by linarith) o).isBiasedLadder_stateAfter
      hγ (by linarith) hext hω).isBiasedSteepLadder

/-- In a block, a near-greedy expression moves one phase down. -/
theorem BiasedExitInv.express_nearGreedy (hM : 2 ≤ M) (hN : 2 ≤ N) (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) {v : Profile N M} {j : ℕ} (hv : BiasedExitInv γ o v (j + 1))
    {a : Actor N} {p : Opinion M} (hg : ∀ b q, v.pressure γ b q - γ / 2 < v.pressure γ a p) :
    BiasedExitInv γ o (Profile.express a p v) j := by
  obtain ⟨hset, hrun⟩ := hv
  have hpo : p = o := hset.elim (fun h => h.opinion_eq_of_nearGreedy hg)
    fun h => h.opinion_eq_of_nearGreedy hM hγ hγ' hg
  subst hpo
  have hγ2 : γ < 2 := by linarith [lt_one_of_lt_inv hM hγ']
  cases j with
  | zero =>
      have h := hrun (consPath (a, p) fun _ => (a, p)) fun k hk => by
        obtain rfl : k = 0 := by omega
        exact (isNearGreedyAt_consPath_zero _ _ _ _).2 hg
      rw [stateAfter_consPath_succ, stateAfter_zero] at h
      exact h
  | succ j =>
      refine ⟨hset.elim (fun h => Or.inl (h.express hN hγ hγ2 a))
        fun h => Or.inr (h.express hN hγ a), fun ω hω => ?_⟩
      have h := hrun (consPath (a, p) ω) fun k hk => by
        cases k with
        | zero => exact (isNearGreedyAt_consPath_zero _ _ _ _).2 hg
        | succ k => exact (isNearGreedyAt_consPath_succ _ _ _ _ _).2 (hω k (by omega))
      rwa [stateAfter_consPath_succ] at h

end Invariant

/-! ### The biased process restarted at its first jump

The biased path measure is `SocialNetwork.drivenMeasure` of `Profile.express` and the biased step
law, so the joint law of the first step and the rest is `SocialNetwork.map_drivenMeasure_firstRest`.
Everything after that is the argument of `SocialNetwork.ConsensusExit`, with
`SocialNetwork.Bias.stateAfter` in place of `SocialNetwork.Trajectory.state`. -/

section Restart

variable [NeZero N] [NeZero M]

/-- The biased path measure is the driven measure of its step law. -/
theorem biasedCtsPathMeasure_eq_drivenMeasure (γ β : ℝ) (u : Profile N M) :
    biasedCtsPathMeasure γ β u
      = drivenMeasure (fun (P : Profile N M) (p : Jump N M) => Profile.express p.1 p.2 P)
          (biasedStepLaw γ β) u := by
  have hstate : ∀ (j : ℕ → Jump N M) (n : ℕ),
      stateAfterJumps (fun (P : Profile N M) (p : Jump N M) => Profile.express p.1 p.2 P) u j n
        = stateAfter u j n := by
    intro j n
    induction n with
    | zero => rfl
    | succ n ih => rw [stateAfterJumps_succ, ih, stateAfter_succ]
  have hker : drivenKernel (fun (P : Profile N M) (p : Jump N M) => Profile.express p.1 p.2 P)
      (biasedStepLaw γ β) u = biasedCtsDrivingKernel γ β u := by
    funext n
    ext h : 1
    rw [drivenKernel_apply, biasedCtsDrivingKernel_apply]
    exact congrArg _ (hstate _ (n + 1))
  rw [drivenMeasure, jumpHoldMeasure, biasedCtsPathMeasure]
  simp only [hker]
  rfl

/-- **The restart at the first jump, on an arbitrary event**, for the biased process. -/
theorem biasedCtsPathMeasure_firstStep_apply (γ β : ℝ) (u : Profile N M)
    {S : Set (Step N M × (ℕ → Step N M))} (hS : MeasurableSet S) :
    biasedCtsPathMeasure γ β u {ω | (ω 0, shiftStepPath ω) ∈ S}
      = ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u) {ω' | (z, ω') ∈ S}
          ∂(biasedStepLaw γ β u) := by
  have hmeas : Measurable (fun ω : ℕ → Step N M => (ω 0, shiftHold ω)) :=
    (measurable_pi_apply 0).prodMk measurable_shiftHold
  have hset : {ω : ℕ → Step N M | (ω 0, shiftStepPath ω) ∈ S}
      = (fun ω : ℕ → Step N M => (ω 0, shiftHold ω)) ⁻¹' S := rfl
  rw [hset, biasedCtsPathMeasure_eq_drivenMeasure, ← Measure.map_apply hmeas hS,
    map_drivenMeasure_firstRest, Measure.compProd_apply hS]
  refine lintegral_congr fun z => ?_
  rw [restartKernel_apply, biasedCtsPathMeasure_eq_drivenMeasure]
  rfl

/-- The chance that the first holding time exceeds `t`. -/
theorem biasedCtsPathMeasure_lt_holdingTime (γ β : ℝ) (u : Profile N M) {t : ℝ} (ht : 0 ≤ t) :
    biasedCtsPathMeasure γ β u {ω | t < holdingTime 0 ω}
      = ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t))) := by
  have hq := biasedTotalRate_pos γ β u
  have hE : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β u)) :=
    isProbabilityMeasure_expMeasure hq
  have hS : MeasurableSet {x : Step N M × (ℕ → Step N M) | t < x.1.2} :=
    measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)
  have h := biasedCtsPathMeasure_firstStep_apply γ β u hS
  have hset : {ω : ℕ → Step N M | t < holdingTime 0 ω}
      = {ω | (ω 0, shiftStepPath ω) ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}} := rfl
  rw [hset, h]
  have hpt : ∀ z : Step N M, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
      {ω' | (z, ω') ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}}
      = (Set.univ ×ˢ Set.Ioi t : Set (Step N M)).indicator 1 z := by
    rintro ⟨p, s⟩
    by_cases hs : t < s
    · have hmem : ((p, s) : Step N M) ∈ (Set.univ ×ˢ Set.Ioi t : Set (Step N M)) :=
        ⟨Set.mem_univ _, hs⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      have : {ω' : ℕ → Step N M | ((p, s), ω') ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}}
          = Set.univ := by ext; simp [hs]
      rw [this, measure_univ]
    · have hmem : ((p, s) : Step N M) ∉ (Set.univ ×ˢ Set.Ioi t : Set (Step N M)) :=
        fun h => hs h.2
      rw [Set.indicator_of_notMem hmem]
      have : {ω' : ℕ → Step N M | ((p, s), ω') ∈ {x : Step N M × (ℕ → Step N M) | t < x.1.2}}
          = ∅ := by ext; simp [hs]
      rw [this, measure_empty]
  rw [lintegral_congr hpt, lintegral_indicator_one (MeasurableSet.univ.prod measurableSet_Ioi),
    biasedStepLaw, Measure.prod_prod, measure_univ, one_mul,
    expMeasure_Ioi_of_nonneg hq ht]

/-- Every holding time is almost surely positive. -/
theorem biasedCtsPathMeasure_holdingTime_nonpos (γ β : ℝ) (n : ℕ) :
    ∀ u : Profile N M, biasedCtsPathMeasure γ β u {ω | holdingTime n ω ≤ 0} = 0 := by
  induction n with
  | zero =>
      intro u
      have hq := biasedTotalRate_pos γ β u
      have hle : biasedCtsPathMeasure γ β u {ω | holdingTime 0 ω ≤ 0}
          ≤ biasedCtsPathMeasure γ β u {ω | 0 < holdingTime 0 ω}ᶜ :=
        measure_mono fun ω hω => by simpa using hω
      have hc := prob_compl_eq_one_sub (μ := biasedCtsPathMeasure γ β u)
        (s := {ω : ℕ → Step N M | 0 < holdingTime 0 ω})
        (measurableSet_lt measurable_const (measurable_holdingTime 0))
      rw [biasedCtsPathMeasure_lt_holdingTime γ β u le_rfl, mul_zero, neg_zero, Real.exp_zero,
        ENNReal.ofReal_one, tsub_self] at hc
      exact le_antisymm (hc ▸ hle) zero_le
  | succ n ih =>
      intro u
      have hS : MeasurableSet {x : Step N M × (ℕ → Step N M) | holdingTime n x.2 ≤ 0} :=
        measurableSet_le ((measurable_holdingTime n).comp measurable_snd) measurable_const
      have hset : {ω : ℕ → Step N M | holdingTime (n + 1) ω ≤ 0}
          = {ω | (ω 0, shiftStepPath ω) ∈
              {x : Step N M × (ℕ → Step N M) | holdingTime n x.2 ≤ 0}} := by
        ext ω
        simp only [Set.mem_ofPred_eq, holdingTime_shiftStepPath]
      rw [hset, biasedCtsPathMeasure_firstStep_apply γ β u hS]
      exact lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun z => ih _) |>.trans
        (by simp)

/-- The realisations whose holding times are all positive carry all the mass. -/
theorem biasedCtsPathMeasure_holdingTime_pos_compl (γ β : ℝ) (u : Profile N M) :
    biasedCtsPathMeasure γ β u {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}ᶜ = 0 := by
  rw [show {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}ᶜ
      = ⋃ n, {ω : ℕ → Step N M | holdingTime n ω ≤ 0} from by
    ext ω; simp [not_forall, not_lt]]
  exact measure_iUnion_null fun n => biasedCtsPathMeasure_holdingTime_nonpos γ β n u

end Restart

/-! ### Reading the biased process off the jump times -/

section Shift

/-- No jump by time `t`: the biased process is still where it started. -/
theorem biasedProcess_eq_of_lt_holdingTime (u : Profile N M) {ω : ℕ → Step N M}
    (hpos : ∀ n, 0 < holdingTime n ω) {t : ℝ} (ht : 0 ≤ t) (h : t < holdingTime 0 ω) :
    biasedProcess u t ω = u := by
  have hset : {n : ℕ | jumpTime n ω ≤ t} = {0} := by
    refine Set.Subset.antisymm (fun n hn => ?_) (by simpa using ht)
    by_contra hne
    have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by simpa using hne)
    have hle : jumpTime 1 ω ≤ jumpTime n ω := jumpTime_mono hpos h1
    rw [jumpTime_one] at hle
    exact absurd (le_trans hle hn) (not_le.2 h)
  have hcount : jumpCount ω t = 0 := by
    rw [jumpCount, hset, csSup_singleton]
  show stateAfter u (fun n => (ω n).1) (jumpCount ω t) = u
  rw [hcount, stateAfter_zero]

/-- The profile after `n + 1` expressions is the one the rest reaches after `n`, from the profile
the first expression produced. -/
theorem stateAfter_succ_shift (u : Profile N M) (ω : ℕ → Step N M) (n : ℕ) :
    stateAfter u (fun k => (ω k).1) (n + 1)
      = stateAfter (Profile.express (ω 0).1.1 (ω 0).1.2 u)
          (fun k => (shiftStepPath ω k).1) n := by
  rw [Nat.add_comm, stateAfter_add]
  rfl

/-- **The biased hitting time after the first jump, from below.** -/
theorem le_biasedHittingTimeCts_shift (u : Profile N M) {θ : Set (Profile N M)} (hu : u ∉ θ)
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) :
    ENNReal.ofReal (holdingTime 0 ω)
        + biasedHittingTimeCts (Profile.express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
      ≤ biasedHittingTimeCts u θ ω := by
  set S₀ := holdingTime 0 ω with hS₀
  have hS₀pos : 0 < S₀ := hpos 0
  conv_rhs => unfold biasedHittingTimeCts
  refine le_sInf ?_
  rintro _ ⟨s, ⟨hs0, hsθ⟩, rfl⟩
  have hS₀s : S₀ ≤ s := by
    by_contra hlt
    exact hu (by rwa [biasedProcess_eq_of_lt_holdingTime u hpos hs0 (not_le.1 hlt)] at hsθ)
  by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ s}
  · have hb' : BddAbove {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s - S₀} := by
      obtain ⟨B, hB⟩ := hb
      refine ⟨B, fun m hm => ?_⟩
      have : jumpTime (m + 1) ω ≤ s := by
        rw [jumpTime_succ_shiftStepPath]
        have : jumpTime m (shiftStepPath ω) ≤ s - S₀ := hm
        linarith
      have := hB this
      omega
    have hne : {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s - S₀}.Nonempty :=
      ⟨0, by simp; linarith⟩
    set m := jumpCount (shiftStepPath ω) (s - S₀) with hm
    have hmem : jumpTime m (shiftStepPath ω) ≤ s - S₀ := Nat.sSup_mem hne hb'
    have hcount : jumpCount ω s = m + 1 := by
      refine (jumpCount_eq_iff s ω (Nat.succ_ne_zero m)).2 ⟨?_, fun k hk => ?_⟩
      · rw [jumpTime_succ_shiftStepPath]; linarith
      · cases k with
        | zero => omega
        | succ j =>
            rw [jumpTime_succ_shiftStepPath] at hk
            have hj : jumpTime j (shiftStepPath ω) ≤ s - S₀ := by linarith
            have h' : j ≤ jumpCount (shiftStepPath ω) (s - S₀) := le_csSup hb' hj
            omega
    have hproc : biasedProcess (Profile.express (ω 0).1.1 (ω 0).1.2 u) (s - S₀) (shiftStepPath ω)
        = biasedProcess u s ω := by
      show stateAfter _ (fun k => (shiftStepPath ω k).1) (jumpCount (shiftStepPath ω) (s - S₀))
        = stateAfter u (fun k => (ω k).1) (jumpCount ω s)
      rw [hcount, ← hm, stateAfter_succ_shift]
    calc ENNReal.ofReal S₀
          + biasedHittingTimeCts (Profile.express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
        ≤ ENNReal.ofReal S₀ + ENNReal.ofReal (s - S₀) := by
          refine add_le_add le_rfl (sInf_le ⟨s - S₀, ⟨by linarith, ?_⟩, rfl⟩)
          rw [hproc]; exact hsθ
      _ = ENNReal.ofReal s := by
          rw [← ENNReal.ofReal_add hS₀pos.le (by linarith)]
          congr 1; ring
  · exfalso
    have h0 : jumpCount ω s = 0 := Nat.sSup_of_not_bddAbove hb
    apply hu
    have : biasedProcess u s ω = u := by
      show stateAfter u (fun k => (ω k).1) (jumpCount ω s) = u
      rw [h0, stateAfter_zero]
    rwa [this] at hsθ

end Shift

/-! ### Not reaching the target before `min (t, T_n)`, for the biased process -/

section Avoid

/-- The realisations on which `θ` has not been reached before `min (t, T_n)`. -/
def biasedAvoidBefore (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ) (t : ℝ) :
    Set (ℕ → Step N M) :=
  {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω ∨
    ENNReal.ofReal (jumpTime n ω) ≤ biasedHittingTimeCts u θ ω}

/-- The same events, at all times at once. -/
def biasedAvoidBeforeGraph (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ) :
    Set (ℝ × (ℕ → Step N M)) :=
  {x | x.2 ∈ biasedAvoidBefore u θ n x.1}

theorem measurableSet_biasedAvoidBeforeGraph (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ) :
    MeasurableSet (biasedAvoidBeforeGraph u θ n) := by
  have h1 : Measurable fun x : ℝ × (ℕ → Step N M) => biasedHittingTimeCts u θ x.2 :=
    (measurable_biasedHittingTimeCts u θ).comp measurable_snd
  have h2 : Measurable fun x : ℝ × (ℕ → Step N M) => ENNReal.ofReal x.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have h3 : Measurable fun x : ℝ × (ℕ → Step N M) => ENNReal.ofReal (jumpTime n x.2) :=
    ENNReal.measurable_ofReal.comp ((measurable_jumpTime n).comp measurable_snd)
  have hset : biasedAvoidBeforeGraph u θ n
      = {x : ℝ × (ℕ → Step N M) | ENNReal.ofReal x.1 < biasedHittingTimeCts u θ x.2}
        ∪ {x | ENNReal.ofReal (jumpTime n x.2) ≤ biasedHittingTimeCts u θ x.2} := rfl
  rw [hset]
  exact (measurableSet_lt h2 h1).union (measurableSet_le h3 h1)

theorem measurableSet_biasedAvoidBefore (u : Profile N M) (θ : Set (Profile N M)) (n : ℕ)
    (t : ℝ) : MeasurableSet (biasedAvoidBefore u θ n t) := by
  show MeasurableSet (Prod.mk t ⁻¹' biasedAvoidBeforeGraph u θ n)
  exact measurable_prodMk_left (measurableSet_biasedAvoidBeforeGraph u θ n)

theorem biasedAvoidBefore_zero (u : Profile N M) (θ : Set (Profile N M)) (t : ℝ) :
    biasedAvoidBefore u θ 0 t = Set.univ := by
  ext ω
  simp [biasedAvoidBefore]

variable [NeZero N] [NeZero M]

/-- **The first-step inequality**, for the biased process. -/
theorem le_biasedCtsPathMeasure_avoidBefore_succ (γ β : ℝ) {u : Profile N M}
    {θ : Set (Profile N M)} (hu : u ∉ θ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t)))
        + ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
            {ω' | z.2 ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express z.1.1 z.1.2 u) θ n (t - z.2)}
            ∂(biasedStepLaw γ β u)
      ≤ biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ (n + 1) t) := by
  set G := {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} with hGdef
  set S : Set (Step N M × (ℕ → Step N M)) :=
    {x | x.1.2 ≤ t ∧ x.2 ∈ biasedAvoidBefore (Profile.express x.1.1.1 x.1.1.2 u) θ n (t - x.1.2)}
    with hSdef
  have hSmeas : MeasurableSet S := by
    have hset : S = ⋃ p : Jump N M,
        ((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹' {p})
          ∩ (((fun x : Step N M × (ℕ → Step N M) => x.1.2) ⁻¹' Set.Iic t)
            ∩ ((fun x : Step N M × (ℕ → Step N M) => (t - x.1.2, x.2)) ⁻¹'
              biasedAvoidBeforeGraph (Profile.express p.1 p.2 u) θ n)) := by
      ext x
      simp only [hSdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_Iic, biasedAvoidBeforeGraph, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨x.1.1, rfl, h1, h2⟩
      · rintro ⟨p, rfl, h1, h2⟩
        exact ⟨h1, h2⟩
    rw [hset]
    refine MeasurableSet.iUnion fun p => ?_
    refine ((measurable_fst.comp measurable_fst) (measurableSet_singleton p)).inter
      (((measurable_snd.comp measurable_fst) measurableSet_Iic).inter ?_)
    exact ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
      (measurableSet_biasedAvoidBeforeGraph _ θ n)
  set A : Set (ℕ → Step N M) := {ω | t < holdingTime 0 ω} with hAdef
  set B : Set (ℕ → Step N M) := {ω | (ω 0, shiftStepPath ω) ∈ S} with hBdef
  have hBmeas : MeasurableSet B :=
    ((measurable_pi_apply 0).prodMk measurable_shiftStepPath) hSmeas
  have hA : biasedCtsPathMeasure γ β u A
      = ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t))) :=
    biasedCtsPathMeasure_lt_holdingTime γ β u ht
  have hB : biasedCtsPathMeasure γ β u B
      = ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
          {ω' | z.2 ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express z.1.1 z.1.2 u) θ n (t - z.2)}
          ∂(biasedStepLaw γ β u) :=
    biasedCtsPathMeasure_firstStep_apply γ β u hSmeas
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ω hA ⟨hB, -⟩
    exact absurd hB (not_le.2 hA)
  have hsub : (A ∪ B) ∩ G ⊆ biasedAvoidBefore u θ (n + 1) t := by
    rintro ω ⟨hAB, hG⟩
    have hG' : ∀ n, 0 < holdingTime n ω := hG
    have hkey := le_biasedHittingTimeCts_shift u hu hG'
    set R' := biasedHittingTimeCts (Profile.express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
    have hS₀ : 0 < holdingTime 0 ω := hG' 0
    rcases hAB with hω | ⟨hle, hω⟩
    · change t < holdingTime 0 ω at hω
      left
      calc ENNReal.ofReal t < ENNReal.ofReal (holdingTime 0 ω) :=
            (ENNReal.ofReal_lt_ofReal_iff hS₀).2 hω
        _ ≤ ENNReal.ofReal (holdingTime 0 ω) + R' := le_self_add
        _ ≤ biasedHittingTimeCts u θ ω := hkey
    · change holdingTime 0 ω ≤ t at hle
      change ENNReal.ofReal (t - holdingTime 0 ω) < R'
        ∨ ENNReal.ofReal (jumpTime n (shiftStepPath ω)) ≤ R' at hω
      rcases hω with hω | hω
      · left
        calc ENNReal.ofReal t
            = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal (t - holdingTime 0 ω) := by
              rw [← ENNReal.ofReal_add hS₀.le (by linarith)]; congr 1; ring
          _ < ENNReal.ofReal (holdingTime 0 ω) + R' :=
              ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hω
          _ ≤ biasedHittingTimeCts u θ ω := hkey
      · right
        have hTn : 0 ≤ jumpTime n (shiftStepPath ω) :=
          Finset.sum_nonneg fun k _ => by
            rw [holdingTime_shiftStepPath]; exact (hG' (k + 1)).le
        calc ENNReal.ofReal (jumpTime (n + 1) ω)
            = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal (jumpTime n (shiftStepPath ω)) := by
              rw [jumpTime_succ_shiftStepPath, ENNReal.ofReal_add hS₀.le hTn]
          _ ≤ ENNReal.ofReal (holdingTime 0 ω) + R' := add_le_add le_rfl hω
          _ ≤ biasedHittingTimeCts u θ ω := hkey
  have hGnull := biasedCtsPathMeasure_holdingTime_pos_compl γ β u
  have hconull : biasedCtsPathMeasure γ β u ((A ∪ B) ∩ G)
      = biasedCtsPathMeasure γ β u (A ∪ B) := by
    have h := measure_inter_add_sdiff (μ := biasedCtsPathMeasure γ β u) (A ∪ B)
      measurableSet_holdingTime_pos
    rwa [measure_mono_null (Set.sdiff_subset_compl _ _) hGnull, add_zero] at h
  rw [← hA, ← hB, ← measure_union hdisj hBmeas, ← hconull]
  exact measure_mono hsub

/-- **Passing to the limit**, for the biased process. -/
theorem le_biasedCtsPathMeasure_lt_hittingTimeCts (γ β : ℝ) {u : Profile N M}
    {θ : Set (Profile N M)} (hu : u ∉ θ) {t : ℝ} {c : ℝ≥0∞}
    (h : ∀ n, c ≤ biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ n t)) :
    c ≤ biasedCtsPathMeasure γ β u {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω} := by
  set G := {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} with hGdef
  set s : ℕ → Set (ℕ → Step N M) := fun n => biasedAvoidBefore u θ n t ∩ G with hsdef
  have hGnull := biasedCtsPathMeasure_holdingTime_pos_compl γ β u
  have hconull : ∀ n, biasedCtsPathMeasure γ β u (s n)
      = biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ n t) := by
    intro n
    have h := measure_inter_add_sdiff (μ := biasedCtsPathMeasure γ β u)
      (biasedAvoidBefore u θ n t) measurableSet_holdingTime_pos
    rwa [measure_mono_null (Set.sdiff_subset_compl _ _) hGnull, add_zero] at h
  have hanti : Antitone s := by
    refine antitone_nat_of_succ_le fun n => ?_
    rintro ω ⟨hω, hG⟩
    refine ⟨?_, hG⟩
    rcases hω with hω | hω
    · exact Or.inl hω
    · right
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hω
      rw [jumpTime_succ]
      linarith [(hG : ∀ n, 0 < holdingTime n ω) n]
  have hinter : (⋂ n, s n) ⊆ {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω} := by
    intro ω hω
    rw [Set.mem_iInter] at hω
    have hG : ∀ n, 0 < holdingTime n ω := (hω 0).2
    by_contra hnot
    have hall : ∀ n, ENNReal.ofReal (jumpTime n ω) ≤ biasedHittingTimeCts u θ ω := fun n =>
      (hω n).1.resolve_left hnot
    apply hnot
    show ENNReal.ofReal t < biasedHittingTimeCts u θ ω
    suffices htop : biasedHittingTimeCts u θ ω = ⊤ by rw [htop]; exact ENNReal.ofReal_lt_top
    unfold biasedHittingTimeCts
    rw [sInf_eq_top]
    rintro _ ⟨r, ⟨hr0, hrθ⟩, rfl⟩
    exfalso
    by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ r}
    · have hne : {n : ℕ | jumpTime n ω ≤ r}.Nonempty := ⟨0, by simpa using hr0⟩
      set k := jumpCount ω r with hk
      have hkmem : jumpTime k ω ≤ r := Nat.sSup_mem hne hb
      have hmono := jumpTime_mono hG
      have hk0 : 0 ≤ jumpTime k ω := Finset.sum_nonneg fun i _ => (hG i).le
      have hcountk : jumpCount ω (jumpTime k ω) = k := by
        have hbk : BddAbove {n : ℕ | jumpTime n ω ≤ jumpTime k ω} :=
          hb.mono fun n hn => le_trans hn hkmem
        have hkk : k ∈ {n : ℕ | jumpTime n ω ≤ jumpTime k ω} := le_refl (jumpTime k ω)
        refine le_antisymm (csSup_le ⟨k, hkk⟩ fun n hn => ?_) (le_csSup hbk hkk)
        by_contra hlt
        have hstep : jumpTime (k + 1) ω ≤ jumpTime n ω := hmono (by omega)
        rw [jumpTime_succ] at hstep
        have : jumpTime n ω ≤ jumpTime k ω := hn
        linarith [hG k]
      have hR : biasedHittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime k ω) := by
        unfold biasedHittingTimeCts
        refine sInf_le ⟨jumpTime k ω, ⟨hk0, ?_⟩, rfl⟩
        show stateAfter u (fun n => (ω n).1) (jumpCount ω (jumpTime k ω)) ∈ θ
        rw [hcountk]
        exact hrθ
      have h1 := le_trans (hall (k + 1)) hR
      rw [ENNReal.ofReal_le_ofReal_iff hk0, jumpTime_succ] at h1
      linarith [hG k]
    · have h0 : jumpCount ω r = 0 := Nat.sSup_of_not_bddAbove hb
      apply hu
      have : biasedProcess u r ω = u := by
        show stateAfter u (fun n => (ω n).1) (jumpCount ω r) = u
        rw [h0, stateAfter_zero]
      rwa [this] at hrθ
  have hsmeas : ∀ n, MeasurableSet (s n) := fun n =>
    (measurableSet_biasedAvoidBefore u θ n t).inter measurableSet_holdingTime_pos
  have hlim : biasedCtsPathMeasure γ β u (⋂ n, s n) = ⨅ n, biasedCtsPathMeasure γ β u (s n) :=
    hanti.measure_iInter (fun n => (hsmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  calc c ≤ ⨅ n, biasedCtsPathMeasure γ β u (s n) := le_iInf fun n => by rw [hconull]; exact h n
    _ = biasedCtsPathMeasure γ β u (⋂ n, s n) := hlim.symm
    _ ≤ _ := measure_mono hinter

end Avoid

/-! ### Comparing with an exponential clock, for the biased process

One step of the comparison of `SocialNetwork.ConsensusExit`, with the biased rates. -/

section Comparison

variable [NeZero N] [NeZero M]

/-- The biased jump law, written with the rates. -/
theorem biasedJumpPMF_eq_ofReal (γ β : ℝ) (v : Profile N M) (p : Jump N M) :
    biasedJumpPMF γ β v p
      = ENNReal.ofReal (biasedJumpRate γ β v p.1 p.2 / biasedTotalRate γ β v) := by
  have hpos := biasedTotalRate_pos γ β v
  have hsum : ∑' q : Jump N M, biasedJumpWeight γ β v q
      = ENNReal.ofReal (biasedTotalRate γ β v) := by
    rw [tsum_fintype, biasedTotalRate]
    exact (ENNReal.ofReal_sum_of_nonneg fun q _ => (biasedJumpRate_pos γ β v q.1 q.2).le).symm
  rw [biasedJumpPMF_apply, hsum, biasedJumpWeight, ← div_eq_mul_inv,
    ← ENNReal.ofReal_div_of_pos hpos]

/-- Integrating a score against the biased jump law. -/
theorem lintegral_biasedJumpPMF_ofReal (γ β : ℝ) (v : Profile N M) {sc : Jump N M → ℝ}
    (hsc : ∀ p, 0 ≤ sc p) :
    ∫⁻ p, ENNReal.ofReal (sc p) ∂(biasedJumpPMF γ β v).toMeasure
      = ENNReal.ofReal ((∑ p, sc p * biasedJumpRate γ β v p.1 p.2) / biasedTotalRate γ β v) := by
  have hpos := biasedTotalRate_pos γ β v
  rw [lintegral_countable', tsum_fintype]
  have hterm : ∀ p : Jump N M, ENNReal.ofReal (sc p) * (biasedJumpPMF γ β v).toMeasure {p}
      = ENNReal.ofReal (sc p * biasedJumpRate γ β v p.1 p.2 / biasedTotalRate γ β v) := by
    intro p
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), biasedJumpPMF_eq_ofReal,
      ← ENNReal.ofReal_mul (hsc p), mul_div_assoc]
  rw [Finset.sum_congr rfl fun p _ => hterm p,
    ← ENNReal.ofReal_sum_of_nonneg fun p _ =>
      div_nonneg (mul_nonneg (hsc p) (biasedJumpRate_pos γ β v p.1 p.2).le) hpos.le,
    Finset.sum_div]

/-- **One step of the comparison**, for the biased process. -/
theorem le_biasedCtsPathMeasure_avoidBefore_of_score (γ β : ℝ) {u : Profile N M}
    {θ : Set (Profile N M)} (hu : u ∉ θ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {Λ φ : ℝ}
    (hΛ : 0 ≤ Λ) (hφ1 : φ ≤ 1) (sc : Jump N M → ℝ) (hsc : ∀ p, 0 ≤ sc p)
    (hcomp : (biasedTotalRate γ β u - Λ) * φ ≤ ∑ p, sc p * biasedJumpRate γ β u p.1 p.2)
    (hIH : ∀ p : Jump N M, ∀ s : ℝ, s ≤ t →
      ENNReal.ofReal (sc p * Real.exp (-(Λ * (t - s))))
        ≤ biasedCtsPathMeasure γ β (Profile.express p.1 p.2 u)
            (biasedAvoidBefore (Profile.express p.1 p.2 u) θ n (t - s))) :
    ENNReal.ofReal (φ * Real.exp (-(Λ * t)))
      ≤ biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ (n + 1) t) := by
  have hq := biasedTotalRate_pos γ β u
  have hE : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β u)) :=
    isProbabilityMeasure_expMeasure hq
  set W := ∑ p, sc p * biasedJumpRate γ β u p.1 p.2 with hWdef
  have hW : 0 ≤ W :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hsc p) (biasedJumpRate_pos γ β u p.1 p.2).le
  set g : ℝ → ℝ≥0∞ :=
    (Set.Iic t).indicator (fun s => ENNReal.ofReal (Real.exp (-(Λ * (t - s))))) with hgdef
  have hg : Measurable g := Measurable.indicator (by fun_prop) measurableSet_Iic
  have hprod : ∫⁻ z, ENNReal.ofReal (sc z.1) * g z.2 ∂(biasedStepLaw γ β u)
      = ENNReal.ofReal (W / biasedTotalRate γ β u)
          * ∫⁻ s, g s ∂(expMeasure (biasedTotalRate γ β u)) := by
    rw [biasedStepLaw, lintegral_prod_mul (f := fun p => ENNReal.ofReal (sc p)) (g := g)
      (measurable_of_countable _).aemeasurable hg.aemeasurable,
      lintegral_biasedJumpPMF_ofReal γ β u hsc]
  have hpt : ∀ z : Step N M, ENNReal.ofReal (sc z.1) * g z.2
      ≤ biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
          {ω' | z.2 ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express z.1.1 z.1.2 u) θ n (t - z.2)} := by
    rintro ⟨p, s⟩
    by_cases hs : s ≤ t
    · have hmem : s ∈ Set.Iic t := hs
      simp only [hgdef, Set.indicator_of_mem hmem]
      rw [← ENNReal.ofReal_mul (hsc p)]
      have hset : {ω' | s ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express p.1 p.2 u) θ n (t - s)}
          = biasedAvoidBefore (Profile.express p.1 p.2 u) θ n (t - s) := by
        ext ω'; simp [hs]
      rw [hset]
      exact hIH p s hs
    · have hmem : s ∉ Set.Iic t := hs
      simp [hgdef, Set.indicator_of_notMem hmem]
  calc ENNReal.ofReal (φ * Real.exp (-(Λ * t)))
      ≤ ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t)))
        + ENNReal.ofReal (W / biasedTotalRate γ β u)
          * ∫⁻ s, g s ∂(expMeasure (biasedTotalRate γ β u)) :=
        le_exp_add_mul_lintegral hq hΛ hφ1 hW hcomp ht
    _ = ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t)))
        + ∫⁻ z, ENNReal.ofReal (sc z.1) * g z.2 ∂(biasedStepLaw γ β u) := by rw [hprod]
    _ ≤ ENNReal.ofReal (Real.exp (-(biasedTotalRate γ β u * t)))
        + ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
            {ω' | z.2 ≤ t ∧ ω' ∈ biasedAvoidBefore (Profile.express z.1.1 z.1.2 u) θ n (t - z.2)}
            ∂(biasedStepLaw γ β u) := add_le_add le_rfl (lintegral_mono hpt)
    _ ≤ biasedCtsPathMeasure γ β u (biasedAvoidBefore u θ (n + 1) t) :=
        le_biasedCtsPathMeasure_avoidBefore_succ γ β hu n ht

end Comparison

/-! ### Lemma 29

The rate of failure is `Λ = 2 N³ (M+1)³ e^{-βγ/2}`, the paper's.  In phase `0` the pairs
expressing against a negative pressure fail, at total rate at most `N M e^{-βγ}`, and the pairs
expressing `p ≠ o` against a non-negative pressure open a block, at total rate at most `N M`,
which fails with probability at most `1 - ζ_{α,β}^N ≤ N · M N e^{-βγ/2}` by Proposition 24 and
the biased Remark 4.  Inside a block every expression has to be near-greedy, which it is with
probability at least `ζ_{α,β}` whatever the profile. -/

section Rates

/-- The rate of failure, `2 N³ (M+1)³ e^{-βγ/2}`. -/
noncomputable def biasedExitRate (N M : ℕ) (γ β : ℝ) : ℝ :=
  2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-(β * γ / 2))

theorem biasedExitRate_nonneg (N M : ℕ) (γ β : ℝ) : 0 ≤ biasedExitRate N M γ β := by
  unfold biasedExitRate; positivity

theorem biasedZeta_le_one (N M : ℕ) (γ β : ℝ) : biasedZeta N M γ β ≤ 1 := by
  have h1 : (0 : ℝ) < Real.exp (β * γ / 2) := Real.exp_pos _
  have h2 : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold biasedZeta
  rw [div_le_one (by linarith)]
  linarith

/-- The first half of Remark 4 for the biased model: `ζ_{α,β} ≥ 1 - MN e^{-βγ/2}`. -/
theorem one_sub_le_biasedZeta (N M : ℕ) (γ β : ℝ) :
    1 - ((M * N : ℕ) : ℝ) * Real.exp (-(β * γ / 2)) ≤ biasedZeta N M γ β := by
  set E := Real.exp (β * γ / 2) with hE
  set c := ((M * N : ℕ) : ℝ) with hc
  have hEpos : 0 < E := Real.exp_pos _
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  unfold biasedZeta
  rw [← hE, ← hc, Real.exp_neg, ← hE, le_div_iff₀ (by linarith)]
  have key : (1 - c * E⁻¹) * (E + c) = E - c * c * E⁻¹ + c * (1 - E⁻¹ * E) := by ring
  rw [key, inv_mul_cancel₀ hEpos.ne']
  have hnn : 0 ≤ c * c * E⁻¹ := by positivity
  linarith

/-- **Remark 4 for the biased model**: `ζ_{α,β}^m ≥ 1 - m M N e^{-βγ/2}`. -/
theorem one_sub_le_biasedZeta_pow (N M : ℕ) (γ β : ℝ) (m : ℕ) :
    1 - (m : ℝ) * (((M * N : ℕ) : ℝ) * Real.exp (-(β * γ / 2))) ≤ biasedZeta N M γ β ^ m := by
  set x := ((M * N : ℕ) : ℝ) * Real.exp (-(β * γ / 2)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hz : 1 - x ≤ biasedZeta N M γ β := one_sub_le_biasedZeta N M γ β
  have hzpos := biasedZeta_pos N M γ β
  rcases le_or_gt 1 x with h | h
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hpow : (0 : ℝ) < biasedZeta N M γ β ^ m := pow_pos hzpos m
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1) (by linarith : (0 : ℝ) ≤ x - 1)]
  · have h1 : 0 ≤ 1 - x := by linarith
    have h2 : (1 - x) ^ m ≤ biasedZeta N M γ β ^ m := pow_le_pow_left₀ h1 hz m
    have h3 := one_add_mul_le_pow (a := -x) (by linarith) m
    rw [show (1 : ℝ) + (m : ℝ) * -x = 1 - (m : ℝ) * x by ring,
      show (1 : ℝ) + -x = 1 - x by ring] at h3
    exact h3.trans h2

variable {γ β : ℝ} {o : Opinion M}

/-- In `L̂_α^o`, an expression against a negative pressure has rate at most `e^{-βγ/2}`. -/
theorem IsBiasedSteepLadder.biasedJumpRate_le_of_neg (hγ : 0 < γ) (hβ : 0 ≤ β)
    {v : Profile N M} (hv : IsBiasedSteepLadder γ o v) {a : Actor N} {p : Opinion M}
    (h : v.pressure γ a p < 0) : biasedJumpRate γ β v a p ≤ Real.exp (-(β * γ / 2)) := by
  unfold biasedJumpRate
  refine Real.exp_le_exp.2 ?_
  have hle := hv.le_neg_of_neg hγ h
  nlinarith [mul_le_mul_of_nonneg_left hle hβ, mul_nonneg hβ hγ.le]

/-- An expression against a non-positive pressure has rate at most `1`. -/
theorem biasedJumpRate_le_one (hβ : 0 ≤ β) {v : Profile N M} {a : Actor N} {p : Opinion M}
    (h : v.pressure γ a p ≤ 0) : biasedJumpRate γ β v a p ≤ 1 := by
  unfold biasedJumpRate
  exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hβ h)

/-- **Phase `0`.**  The rate of the pairs that fail, plus the rate of those that open a block
times the chance the block fails, is at most `Λ`. -/
theorem biasedRate_phase_zero (hγ : 0 < γ) (hβ : 0 ≤ β) {v : Profile N M}
    (hv : IsBiasedSteepLadder γ o v) :
    (biasedTotalRate γ β v - biasedExitRate N M γ β) * biasedZeta N M γ β ^ 0
      ≤ ∑ p : Jump N M, (if v.pressure γ p.1 p.2 < 0 then 0
          else if p.2 = o then 1 else biasedZeta N M γ β ^ N) * biasedJumpRate γ β v p.1 p.2 := by
  set e := Real.exp (-(β * γ / 2)) with he
  set z := biasedZeta N M γ β ^ N with hz
  have hz1 : z ≤ 1 := pow_le_one₀ (biasedZeta_pos N M γ β).le (biasedZeta_le_one N M γ β)
  have hz0 : 0 ≤ z := pow_nonneg (biasedZeta_pos N M γ β).le N
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hterm : ∀ p : Jump N M,
      biasedJumpRate γ β v p.1 p.2
        - (if v.pressure γ p.1 p.2 < 0 then 0 else if p.2 = o then 1 else z)
          * biasedJumpRate γ β v p.1 p.2
        ≤ e + (1 - z) := by
    intro p
    have hr := (biasedJumpRate_pos γ β v p.1 p.2).le
    by_cases hneg : v.pressure γ p.1 p.2 < 0
    · rw [if_pos hneg]
      have := hv.biasedJumpRate_le_of_neg hγ hβ hneg
      linarith
    · rw [if_neg hneg]
      by_cases ho : p.2 = o
      · rw [if_pos ho]; linarith
      · rw [if_neg ho]
        have h1 := biasedJumpRate_le_one (β := β) hβ (hv.nonpos hγ p.1 ho)
        nlinarith
  have hsum : biasedTotalRate γ β v
      - ∑ p : Jump N M, (if v.pressure γ p.1 p.2 < 0 then 0 else if p.2 = o then 1 else z)
          * biasedJumpRate γ β v p.1 p.2
      ≤ (N * M : ℕ) * (e + (1 - z)) := by
    rw [biasedTotalRate, ← Finset.sum_sub_distrib]
    calc ∑ p : Jump N M, (biasedJumpRate γ β v p.1 p.2
            - (if v.pressure γ p.1 p.2 < 0 then 0 else if p.2 = o then 1 else z)
              * biasedJumpRate γ β v p.1 p.2)
        ≤ ∑ _p : Jump N M, (e + (1 - z)) := Finset.sum_le_sum fun p _ => hterm p
      _ = (N * M : ℕ) * (e + (1 - z)) := by
          rw [Finset.sum_const, Finset.card_univ, card_jump, nsmul_eq_mul]
  have hrem := one_sub_le_biasedZeta_pow N M γ β N
  rw [← he, ← hz] at hrem
  have hconst := rates_le_exitRate_const N M
  have hΛ : (N * M : ℕ) * (e + (1 - z)) ≤ biasedExitRate N M γ β := by
    have h1 : (1 - z) ≤ (N : ℝ) * ((M : ℝ) * N * e) := by push_cast at hrem; linarith
    have hNM : (0 : ℝ) ≤ ((N * M : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((N * M : ℕ) : ℝ) * (e + (1 - z))
        ≤ ((N * M : ℕ) : ℝ) * (e + (N : ℝ) * ((M : ℝ) * N * e)) :=
          mul_le_mul_of_nonneg_left (by linarith) hNM
      _ = ((N : ℝ) * M + (N : ℝ) * ((M : ℝ) * N * N * M)) * e := by push_cast; ring
      _ ≤ 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * e := mul_le_mul_of_nonneg_right hconst he0
      _ = biasedExitRate N M γ β := rfl
  rw [pow_zero, mul_one]
  linarith

variable [NeZero N] [NeZero M]

/-- **In a block.**  The near-greedy pairs carry rate at least `ζ_{α,β} q`. -/
theorem biasedRate_phase_succ (hγ : 0 < γ) (hβ : 0 ≤ β) (v : Profile N M) (j : ℕ) :
    (biasedTotalRate γ β v - biasedExitRate N M γ β) * biasedZeta N M γ β ^ (j + 1)
      ≤ ∑ p : Jump N M, (if p ∈ nearArgmaxFinset γ v then biasedZeta N M γ β ^ j else 0)
          * biasedJumpRate γ β v p.1 p.2 := by
  have hq := biasedTotalRate_pos γ β v
  have hζ := biasedZeta_pos N M γ β
  -- Proposition 24: the near-greedy pairs carry probability at least `ζ_{α,β}`
  have h24 := biasedZeta_le_biasedJumpPMF_nearArgmaxFinset (N := N) (M := M) hγ hβ v
  rw [PMF.toMeasure_apply_finset] at h24
  have hsum : ∑ p ∈ nearArgmaxFinset γ v, biasedJumpPMF γ β v p
      = ENNReal.ofReal ((∑ p ∈ nearArgmaxFinset γ v, biasedJumpRate γ β v p.1 p.2)
          / biasedTotalRate γ β v) := by
    rw [Finset.sum_congr rfl fun p _ => biasedJumpPMF_eq_ofReal γ β v p,
      ← ENNReal.ofReal_sum_of_nonneg fun p _ =>
        div_nonneg (biasedJumpRate_pos γ β v p.1 p.2).le hq.le,
      Finset.sum_div]
  rw [hsum, ENNReal.ofReal_le_ofReal_iff (div_nonneg
    (Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β v p.1 p.2).le) hq.le),
    le_div_iff₀ hq] at h24
  have hrhs : ∑ p : Jump N M, (if p ∈ nearArgmaxFinset γ v then biasedZeta N M γ β ^ j else 0)
        * biasedJumpRate γ β v p.1 p.2
      = biasedZeta N M γ β ^ j * ∑ p ∈ nearArgmaxFinset γ v, biasedJumpRate γ β v p.1 p.2 := by
    rw [Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ nearArgmaxFinset γ v)]
    have h1 : Finset.univ.filter (· ∈ nearArgmaxFinset γ v) = nearArgmaxFinset γ v := by
      ext p; simp
    rw [h1]
    have h2 : ∑ p ∈ Finset.univ.filter (fun p => p ∉ nearArgmaxFinset γ v),
        (if p ∈ nearArgmaxFinset γ v then biasedZeta N M γ β ^ j else 0)
          * biasedJumpRate γ β v p.1 p.2 = 0 :=
      Finset.sum_eq_zero fun p hp => by
        rw [if_neg (Finset.mem_filter.1 hp).2, zero_mul]
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun p hp => by rw [if_pos hp]
  rw [hrhs, pow_succ]
  have hΛ := biasedExitRate_nonneg N M γ β
  have hzj : 0 ≤ biasedZeta N M γ β ^ j := pow_nonneg hζ.le j
  calc (biasedTotalRate γ β v - biasedExitRate N M γ β)
        * (biasedZeta N M γ β ^ j * biasedZeta N M γ β)
      ≤ biasedTotalRate γ β v * (biasedZeta N M γ β ^ j * biasedZeta N M γ β) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = biasedZeta N M γ β ^ j * (biasedZeta N M γ β * biasedTotalRate γ β v) := by ring
    _ ≤ biasedZeta N M γ β ^ j * ∑ p ∈ nearArgmaxFinset γ v, biasedJumpRate γ β v p.1 p.2 :=
        mul_le_mul_of_nonneg_left h24 hzj

end Rates

section Lemma29

variable [NeZero N] [NeZero M]

/-- **The comparison, by induction on the number of jumps.**  From a phase-`j` profile the
consensus for another opinion is avoided before `min (t, T_n)` with probability at least
`ζ_{α,β}^j e^{-Λ t}`. -/
theorem le_biasedCtsPathMeasure_avoidBefore (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) (o : Opinion M) (n : ℕ) :
    ∀ (j : ℕ) (v : Profile N M), BiasedExitInv γ o v j → ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal (biasedZeta N M γ β ^ j * Real.exp (-(biasedExitRate N M γ β * t)))
        ≤ biasedCtsPathMeasure γ β v (biasedAvoidBefore v (biasedConsensusSetOther N γ o) n t) := by
  have hζ0 := (biasedZeta_pos N M γ β).le
  have hζ1 := biasedZeta_le_one N M γ β
  have hΛ := biasedExitRate_nonneg N M γ β
  induction n with
  | zero =>
      intro j v _ t ht
      rw [biasedAvoidBefore_zero, measure_univ]
      refine ENNReal.ofReal_le_one.2 (mul_le_one₀ (pow_le_one₀ hζ0 hζ1) (Real.exp_pos _).le ?_)
      exact Real.exp_le_one_iff.2 (by nlinarith)
  | succ n ih =>
      intro j v hv t ht
      have hnot := hv.notMem hM (by omega) hγ'
      cases j with
      | zero =>
          have hv' : IsBiasedSteepLadder γ o v := hv
          refine le_biasedCtsPathMeasure_avoidBefore_of_score γ β hnot n ht hΛ
            (pow_le_one₀ hζ0 hζ1)
            (fun p => if v.pressure γ p.1 p.2 < 0 then 0
              else if p.2 = o then 1 else biasedZeta N M γ β ^ N)
            (fun p => by split_ifs <;> positivity) (biasedRate_phase_zero hγ hβ hv') ?_
          rintro ⟨a, p⟩ s hs
          by_cases hneg : v.pressure γ a p < 0
          · simp [hneg]
          · by_cases ho : p = o
            · subst ho
              have h := ih 0 (Profile.express a p v) (hv.express_self a) (t - s) (by linarith)
              simpa [hneg] using h
            · have h := ih N (Profile.express a p v)
                (hv.express_other hM hN hγ hγ' ho (le_of_not_gt hneg)) (t - s) (by linarith)
              simpa [hneg, ho] using h
      | succ j =>
          refine le_biasedCtsPathMeasure_avoidBefore_of_score γ β hnot n ht hΛ
            (pow_le_one₀ hζ0 hζ1)
            (fun p => if p ∈ nearArgmaxFinset γ v then biasedZeta N M γ β ^ j else 0)
            (fun p => by split_ifs <;> positivity) (biasedRate_phase_succ hγ hβ v j) ?_
          rintro ⟨a, p⟩ s hs
          by_cases hg : (a, p) ∈ nearArgmaxFinset γ v
          · have hng : ∀ b q, v.pressure γ b q - γ / 2 < v.pressure γ a p := fun b q => by
              have h1 := mem_nearArgmaxFinset.1 hg
              have h2 := le_pressureSup γ v b q
              simp only at h1
              linarith
            have h := ih j (Profile.express a p v)
              (hv.express_nearGreedy hM (by omega) hγ hγ' hng) (t - s) (by linarith)
            simpa [hg] using h
          · simp [hg]

/-- **Lemma 29.1.**  From a biased ladder supporting `o`, the consensus for another opinion is
not reached before time `t` with probability at least
`exp (-2 t N³ (M+1)³ e^{-βγ/2})`.

**Follows the paper's proof**, which is that of Lemma 14 with the gap `1/(M-1)` replaced by the
slack `γ/2` of Remark 7, and with the same departures as `SocialNetwork.ConsensusExit`: the
block is the last stage of Proposition 23, `N` near-greedy expressions, and the comparison with
an exponential clock is run on the jump chain, without Theorem 1.1.  **Supplies two steps** the
transport needs and Appendix C does not write: that a near-greedy expression from `C_α^o`
expresses `o`, and that a near-greedy run sweeps onto `L_α^o`; see the module docstring. -/
theorem le_biasedProbHittingGT (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {l : Profile N M}
    (hl : IsBiasedLadder γ o l) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.exp
        (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β * γ / 2)))
      ≤ biasedProbHittingGT γ β l (biasedConsensusSetOther N γ o) (ENNReal.ofReal t) := by
  have hinv : BiasedExitInv γ o l 0 := biasedExitInv_zero_of_isBiasedLadder hl
  have key := le_biasedCtsPathMeasure_lt_hittingTimeCts γ β (hinv.notMem hM (by omega) hγ')
    fun n => le_biasedCtsPathMeasure_avoidBefore hM hN hγ hγ' hβ o n 0 l hinv t ht.le
  have heq : biasedZeta N M γ β ^ 0 * Real.exp (-(biasedExitRate N M γ β * t))
      = Real.exp (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β * γ / 2)) := by
    rw [pow_zero, one_mul, biasedExitRate, show -β * γ / 2 = -(β * γ / 2) by ring]
    congr 1
    ring
  rw [← heq]
  exact key

/-- **Lemma 29.2.**  From a biased consensus state for `o`, the consensus for another opinion
is reached before time `t` with probability at most
`(N² M + 2 t N³ (M+1)³) e^{-βγ/2}`.

**Follows the paper's proof**, with the departures of `SocialNetwork.Bias.le_biasedProbHittingGT`:
from `C_α^o` the process returns to `L_α^o` through `N` near-greedy expressions, with probability
at least `ζ_{α,β}^N`. -/
theorem biasedProbHittingLE_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {u : Profile N M}
    (hu : IsBiasedConsensus γ o u) {t : ℝ} (ht : 0 < t) :
    biasedCtsPathMeasure γ β u
        {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal t}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
          Real.exp (-β * γ / 2)) := by
  set θ := biasedConsensusSetOther N γ o
  have hinv : BiasedExitInv γ o u N :=
    biasedExitInv_of_isBiasedConsensus hM (by omega) hγ hγ' hu
  have key := le_biasedCtsPathMeasure_lt_hittingTimeCts γ β (hinv.notMem hM (by omega) hγ')
    fun n => le_biasedCtsPathMeasure_avoidBefore hM hN hγ hγ' hβ o n N u hinv t ht.le
  have hcompl : {ω | biasedHittingTimeCts u θ ω ≤ ENNReal.ofReal t}
      = {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω}ᶜ := by
    ext ω; simp [not_lt]
  have hmeas : MeasurableSet {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω} :=
    measurableSet_lt measurable_const (measurable_biasedHittingTimeCts u θ)
  set z := biasedZeta N M γ β ^ N with hz
  set E := Real.exp (-(biasedExitRate N M γ β * t)) with hE
  have hz0 : 0 ≤ z := pow_nonneg (biasedZeta_pos N M γ β).le N
  have hz1 : z ≤ 1 := pow_le_one₀ (biasedZeta_pos N M γ β).le (biasedZeta_le_one N M γ β)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [biasedExitRate_nonneg N M γ β])
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  calc 1 - biasedCtsPathMeasure γ β u {ω | ENNReal.ofReal t < biasedHittingTimeCts u θ ω}
      ≤ 1 - ENNReal.ofReal (z * E) := tsub_le_tsub_left key 1
    _ = ENNReal.ofReal (1 - z * E) := by
        rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (mul_nonneg hz0 hE0)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        -- Remark 4 for the run to the ladder, and `1 - e^{-x} ≤ x` for the rest
        have hrem := one_sub_le_biasedZeta_pow N M γ β N
        rw [← hz] at hrem
        have hexp := one_sub_exp_neg_le (biasedExitRate N M γ β * t)
        rw [← hE] at hexp
        have hzE : z * (1 - E) ≤ 1 - E := mul_le_of_le_one_left (by linarith) hz1
        have hgoal : (N : ℝ) * (((M * N : ℕ) : ℝ) * Real.exp (-(β * γ / 2)))
            + biasedExitRate N M γ β * t
            = (((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
                Real.exp (-β * γ / 2) := by
          rw [biasedExitRate, show -β * γ / 2 = -(β * γ / 2) by ring]
          push_cast
          ring
        nlinarith

end Lemma29

end Bias

end SocialNetwork
