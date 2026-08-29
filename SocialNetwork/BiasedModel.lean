/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Bias
import SocialNetwork.Ladder
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The biased model of Section 3, assembled into a network state

`SocialNetwork.Bias` supplies the memory `(nₐ, cₚ)` of a single actor and the row formula of
equation (6).  This file assembles those rows into a network state, so that the operator
`π_α^{a,o}` of equation (5), the state space `S^α` of equation (6), and the sets `C_α^o` and
`L_α^o` of equations (8) and (9) all become available.

## The state space, and a correction to equation (6)

Equation (6) describes `S^α` by two conditions on the memory profile: some actor has heard
nothing (`min_a ‖u (a, ·)‖_∞ = 0`), and `∑_a nₐ ≥ N (N-1) / 2`.  The justification given for
the second is that the actors cannot express simultaneously, so their `nₐ` are the times
elapsed since `N` distinct moments, and therefore `∑_a nₐ ≥ 0 + 1 + ⋯ + (N-1)`.

That justification proves something strictly stronger than the stated condition, and the
strengthening is needed: **the condition `∑_a nₐ ≥ N (N-1) / 2` is not stable under
`π_α^{a,o}`.**  Expressing sets `nₐ` to `0` and adds one to every other `n_b`, so the sum
changes by `(N-1) - nₐ`, which is negative when the expressing actor had heard a lot.  For
`N = 3`, the profile `n = (0, 0, 3)` has sum `3 = N (N-1) / 2`, and expressing from the third
actor gives `n = (1, 1, 0)`, of sum `2 < 3`.

What *is* stable is the property the justification actually establishes: the `nₐ` are
**pairwise distinct**.  Expressing replaces `{n_b : b ≠ a}` by `{n_b + 1 : b ≠ a}`, all at
least one, and adds `nₐ ↦ 0`, so distinctness is preserved.  Distinctness together with the
first condition implies the paper's bound, so nothing is lost:
`SocialNetwork.Bias.IsBiasedState.two_mul_totalHeard_ge`.

`SocialNetwork.Bias.IsBiasedState` therefore takes distinctness as its second field.

## Main definitions

* `SocialNetwork.Bias.Profile` — one memory per actor.
* `SocialNetwork.Bias.Profile.pressure` — the matrix of equation (6).
* `SocialNetwork.Bias.Profile.express` — the operator `π_α^{a,o}` of equation (5).
* `SocialNetwork.Bias.IsBiasedState` — the state space `S^α` of equation (6).
* `SocialNetwork.Bias.IsBiasedConsensus` — `C_α^o` of equation (8).
* `SocialNetwork.Bias.IsBiasedLadder` — `L_α^o` of equation (9).
* `SocialNetwork.Bias.IsBiasedSteepLadder` — `L̂_α` of Appendix C.

## Main results

* `SocialNetwork.Bias.IsBiasedState.express` — **Remark 1**, stability of `S^α`, proved.
* `SocialNetwork.Bias.Profile.pressure_mem_addSubgroup` — **Remark 1**,
  `u (a, p) ∈ ℤ + γℤ`, proved.
* `SocialNetwork.Bias.IsBiasedState.pressure_ne_zero` — **Remark 1**, `0 ∉ S^α` when
  `(M-1) α ≠ 0`, proved.
* `SocialNetwork.Bias.pressure_lt_pressure_hear_of_neg` — **Remark 2**, the degeneracy for
  `α > 1/(M-1)`, proved.
* `SocialNetwork.Bias.IsBiasedState.two_mul_totalHeard_ge` — **equation (6)**, the bound
  `2 ∑_a nₐ ≥ N (N-1)`, proved, via `SocialNetwork.Bias.sum_range_card_le_sum`.
* `SocialNetwork.Bias.le_max_pressure` — **Remark 8**, the lower bound `(M-1) α` on the
  maximum of a non-null row, unproved.
-/

namespace SocialNetwork

namespace Bias

open Finset

variable {N M : ℕ}

/-! ### Profiles -/

section Profile

/-- The memory of the whole network: one variable-length memory per actor. -/
abbrev Profile (N M : ℕ) := Actor N → Memory M

/-- `nₐ`, the number of expressions actor `a` has heard since it last expressed. -/
def Profile.heard (P : Profile N M) (a : Actor N) : ℕ := (P a).heard

/-- `∑_a nₐ`, the quantity equation (6) bounds below. -/
def Profile.totalHeard (P : Profile N M) : ℕ := ∑ a, P.heard a

/-- The matrix of social pressures of equation (6):
`u (a, p) = cₚ (1 + γ) - γ nₐ`, with `γ = 1/(M-1) - α`. -/
def Profile.pressure (γ : ℝ) (P : Profile N M) (a : Actor N) (p : Opinion M) : ℝ :=
  (P a).pressure γ p

/-- **Equation (5)**, the operator `π_α^{a,o}` on the whole network: the expressing actor's
memory is reset, everybody else hears one expression of `o`. -/
def Profile.express (a : Actor N) (o : Opinion M) (P : Profile N M) : Profile N M :=
  fun b => if b = a then Memory.reset M else Memory.hear o (P b)

@[simp]
theorem Profile.express_self (a : Actor N) (o : Opinion M) (P : Profile N M) :
    Profile.express a o P a = Memory.reset M := by simp [Profile.express]

theorem Profile.express_of_ne {a b : Actor N} (hb : b ≠ a) (o : Opinion M) (P : Profile N M) :
    Profile.express a o P b = Memory.hear o (P b) := by simp [Profile.express, hb]

@[simp]
theorem Profile.heard_express_self (a : Actor N) (o : Opinion M) (P : Profile N M) :
    (Profile.express a o P).heard a = 0 := by simp [Profile.heard]

theorem Profile.heard_express_of_ne {a b : Actor N} (hb : b ≠ a) (o : Opinion M)
    (P : Profile N M) : (Profile.express a o P).heard b = P.heard b + 1 := by
  simp [Profile.heard, Profile.express_of_ne hb]

/-- **Equation (5)** at the level of the pressure matrix: expressing resets the expressing
actor's row and moves every other row by `+1` on the expressed opinion and `-γ` elsewhere.
This is `SocialNetwork.Bias.Memory.pressure_hear` read on the network. -/
theorem Profile.pressure_express (γ : ℝ) (a : Actor N) (o : Opinion M) (P : Profile N M)
    (b : Actor N) (p : Opinion M) :
    (Profile.express a o P).pressure γ b p
      = if b = a then 0 else P.pressure γ b p + (if p = o then 1 else -γ) := by
  by_cases hb : b = a
  · subst hb; simp [Profile.pressure, Profile.express]
  · rw [if_neg hb, Profile.pressure, Profile.express_of_ne hb, Memory.pressure_hear]
    rfl

end Profile

/-! ### The state space `S^α` of equation (6) -/

section State

/-- **Equation (6)**, the state space `S^α`, taken on the memory profile rather than on the
matrix.

The second field is the paper's justification for its `∑_a nₐ ≥ N (N-1)/2` rather than that
inequality itself; see the module docstring for why the inequality alone is not stable and
distinctness is. -/
structure IsBiasedState (P : Profile N M) : Prop where
  /-- `min_a ‖u (a, ·)‖_∞ = 0`: some actor has heard nothing since it last expressed. -/
  exists_zero_row : ∃ a, P.heard a = 0
  /-- The actors last expressed at distinct moments, so their `nₐ` are pairwise distinct. -/
  injective_heard : Function.Injective P.heard

/-- Stability of `S^α` under every `π_α^{a,o}`: the first half of **Remark 1**. -/
theorem IsBiasedState.express {P : Profile N M} (hP : IsBiasedState P) (a : Actor N)
    (o : Opinion M) : IsBiasedState (Profile.express a o P) := by
  refine ⟨⟨a, by simp⟩, fun b c hbc => ?_⟩
  by_cases hb : b = a <;> by_cases hc : c = a
  · rw [hb, hc]
  · rw [hb, Profile.heard_express_self, Profile.heard_express_of_ne hc] at hbc
    omega
  · rw [hc, Profile.heard_express_self, Profile.heard_express_of_ne hb] at hbc
    omega
  · rw [Profile.heard_express_of_ne hb, Profile.heard_express_of_ne hc] at hbc
    exact hP.injective_heard (by omega)

/-- A finite set of `n` naturals has sum at least `0 + 1 + ⋯ + (n-1)`.

**No counterpart in the paper**, which uses this implication without proving it — see
`SocialNetwork.Bias.IsBiasedState.two_mul_totalHeard_ge`, whose argument *is* the paper's.

Mathlib has no lemma to this effect.  The route it suggests — enumerate the set in increasing
order with `Finset.orderEmbOfFin`, then observe that a strictly monotone `Fin n → ℕ` dominates
the identity — needs that last step redone by hand, because `StrictMono.le_apply` is stated
only for endomorphisms `β → β`.  Induction on the largest element avoids it altogether:
adjoining a new maximum `a` to `s` adds `a` to the sum and `#s` to the bound, and `a ≥ #s`
because `s ⊆ range a`. -/
theorem sum_range_card_le_sum (s : Finset ℕ) : ∑ i ∈ Finset.range s.card, i ≤ ∑ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
      have hmem : a ∉ s := fun h => lt_irrefl a (ha a h)
      have hcard : s.card ≤ a := by
        have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
        simpa using Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hmem, Finset.sum_insert hmem, Finset.sum_range_succ]
      omega

/-- The sum of `N` pairwise distinct naturals is at least `0 + 1 + ⋯ + (N-1)`.

The `N` values are distinct, so they form a `Finset ℕ` of cardinality `N` with the same sum;
`SocialNetwork.Bias.sum_range_card_le_sum` bounds it. -/
theorem sum_ge_of_injective {f : Actor N → ℕ} (hf : Function.Injective f) :
    ∑ i ∈ Finset.range N, i ≤ ∑ a, f a := by
  classical
  have hcard : (Finset.univ.image f).card = N := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  calc ∑ i ∈ Finset.range N, i
      = ∑ i ∈ Finset.range (Finset.univ.image f).card, i := by rw [hcard]
    _ ≤ ∑ x ∈ Finset.univ.image f, x := sum_range_card_le_sum _
    _ = ∑ a, f a := Finset.sum_image fun x _ y _ h => hf h

/-- **Equation (6)**, the bound the paper states: `2 ∑_a nₐ ≥ N (N-1)`, cleared of its
division by two.  It follows from the distinctness of the `nₐ`.

This is **the paper's own argument**: the actors cannot express simultaneously, so the `nₐ`
count the time since `N` distinct moments and are pairwise distinct, whence the bound.  The
step the paper leaves implicit — that `N` distinct naturals sum to at least `0 + 1 + ⋯ +
(N-1)` — is `SocialNetwork.Bias.sum_ge_of_injective`. -/
theorem IsBiasedState.two_mul_totalHeard_ge {P : Profile N M} (hP : IsBiasedState P) :
    N * (N - 1) ≤ 2 * P.totalHeard := by
  have h := sum_ge_of_injective hP.injective_heard
  have h2 : (∑ i ∈ Finset.range N, i) * 2 = N * (N - 1) := Finset.sum_range_id_mul_two N
  have ht : P.totalHeard = ∑ a, P.heard a := rfl
  omega

end State

/-! ### Remark 1: the arithmetic of a row -/

section Remark1

/-- **Remark 1**: `u (a, p) = cₚ + γ (cₚ - nₐ) ∈ ℤ + γ ℤ`.

The membership is exhibited by the two integers `cₚ` and `cₚ - nₐ`. -/
theorem Profile.pressure_eq_add_mul (γ : ℝ) (P : Profile N M) (a : Actor N) (p : Opinion M) :
    P.pressure γ a p
      = (((P a).count p : ℤ) : ℝ) + γ * ((((P a).count p : ℤ) : ℝ) - (((P a).heard : ℤ) : ℝ)) := by
  simp only [Profile.pressure, Memory.pressure]
  push_cast
  ring

/-- **Remark 1**: every entry lies in the subgroup `ℤ + γℤ` of `ℝ`. -/
theorem Profile.pressure_mem_addSubgroup (γ : ℝ) (P : Profile N M) (a : Actor N)
    (p : Opinion M) :
    ∃ j k : ℤ, P.pressure γ a p = (j : ℝ) + γ * (k : ℝ) :=
  ⟨((P a).count p : ℤ), ((P a).count p : ℤ) - ((P a).heard : ℤ), by
    rw [Profile.pressure_eq_add_mul]; push_cast; ring⟩

/-- **Remark 1**: the trust of an actor is `nₐ (M-1) α`. -/
theorem Profile.sum_pressure_eq (γ α : ℝ) (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α)
    (P : Profile N M) (a : Actor N) :
    ∑ p, P.pressure γ a p = ((P a).heard : ℝ) * (((M : ℝ) - 1) * α) :=
  Memory.sum_pressure_eq γ α h (P a)

/-- **Remark 1**: a row vanishes if the actor has heard nothing. -/
theorem Profile.pressure_eq_zero_of_heard_eq_zero (γ : ℝ) {P : Profile N M} {a : Actor N}
    (ha : P.heard a = 0) (p : Opinion M) : P.pressure γ a p = 0 :=
  Memory.pressure_eq_zero_of_heard_eq_zero γ ha p

/-- **Remark 1**, the converse: when `(M-1) α ≠ 0`, a row vanishes *only* if the actor has
heard nothing, because a balanced row with `nₐ ≥ 1` has trust `nₐ (M-1) α ≠ 0`. -/
theorem Profile.heard_eq_zero_of_pressure_eq_zero (γ α : ℝ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : ((M : ℝ) - 1) * α ≠ 0)
    {P : Profile N M} {a : Actor N} (hzero : ∀ p, P.pressure γ a p = 0) : P.heard a = 0 := by
  have hsum := Profile.sum_pressure_eq γ α h P a
  rw [Finset.sum_congr rfl fun p _ => hzero p] at hsum
  simp only [Finset.sum_const_zero] at hsum
  have : ((P a).heard : ℝ) = 0 := by
    rcases mul_eq_zero.1 hsum.symm with h1 | h2
    · exact h1
    · exact absurd h2 hα
  exact_mod_cast this

/-- **Remark 1**: `0 ∉ S^α` when `(M-1) α ≠ 0`.

If every row vanished, every actor would have heard nothing, so all the `nₐ` would be equal —
contradicting their distinctness as soon as there are two actors. -/
theorem IsBiasedState.pressure_ne_zero (hN : 2 ≤ N) (γ α : ℝ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : ((M : ℝ) - 1) * α ≠ 0)
    {P : Profile N M} (hP : IsBiasedState P) : ∃ a p, P.pressure γ a p ≠ 0 := by
  by_contra hno
  push_neg at hno
  have hall : ∀ a, P.heard a = 0 := fun a =>
    Profile.heard_eq_zero_of_pressure_eq_zero γ α h hα fun p => hno a p
  have h0 : (⟨0, by omega⟩ : Actor N) ≠ (⟨1, by omega⟩ : Actor N) := by
    simp [Fin.ext_iff]
  exact h0 (hP.injective_heard (by rw [hall, hall]))

end Remark1

/-! ### Remark 2: the degenerate regimes -/

section Remark2

/-- **Remark 2**, first half.  When `α > 1/(M-1)`, that is `γ < 0`, every expression raises
the social pressure of every listener for *every* opinion, so no opinion can ever acquire the
negative pressure that Definition 2 asks of a consensus. -/
theorem pressure_lt_pressure_hear_of_neg {γ : ℝ} (hγ : γ < 0) (o : Opinion M) (m : Memory M)
    (p : Opinion M) : m.pressure γ p < (Memory.hear o m).pressure γ p := by
  rw [Memory.pressure_hear]
  by_cases hp : p = o
  · simp [hp]
  · simp only [hp, if_false]
    linarith

/-- **Remark 2**, second half.  When `α ≥ 1 + 1/(M-1)`, that is `γ ≤ -1`, an expression of `o`
raises the pressure for every *other* opinion by at least as much as it raises the pressure
for `o` itself: the expression supports the opinions it does not name. -/
theorem le_pressure_hear_of_le_neg_one {γ : ℝ} (hγ : γ ≤ -1) (o : Opinion M) (m : Memory M)
    {p : Opinion M} (hp : p ≠ o) :
    (Memory.hear o m).pressure γ o - m.pressure γ o
      ≤ (Memory.hear o m).pressure γ p - m.pressure γ p := by
  rw [Memory.pressure_hear, Memory.pressure_hear, if_pos rfl, if_neg hp]
  linarith

end Remark2

/-! ### Remark 8: the maximum of a non-null row -/

section Remark8

/-- Some opinion has been heard at least `⌈nₐ / M⌉` times: the pigeonhole behind Remark 8. -/
theorem exists_count_ge (hM : 0 < M) (m : Memory M) : ∃ p, m.heard ≤ M * m.count p := by
  haveI : NeZero M := ⟨by omega⟩
  by_contra hno
  push_neg at hno
  have hne : (Finset.univ : Finset (Opinion M)).Nonempty := Finset.univ_nonempty
  have hsum : ∑ p : Opinion M, M * m.count p < ∑ _p : Opinion M, m.heard :=
    Finset.sum_lt_sum_of_nonempty hne fun p _ => hno p
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  rw [show (∑ p : Opinion M, m.count p) = m.heard from rfl] at hsum
  omega

/-- The identity behind Remark 8, in the paper's decomposition.  With `cₚ` expressions of `p`
heard out of `nₐ` in total,

```
cₚ (1 + γ) - γ nₐ = cₚ (M-1) α + γ (M cₚ - nₐ).
```

This is the paper's `k (1+γ) - γ nₐ = k (M-1) α + γ (M - r)`, written without introducing the
remainder: with `nₐ = (k-1) M + r` the two right-hand sides agree term by term, since
`M k - nₐ = M - r`. -/
theorem pressure_eq_of_bias {γ α : ℝ}
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (m : Memory M) (p : Opinion M) :
    m.pressure γ p
      = (m.count p : ℝ) * (((M : ℝ) - 1) * α)
        + γ * ((M : ℝ) * (m.count p : ℝ) - (m.heard : ℝ)) := by
  have hα : ((M : ℝ) - 1) * α = 1 - ((M : ℝ) - 1) * γ := by linarith
  show (m.count p : ℝ) * (1 + γ) - γ * (m.heard : ℝ) = _
  rw [hα]; ring

/-- **Remark 8.**  For `0 < α < 1/(M-1)` and an actor with `nₐ ≥ 1`,

```
max_{p ∈ O} u (a, p) ≥ (M-1) α,
```

with equality exactly for an actor that has heard one expression of each opinion.  In
particular the jump rate out of any non-null state is at least `e^{β (M-1) α}`, which is what
replaces the bound `e^{β/(M-1)}` of the unbiased model.

Follows the paper's proof: the pigeonhole step is `SocialNetwork.Bias.exists_count_ge`, which
supplies an opinion heard at least `k = ⌈nₐ/M⌉` times, and the arithmetic is
`SocialNetwork.Bias.pressure_eq_of_bias`.  Both terms of that identity are then non-negative —
`M cₚ ≥ nₐ` is the pigeonhole bound and `γ > 0`, which is the paper's `γ (M - r) ≥ 0` — and the
first is at least `(M-1) α` because `cₚ ≥ 1`, which is the paper's `k ≥ 1`.

**Supplies a step the paper asserts**: that `k ≥ 1`, which the written proof reads off `nₐ ≥ 1`
without comment.  Here it comes from `nₐ ≤ M cₚ`: were `cₚ` zero, no expression would have been
heard at all. -/
theorem le_max_pressure (hM : 2 ≤ M) {γ α : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) {P : Profile N M}
    {a : Actor N} (ha : 1 ≤ P.heard a) :
    ∃ p, ((M : ℝ) - 1) * α ≤ P.pressure γ a p := by
  obtain ⟨p, hp⟩ := exists_count_ge (by omega : 0 < M) (P a)
  refine ⟨p, ?_⟩
  -- `k ≥ 1`: the actor has heard something, and every expression it heard concerned some
  -- opinion, so the opinion the pigeonhole selects was heard at least once.
  have hc1 : 1 ≤ (P a).count p := by
    rcases Nat.eq_zero_or_pos ((P a).count p) with hc | hc
    · rw [hc, Nat.mul_zero] at hp
      have : 1 ≤ (P a).heard := ha
      omega
    · exact hc
  have hM1 : (1 : ℝ) ≤ (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hcR : (1 : ℝ) ≤ ((P a).count p : ℝ) := by exact_mod_cast hc1
  have hnR : ((P a).heard : ℝ) ≤ (M : ℝ) * ((P a).count p : ℝ) := by exact_mod_cast hp
  have hαM : 0 < ((M : ℝ) - 1) * α := mul_pos (by linarith) hα
  show ((M : ℝ) - 1) * α ≤ (P a).pressure γ p
  rw [pressure_eq_of_bias h]
  -- `γ (M cₚ - nₐ) ≥ 0`, the paper's `γ (M - r) ≥ 0`
  have hrem : 0 ≤ γ * ((M : ℝ) * ((P a).count p : ℝ) - ((P a).heard : ℝ)) :=
    mul_nonneg hγ.le (by linarith)
  -- `cₚ (M-1) α ≥ (M-1) α`, the paper's `k (M-1) α ≥ (M-1) α`
  have hlead : ((M : ℝ) - 1) * α ≤ ((P a).count p : ℝ) * (((M : ℝ) - 1) * α) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hcR) hαM.le]
  linarith

end Remark8

/-! ### The consensus and ladder sets of equations (8) and (9) -/

section Sets

variable (γ : ℝ)

/-- **Equation (8)**, the consensus set `C_α^o`: the favoured opinion carries non-negative
pressure for every actor, every other opinion carries non-positive pressure, and the state is
not the null matrix — which, by Remark 1, is automatic in `S^α` when `(M-1) α ≠ 0`. -/
structure IsBiasedConsensus (o : Opinion M) (P : Profile N M) : Prop where
  isBiasedState : IsBiasedState P
  ne_zero : ∃ a p, P.pressure γ a p ≠ 0
  nonneg : ∀ a, 0 ≤ P.pressure γ a o
  nonpos : ∀ a, ∀ p ≠ o, P.pressure γ a p ≤ 0

/-- **Equation (9)**, the ladder set `L_α^o`: the pressures for `o` are `0, 1, …, N-1`, and
every other column is `-γ` times the `o`-column. -/
structure IsBiasedLadder (o : Opinion M) (P : Profile N M) : Prop where
  isBiasedState : IsBiasedState P
  /-- `{u (1, o), …, u (N, o)} = {0, …, N-1}`. -/
  column : Finset.image (fun a : Actor N => P.pressure γ a o) Finset.univ
      = Finset.image (fun k : Actor N => ((k : ℕ) : ℝ)) Finset.univ
  /-- `u (·, p) = -γ u (·, o)` for `p ≠ o`. -/
  other : ∀ a, ∀ p ≠ o, P.pressure γ a p = -γ * P.pressure γ a o

/-- The extended ladder set `L̂_α` of Appendix C: the pressures for `o` are pairwise distinct
non-negative integers with smallest value `0`, and the other columns are `-γ` times the
`o`-column. -/
structure IsBiasedSteepLadder (o : Opinion M) (P : Profile N M) : Prop where
  isBiasedState : IsBiasedState P
  /-- `u (a, o) ∈ ℤ`. -/
  isInt : ∀ a, ∃ k : ℤ, P.pressure γ a o = (k : ℝ)
  injective : Function.Injective fun a : Actor N => P.pressure γ a o
  exists_zero : ∃ a, P.pressure γ a o = 0
  nonneg : ∀ a, 0 ≤ P.pressure γ a o
  other : ∀ a, ∀ p ≠ o, P.pressure γ a p = -γ * P.pressure γ a o

/-- `S^α`, as a set of profiles. -/
def biasedStateSet (N M : ℕ) : Set (Profile N M) := {P | IsBiasedState P}

/-- `C_α^o`, as a set of profiles. -/
def biasedConsensusSet (N : ℕ) {M : ℕ} (γ : ℝ) (o : Opinion M) : Set (Profile N M) :=
  {P | IsBiasedConsensus γ o P}

/-- `C_α^{-o} = ⋃_{p ≠ o} C_α^p`. -/
def biasedConsensusSetOther (N : ℕ) {M : ℕ} (γ : ℝ) (o : Opinion M) : Set (Profile N M) :=
  {P | ∃ p, p ≠ o ∧ IsBiasedConsensus γ p P}

/-- `L_α = ⋃_o L_α^o`, as a set of profiles. -/
def biasedLadderSet (N M : ℕ) (γ : ℝ) : Set (Profile N M) := {P | ∃ o, IsBiasedLadder γ o P}

/-- `L̂_α = ⋃_o L̂_α^o`, as a set of profiles. -/
def biasedSteepLadderSet (N M : ℕ) (γ : ℝ) : Set (Profile N M) :=
  {P | ∃ o, IsBiasedSteepLadder γ o P}

/-- The set `B_N^α = {u ∈ S^α : max {u (a, o)} ≤ N}` of Section 5.4, in which Proposition 17
confines the process. -/
def biasedBounded (N M : ℕ) (γ : ℝ) : Set (Profile N M) :=
  {P | IsBiasedState P ∧ ∀ a p, P.pressure γ a p ≤ (N : ℝ)}

end Sets

/-! ### Remark 5 for the biased model: `L_α ⊆ L̂_α` -/

section BiasedLadder

variable {γ : ℝ} {o : Opinion M} {P : Profile N M}

/-- On a biased ladder the pressure an actor carries for the supported opinion is one of the
`N` values `0, 1, …, N-1`.  This is the `column` field read at a single actor. -/
theorem IsBiasedLadder.exists_eq_natCast (hP : IsBiasedLadder γ o P) (a : Actor N) :
    ∃ k : Actor N, P.pressure γ a o = ((k : ℕ) : ℝ) := by
  have hmem : P.pressure γ a o
      ∈ Finset.image (fun b : Actor N => P.pressure γ b o) Finset.univ :=
    Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [hP.column] at hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmem
  exact ⟨k, hk.symm⟩

/-- On a biased ladder the `o`-column is integer-valued. -/
theorem IsBiasedLadder.isInt (hP : IsBiasedLadder γ o P) (a : Actor N) :
    ∃ k : ℤ, P.pressure γ a o = (k : ℝ) := by
  obtain ⟨k, hk⟩ := hP.exists_eq_natCast a
  exact ⟨((k : ℕ) : ℤ), by rw [hk]; push_cast; ring⟩

/-- On a biased ladder every actor carries non-negative pressure for the supported opinion. -/
theorem IsBiasedLadder.nonneg (hP : IsBiasedLadder γ o P) (a : Actor N) :
    0 ≤ P.pressure γ a o := by
  obtain ⟨k, hk⟩ := hP.exists_eq_natCast a
  rw [hk]
  exact Nat.cast_nonneg _

/-- On a biased ladder some actor carries no pressure for the supported opinion: the value `0`
is one of the `N` the column realises. -/
theorem IsBiasedLadder.exists_zero [NeZero N] (hP : IsBiasedLadder γ o P) :
    ∃ a, P.pressure γ a o = 0 := by
  have h0 : (0 : ℝ) ∈ Finset.image (fun k : Actor N => ((k : ℕ) : ℝ)) Finset.univ :=
    Finset.mem_image.2 ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, Finset.mem_univ _, by simp⟩
  rw [← hP.column] at h0
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h0
  exact ⟨a, ha⟩

/-- On a biased ladder the `o`-column is injective: it realises `N` distinct values.  This is
the unbiased `SocialNetwork.IsLadder.injective` transported to the memory representation. -/
theorem IsBiasedLadder.injective (hP : IsBiasedLadder γ o P) :
    Function.Injective fun a : Actor N => P.pressure γ a o := by
  have hstep : Function.Injective fun k : Actor N => ((k : ℕ) : ℝ) := by
    intro i j hij
    have hcast : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := hij
    exact Fin.val_injective (by exact_mod_cast hcast)
  have hcard : (Finset.image (fun a : Actor N => P.pressure γ a o) Finset.univ).card
      = (Finset.univ : Finset (Actor N)).card := by
    rw [hP.column, Finset.card_image_of_injective _ hstep]
  have hinj : Set.InjOn (fun a : Actor N => P.pressure γ a o)
      (Finset.univ : Finset (Actor N)) := Finset.card_image_iff.1 hcard
  exact fun i j hij => hinj (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- **Remark 5 for the biased model** (Appendix C): `L_α^o ⊆ L̂_α^o`.

**No counterpart in the paper**, which states the inclusion for the unbiased model only and
transfers it to Appendix C without comment.  The argument is the unbiased one of
`SocialNetwork.IsLadder.isSteepLadder`: a column taking each of `0, 1, …, N-1` exactly once is
in particular an injective, non-negative, integer-valued column whose minimum is `0`. -/
theorem IsBiasedLadder.isBiasedSteepLadder [NeZero N] (hP : IsBiasedLadder γ o P) :
    IsBiasedSteepLadder γ o P where
  isBiasedState := hP.isBiasedState
  isInt := hP.isInt
  injective := hP.injective
  exists_zero := hP.exists_zero
  nonneg := hP.nonneg
  other := hP.other

/-- **Remark 5 for the biased model** (Appendix C): `L_α ⊆ L̂_α`. -/
theorem biasedLadderSet_subset_biasedSteepLadderSet [NeZero N] :
    biasedLadderSet N M γ ⊆ biasedSteepLadderSet N M γ :=
  fun _ ⟨o, hP⟩ => ⟨o, hP.isBiasedSteepLadder⟩

end BiasedLadder

end Bias

end SocialNetwork
