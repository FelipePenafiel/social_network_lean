/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Ladder sets and consensus sets

Formalisation of Definitions 1, 2 and 4 of arXiv:2607.19651, together with the inclusion
`L ⊆ L̂` recorded in Remark 5.

Everything is stated in the scaled coordinates set up in `SocialNetwork.Defs`: the paper's
condition `u (·, p) = - u (·, o) / (M - 1)` becomes the division-free identity
`(M - 1) * u (a, p) = - u (a, o)`, and the paper's condition `{u (1, o), …, u (N, o)} =
{0, …, N - 1}` becomes the statement that the `o`-th column takes exactly the `N` values
`(M - 1) * k` for `k < N`.

## Main definitions

* `SocialNetwork.IsLadder o u` — the ladder set `L^o` (Definition 1).
* `SocialNetwork.IsConsensus o u` — the consensus set `C^o` (Definition 2).
* `SocialNetwork.IsSteepLadder o u` — the extended ladder set `L̂^o` (Definition 4).

## Main results

* `SocialNetwork.IsLadder.isSteepLadder` — the inclusion `L^o ⊆ L̂^o` of Remark 5.
* `SocialNetwork.IsLadder.isConsensus` — a ladder state is in particular a consensus state.
-/

namespace SocialNetwork

open Finset

variable {N M : ℕ}

/-- The `N` admissible column values of a ladder supporting a fixed opinion: in scaled
coordinates these are `(M - 1) * k` for `k = 0, …, N - 1`. -/
def ladderValues (N M : ℕ) : Finset ℤ :=
  Finset.image (fun k : Actor N => ((M : ℤ) - 1) * (k : ℕ)) Finset.univ

theorem mem_ladderValues_iff {N M : ℕ} {z : ℤ} :
    z ∈ ladderValues N M ↔ ∃ k : Actor N, z = ((M : ℤ) - 1) * (k : ℕ) := by
  simp [ladderValues, eq_comm]

/-- Definition 1: the ladder set `L^o` supporting opinion `o`.

The social pressures for `o` are aligned on a staircase taking each of the values
`0, 1, …, N - 1` exactly once, while the pressure for every other opinion is the
corresponding negative multiple. -/
structure IsLadder (o : Opinion M) (u : Pressure N M) : Prop where
  isState : IsState u
  /-- `{u (1, o), …, u (N, o)} = {0, …, N - 1}`. -/
  column : Finset.image (fun a : Actor N => u a o) Finset.univ = ladderValues N M
  /-- `u (·, p) = - u (·, o) / (M - 1)` for every `p ≠ o`. -/
  other : ∀ a, ∀ p ≠ o, ((M : ℤ) - 1) * u a p = -u a o

/-- Definition 2: the consensus set `C^o`.

Only the sign pattern is imposed: the favoured opinion carries non-negative pressure for
every actor, all other opinions carry non-positive pressure. -/
structure IsConsensus (o : Opinion M) (u : Pressure N M) : Prop where
  isState : IsState u
  ne_zero : u ≠ 0
  nonneg : ∀ a, 0 ≤ u a o
  nonpos : ∀ a, ∀ p ≠ o, u a p ≤ 0

/-- Definition 4: the extended ladder set `L̂^o` of "steep" ladders.

These are the states reachable from `L^o` by repeatedly expressing `o`: the pressures for
`o` stay pairwise distinct integers (in unscaled coordinates), the smallest being `0`, but
they are no longer required to be consecutive. -/
structure IsSteepLadder (o : Opinion M) (u : Pressure N M) : Prop where
  isState : IsState u
  /-- `u (a, o) ∈ ℤ` in the unscaled coordinates of the paper. -/
  dvd : ∀ a, ((M : ℤ) - 1) ∣ u a o
  /-- `u (a₁, o) < u (a₂, o) < … < u (a_N, o)` are pairwise distinct. -/
  injective : Function.Injective fun a : Actor N => u a o
  /-- The smallest pressure for `o` is `0`. -/
  exists_zero : ∃ a, u a o = 0
  other : ∀ a, ∀ p ≠ o, ((M : ℤ) - 1) * u a p = -u a o

section Ladder

variable {o : Opinion M} {u : Pressure N M}

theorem IsLadder.mem_ladderValues (hu : IsLadder o u) (a : Actor N) :
    u a o ∈ ladderValues N M := by
  rw [← hu.column]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ a)

theorem IsLadder.dvd (hu : IsLadder o u) (a : Actor N) : ((M : ℤ) - 1) ∣ u a o := by
  obtain ⟨k, hk⟩ := mem_ladderValues_iff.1 (hu.mem_ladderValues a)
  exact ⟨(k : ℕ), hk⟩

theorem IsLadder.exists_zero (hu : IsLadder o u) [NeZero N] : ∃ a, u a o = 0 := by
  have h0 : (0 : ℤ) ∈ ladderValues N M := by
    refine mem_ladderValues_iff.2 ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, ?_⟩
    simp
  rw [← hu.column] at h0
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h0
  exact ⟨a, ha⟩

theorem one_lt_of_two_le (hM : 2 ≤ M) : (0 : ℤ) < (M : ℤ) - 1 := by
  have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  omega

/-- On a ladder, the `o`-th column is injective: it realises `N` distinct values. -/
theorem IsLadder.injective (hM : 2 ≤ M) (hu : IsLadder o u) :
    Function.Injective fun a : Actor N => u a o := by
  have hM' : ((M : ℤ) - 1) ≠ 0 := ne_of_gt (one_lt_of_two_le hM)
  have hstep : Function.Injective fun k : Actor N => ((M : ℤ) - 1) * (k : ℕ) := by
    intro i j hij
    have h := mul_left_cancel₀ hM' hij
    exact Fin.val_injective (by exact_mod_cast h)
  have hcard : (Finset.image (fun a : Actor N => u a o) Finset.univ).card
      = (Finset.univ : Finset (Actor N)).card := by
    rw [hu.column, ladderValues, Finset.card_image_of_injective _ hstep]
  have hinj : Set.InjOn (fun a : Actor N => u a o) (Finset.univ : Finset (Actor N)) :=
    Finset.card_image_iff.1 hcard
  intro i j hij
  exact hinj (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- Remark 5: `L^o ⊆ L̂^o`. -/
theorem IsLadder.isSteepLadder (hM : 2 ≤ M) [NeZero N] (hu : IsLadder o u) :
    IsSteepLadder o u where
  isState := hu.isState
  dvd := hu.dvd
  injective := hu.injective hM
  exists_zero := hu.exists_zero
  other := hu.other

/-- On a ladder every actor carries non-negative pressure for the supported opinion. -/
theorem IsLadder.nonneg (hM : 2 ≤ M) (hu : IsLadder o u) (a : Actor N) : 0 ≤ u a o := by
  obtain ⟨k, hk⟩ := mem_ladderValues_iff.1 (hu.mem_ladderValues a)
  rw [hk]
  exact mul_nonneg (le_of_lt (one_lt_of_two_le hM)) (Int.natCast_nonneg _)

/-- On a ladder every actor carries non-positive pressure for the other opinions. -/
theorem IsLadder.nonpos (hM : 2 ≤ M) (hu : IsLadder o u) (a : Actor N) {p : Opinion M}
    (hp : p ≠ o) : u a p ≤ 0 := by
  have hpos := one_lt_of_two_le (M := M) hM
  have heq := hu.other a p hp
  have hge := hu.nonneg hM a
  have h1 : ((M : ℤ) - 1) * u a p ≤ ((M : ℤ) - 1) * 0 := by
    rw [heq, mul_zero]; linarith
  exact le_of_mul_le_mul_left h1 hpos

/-- A ladder supporting `o` is in particular a consensus state for `o` (Definition 2 is
weaker than Definition 1). -/
theorem IsLadder.isConsensus (hM : 2 ≤ M) (hN : 2 ≤ N) (hu : IsLadder o u) :
    IsConsensus o u where
  isState := hu.isState
  ne_zero := by
    have hNpos : 0 < N := lt_of_lt_of_le two_pos hN
    have hmem : ((M : ℤ) - 1) * ((N - 1 : ℕ) : ℤ) ∈ ladderValues N M :=
      mem_ladderValues_iff.2 ⟨⟨N - 1, Nat.sub_lt hNpos one_pos⟩, rfl⟩
    rw [← hu.column] at hmem
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hmem
    intro hzero
    have hposM := one_lt_of_two_le (M := M) hM
    have hposN : (0 : ℤ) < ((N - 1 : ℕ) : ℤ) := by
      have : 1 ≤ N - 1 := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have : u a o = 0 := by rw [hzero]; rfl
    rw [this] at ha
    nlinarith [ha.symm]
  nonneg := hu.nonneg hM
  nonpos := hu.nonpos hM

/-- A consensus state carries a strictly positive pressure for the favoured opinion. This
is the remark made just after Definition 2: were column `o` identically zero, the vanishing
row sums would force the whole matrix to vanish, which `C^o` excludes. -/
theorem IsConsensus.exists_pos (hv : IsConsensus o u) : ∃ a, 0 < u a o := by
  by_contra hno
  refine hv.ne_zero (funext fun a => funext fun p => ?_)
  have hnonpos : ∀ q, u a q ≤ 0 := by
    intro q
    by_cases hq : q = o
    · subst hq; exact not_lt.mp fun h => hno ⟨a, h⟩
    · exact hv.nonpos a q hq
  have hsum : ∑ q, u a q = 0 := hv.isState.trust_eq_zero a
  exact (Finset.sum_eq_zero_iff_of_nonpos fun q _ => hnonpos q).mp hsum p (Finset.mem_univ p)

/-- Expressing the favoured opinion keeps the state in the consensus set. -/
theorem IsConsensus.express (hM : 2 ≤ M) (hN : 2 ≤ N) (hv : IsConsensus o u) (a : Actor N) :
    IsConsensus o (SocialNetwork.express a o u) := by
  have hM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  refine ⟨hv.isState.express a o, ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b : Actor N, b ≠ a := by
      have h0 : (0 : ℕ) < N := by omega
      have h1 : (1 : ℕ) < N := by omega
      by_cases ha : (a : ℕ) = 0
      · refine ⟨⟨1, h1⟩, fun h => ?_⟩; rw [← h] at ha; simp at ha
      · refine ⟨⟨0, h0⟩, fun h => ?_⟩; rw [← h] at ha; simp at ha
    intro hzero
    have h1 : SocialNetwork.express a o u b o = 0 := by rw [hzero]; rfl
    rw [express_of_ne_of_eq hb] at h1
    have := hv.nonneg b
    omega
  · intro b
    by_cases hb : b = a
    · subst hb; simp
    · rw [express_of_ne_of_eq hb]
      have := hv.nonneg b
      omega
  · intro b p hp
    by_cases hb : b = a
    · subst hb; simp
    · rw [express_of_ne_of_ne hb hp]
      have := hv.nonpos b p hp
      omega

end Ladder

end SocialNetwork
