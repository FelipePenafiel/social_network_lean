/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Consensus
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Definition 5, the first-repeat time, and the road to Proposition 7

Appendix A of arXiv:2607.19651 proves Proposition 7 in three moves: Lemma 19 takes an
arbitrary state of `S` to the set `S^o` of Definition 5 at the first repeat time `τ(u)`,
Lemma 20 takes `S^o` to a consensus set `C^o`, and a final step takes `C^o` to a ladder
`L^o`. The last of these is `SocialNetwork.isLadder_state`.

This file supplies the vocabulary of Appendix A — Definition 5 and `τ(u)` — together with
the two components of Lemma 20 that are independent of its induction: that a greedy
expression in a state of `S^o` expresses `o`, and the closing implication that lands in
`C^o`.

## Scaled coordinates

Definition 5 asks for `r ∈ [0, 1)`. Multiplying by `M - 1`, this becomes an integer
`ρ ∈ [0, M - 1)`, since every quantity the paper's own construction feeds into `r` — it
takes `r = m - ⌊m⌋` for `m` an entry of the matrix — lies in `(1/(M-1))ℤ`. The two
conditions of Definition 5 then read

```
(M - 1) * j + ρ ≤ u (aⱼ, o)          and          u (b, p) ≤ (M - 1) * n + ρ - 1
```

with no division anywhere.

## Main definitions

* `SocialNetwork.IsFavouringWith` / `SocialNetwork.IsFavouring` — Definition 5, `S^o`.
* `SocialNetwork.firstRepeat` — the paper's `τ(u)`, shifted to this file's index
  convention: `firstRepeat T` is the paper's `τ(u) - 1`.

## Main results

* `SocialNetwork.firstRepeat_le` — `τ(u) ≤ N + 1`, the bound stated after Definition 5.
* `SocialNetwork.opinion_eq_of_isMax_of_favouring` — in a state of `S^o` a maximising pair
  lies in column `o`, so a greedy expression expresses `o`. This is the step the proof of
  Lemma 20 opens with.
* `SocialNetwork.isConsensus_of_nonpos` — a state of `S` whose columns other than `o` are
  non-positive is a consensus state for `o`. This is the step the proof of Lemma 20 closes
  with, once the bound on the other columns has become negative.
-/

namespace SocialNetwork

open Finset

variable {N M : ℕ}

/-- Definition 5 for an explicit witness `(n, ρ, a)`: `n` actors `a 0, …, a (n-1)` — the
paper's `a₁(u), …, a_{n(u)}(u)` — carry pressure at least `j + r` for opinion `o`, while no
actor carries more than `n + r - 1/(M-1)` for any other opinion. -/
structure IsFavouringWith (o : Opinion M) (u : Pressure N M) (n : ℕ) (ρ : ℤ)
    (a : Fin n → Actor N) : Prop where
  isState : IsState u
  /-- `n (u) ∈ {1, …, N - 1}`. -/
  one_le : 1 ≤ n
  le_pred : n ≤ N - 1
  /-- `r ∈ [0, 1)`, scaled. -/
  rho_nonneg : 0 ≤ ρ
  rho_lt : ρ < (M : ℤ) - 1
  /-- The `a j` are `n` different actors. -/
  injective : Function.Injective a
  /-- `u (aⱼ, o) ≥ j + r` for `j = 1, …, n`. -/
  column : ∀ j : Fin n, (((j : ℕ) : ℤ) + 1) * ((M : ℤ) - 1) + ρ ≤ u (a j) o
  /-- `u (b, p) ≤ n + r - 1/(M-1)` for every actor `b` and every `p ≠ o`. -/
  other : ∀ b, ∀ p ≠ o, u b p ≤ (n : ℤ) * ((M : ℤ) - 1) + ρ - 1

/-- Definition 5: the set `S^o` of matrices favouring the opinion `o`. -/
def IsFavouring (o : Opinion M) (u : Pressure N M) : Prop :=
  ∃ (n : ℕ) (ρ : ℤ) (a : Fin n → Actor N), IsFavouringWith o u n ρ a

section FirstRepeat

variable (T : Trajectory N M)

/-- Some actor expresses twice: the actors form a finite set. -/
theorem exists_repeat : ∃ k, ∃ j < k, T.actor j = T.actor k := by
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    exact (this ▸ T.actor 0).elim0
  have hcard : Fintype.card (Actor N) < Fintype.card (Fin (N + 1)) := by simp
  obtain ⟨x, y, hxy, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (N + 1) => T.actor (i : ℕ)) hcard
  rcases lt_trichotomy (x : ℕ) (y : ℕ) with h | h | h
  · exact ⟨(y : ℕ), (x : ℕ), h, hf⟩
  · exact absurd (Fin.val_injective h) hxy
  · exact ⟨(x : ℕ), (y : ℕ), h, hf.symm⟩

/-- The paper's `τ (u) = inf {n ≥ 1 : Aₙ ∈ {A₁, …, A_{n-1}}}`, in this file's index
convention: `firstRepeat T` is the first `k` at which `T.actor k` repeats an earlier actor,
so it is the paper's `τ (u) - 1`. -/
def firstRepeat : ℕ :=
  Nat.find (exists_repeat T)

theorem firstRepeat_spec : ∃ j < firstRepeat T, T.actor j = T.actor (firstRepeat T) :=
  Nat.find_spec (exists_repeat T)

theorem firstRepeat_le_of_repeat {k : ℕ} (h : ∃ j < k, T.actor j = T.actor k) :
    firstRepeat T ≤ k :=
  Nat.find_le h

/-- Before the first repeat all expressing actors are distinct. -/
theorem actor_injOn_lt_firstRepeat {j k : ℕ} (hjk : j < k) (hk : k < firstRepeat T) :
    T.actor j ≠ T.actor k := by
  intro hEq
  have := firstRepeat_le_of_repeat T ⟨j, hjk, hEq⟩
  omega

/-- `τ (u) ≤ N + 1`: the bound recorded after Definition 5. -/
theorem firstRepeat_le : firstRepeat T ≤ N := by
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    exact (this ▸ T.actor 0).elim0
  have hcard : Fintype.card (Actor N) < Fintype.card (Fin (N + 1)) := by simp
  obtain ⟨x, y, hxy, hf⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (N + 1) => T.actor (i : ℕ)) hcard
  have hx := x.isLt
  have hy := y.isLt
  rcases lt_trichotomy (x : ℕ) (y : ℕ) with h | h | h
  · exact le_trans (firstRepeat_le_of_repeat T ⟨(x : ℕ), h, hf⟩) (by omega)
  · exact absurd (Fin.val_injective h) hxy
  · exact le_trans (firstRepeat_le_of_repeat T ⟨(y : ℕ), h, hf.symm⟩) (by omega)

end FirstRepeat

section Favouring

variable {o : Opinion M} {u : Pressure N M} {n : ℕ} {ρ : ℤ} {a : Fin n → Actor N}

/-- In a state of `S^o` every maximising entry lies in column `o`: the witness `a_{n}`
carries at least `n + r` there, which strictly exceeds the bound `n + r - 1/(M-1)` imposed
on every other column.

Consequently a greedy expression from a state of `S^o` expresses `o` — the step the proof
of Lemma 20 opens with.

**Supplies a step the paper asserts**: the proof of Lemma 20 opens "then
`Ũ_0 (A₁, O₁) = max u (a, o)` and `O₁ = o`", asserting `O₁ = o`. -/
theorem opinion_eq_of_isMax_of_favouring (h : IsFavouringWith o u n ρ a) {b : Actor N}
    {p : Opinion M} (hmax : ∀ c q, u c q ≤ u b p) : p = o := by
  by_contra hp
  have hn : n - 1 < n := by have := h.one_le; omega
  have hcol := h.column ⟨n - 1, hn⟩
  have hcast : (((n - 1 : ℕ) : ℤ) + 1) = (n : ℤ) := by
    have := h.one_le
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at hcol
  have hother := h.other b p hp
  have hle := hmax (a ⟨n - 1, hn⟩) o
  omega

/-- A state of `S` whose columns other than `o` are non-positive, and which is not the null
matrix, is a consensus state for `o`: the vanishing row sums turn the sign condition on the
other columns into non-negativity on column `o`.

This is the step the proof of Lemma 20 closes with, once `k` is large enough that the bound
`n + r - (k+1)/(M-1)` on the other columns has become negative.

**Supplies a step the paper asserts**: the proof of Lemma 20 ends "by taking
`k = (M-1)(n(u)+1)-1` we conclude the proof", the passage to `C^o` being left to the reader. -/
theorem isConsensus_of_nonpos (hu : IsState u) (hne : u ≠ 0)
    (h : ∀ b, ∀ p ≠ o, u b p ≤ 0) : IsConsensus o u := by
  refine ⟨hu, hne, fun b => ?_, h⟩
  have hsplit : u b o + ∑ p ∈ Finset.univ.erase o, u b p = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    exact hu.trust_eq_zero b
  have hnonpos : ∑ p ∈ Finset.univ.erase o, u b p ≤ 0 :=
    Finset.sum_nonpos fun p hp => h b p (Finset.ne_of_mem_erase hp)
  linarith

end Favouring

end SocialNetwork
