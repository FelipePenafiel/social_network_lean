/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

/-!
# Trajectories

Propositions 5, 6 and 7 of arXiv:2607.19651 are stated as statements about the random
process, but their content is entirely deterministic: they hold for *every* realisation of
the sequence `(Aₙ, Oₙ)ₙ` of expressing actors and opinions (Proposition 6 and 7 on the
event `⋂ ξⱼ`, which is itself a condition on the realisation). Isolating that deterministic
layer lets us prove them without any of the missing Markov-jump-process infrastructure.

A `Trajectory` is such a realisation, and `Trajectory.state u n` is the matrix
`U_{T_n}^{β,u}` of the paper. Note the index convention: `T.actor 0` and `T.opinion 0` are
the paper's `A₁` and `O₁`, so `Trajectory.state u n` is the state after `n` expressions.

## Main definitions

* `SocialNetwork.Trajectory` — a realisation of the expressing actors and opinions.
* `SocialNetwork.Trajectory.state` — the matrix after `n` expressions.
* `SocialNetwork.rowSup` — `‖u (a, ·)‖_∞` in scaled coordinates, valued in `ℕ`.

## Main results

* `SocialNetwork.rowSup_state_le` — an actor whose row is null at time `m` has
  `‖U_{m+k} (a, ·)‖_∞ ≤ k` (unscaled), the growth bound driving the proof of Proposition 5.
* `SocialNetwork.exists_rowSup_actor_lt` — **Proposition 5**: among the first `N`
  expressions, at least one comes from an actor carrying pressure below `N`.
* `SocialNetwork.IsGreedyAt` — the paper's event `ξₙ^u`, as a predicate on trajectories.
* `SocialNetwork.entry_mem_of_greedy` — **Proposition 6**: on `⋂_{j ≤ N} ξⱼ^u` the whole
  matrix lies in `(-MN, N)` entrywise after `N` expressions.
-/

namespace SocialNetwork

open Finset

variable {N M : ℕ}

/-- A realisation of the sequence `(Aₙ, Oₙ)ₙ` of expressing actors and opinions.

The paper indexes from `1`; here `actor 0` is the paper's `A₁`. -/
structure Trajectory (N M : ℕ) where
  /-- The actor expressing at the `(n+1)`-st jump. -/
  actor : ℕ → Actor N
  /-- The opinion expressed at the `(n+1)`-st jump. -/
  opinion : ℕ → Opinion M

namespace Trajectory

/-- The social pressure matrix after `n` expressions, starting from `u`. This is the
paper's `U_{T_n}^{β,u}`. -/
def state (T : Trajectory N M) (u : Pressure N M) : ℕ → Pressure N M
  | 0 => u
  | n + 1 => express (T.actor n) (T.opinion n) (T.state u n)

variable (T : Trajectory N M)

@[simp]
theorem state_zero (u : Pressure N M) : T.state u 0 = u := by rw [state]

theorem state_succ (u : Pressure N M) (n : ℕ) :
    T.state u (n + 1) = express (T.actor n) (T.opinion n) (T.state u n) := by rw [state]

/-- The state space `S` is preserved along any trajectory. -/
theorem isState_state {u : Pressure N M} (hu : IsState u) (n : ℕ) : IsState (T.state u n) := by
  induction n with
  | zero => rw [state_zero]; exact hu
  | succ n ih => rw [state_succ]; exact ih.express _ _

/-- The expressing actor's row is null immediately after it expresses. -/
@[simp]
theorem state_succ_actor (u : Pressure N M) (n : ℕ) (p : Opinion M) :
    T.state u (n + 1) (T.actor n) p = 0 := by
  rw [state_succ]; exact express_self _ _ _ _

end Trajectory

/-- `‖u (a, ·)‖_∞` in scaled coordinates, as a natural number.

In the paper's unscaled coordinates this is `(M - 1) * ‖u (a, ·)‖_∞`, so the paper's
condition `‖u (a, ·)‖_∞ < N` reads `rowSup u a < N * (M - 1)` here. -/
def rowSup (u : Pressure N M) (a : Actor N) : ℕ :=
  Finset.univ.sup fun o => (u a o).natAbs

theorem le_rowSup (u : Pressure N M) (a : Actor N) (o : Opinion M) :
    (u a o).natAbs ≤ rowSup u a :=
  Finset.le_sup (f := fun o => (u a o).natAbs) (Finset.mem_univ o)

theorem rowSup_le_iff {u : Pressure N M} {a : Actor N} {k : ℕ} :
    rowSup u a ≤ k ↔ ∀ o, (u a o).natAbs ≤ k := by
  simp [rowSup, Finset.sup_le_iff]

@[simp]
theorem rowSup_eq_zero_iff {u : Pressure N M} {a : Actor N} :
    rowSup u a = 0 ↔ ∀ o, u a o = 0 := by
  simp [rowSup]

/-- A single expression moves any given entry by at most `M - 1` in scaled coordinates,
i.e. by at most `1` in the paper's coordinates. -/
theorem natAbs_express_le (hM : 2 ≤ M) (b : Actor N) (o p : Opinion M) (u : Pressure N M)
    (a : Actor N) : (express b o u a p).natAbs ≤ (u a p).natAbs + (M - 1) := by
  have h1 : 1 ≤ M := le_trans one_le_two hM
  have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
    push_cast [Nat.cast_sub h1]; ring
  have hM' : 1 ≤ (M - 1 : ℕ) := by omega
  unfold express
  split_ifs <;> omega

/-- The row of any actor grows by at most `M - 1` (scaled) at each expression. -/
theorem rowSup_express_le (hM : 2 ≤ M) (b : Actor N) (o : Opinion M) (u : Pressure N M)
    (a : Actor N) : rowSup (express b o u) a ≤ rowSup u a + (M - 1) := by
  rw [rowSup_le_iff]
  exact fun p => le_trans (natAbs_express_le hM b o p u a)
    (Nat.add_le_add_right (le_rowSup u a p) _)

/-- Growth bound: an actor whose row is null at time `m` has, `k` expressions later, a row
bounded by `k` in the paper's coordinates.

This is the estimate `‖U_{T_m} (a₀, ·)‖_∞ ≤ m` used in the proof of Proposition 5. -/
theorem rowSup_state_le (hM : 2 ≤ M) (T : Trajectory N M) (u : Pressure N M) (a : Actor N)
    (m : ℕ) (hm : rowSup (T.state u m) a = 0) (k : ℕ) :
    rowSup (T.state u (m + k)) a ≤ k * (M - 1) := by
  induction k with
  | zero => simpa using hm.le
  | succ k ih =>
      have hstep : rowSup (T.state u (m + k + 1)) a ≤ rowSup (T.state u (m + k)) a + (M - 1) := by
        rw [T.state_succ]
        exact rowSup_express_le hM _ _ _ _
      calc rowSup (T.state u (m + (k + 1))) a
          = rowSup (T.state u (m + k + 1)) a := by rw [← Nat.add_assoc]
        _ ≤ rowSup (T.state u (m + k)) a + (M - 1) := hstep
        _ ≤ k * (M - 1) + (M - 1) := Nat.add_le_add_right ih _
        _ = (k + 1) * (M - 1) := by ring

/-- Specialisation of `rowSup_state_le` to an actor that has just expressed. -/
theorem rowSup_state_le_of_actor (hM : 2 ≤ M) (T : Trajectory N M) (u : Pressure N M)
    (n k : ℕ) : rowSup (T.state u (n + 1 + k)) (T.actor n) ≤ k * (M - 1) :=
  rowSup_state_le hM T u _ (n + 1) (by simp) k

/-!
## Proposition 5

Among any `N` consecutive expressions, at least one comes from an actor whose social
pressure on the expressed opinion is below `N`.

Recall the index convention: `T.actor k` is the paper's `A_{k+1}` and `T.state u k` is
`U_{T_k}`, so the paper's `inf {n ≥ 1 : ‖U_{T_{n-1}} (A_n, ·)‖_∞ < N} ≤ N` is the statement
that some `k < N` satisfies `‖U_{T_k} (A_{k+1}, ·)‖_∞ < N`. In scaled coordinates
`‖·‖_∞ < N` reads `rowSup … < N * (M - 1)`; the two are equivalent because the rescaling is
by the positive factor `M - 1`.
-/

section Proposition5

variable (T : Trajectory N M) {u : Pressure N M}

/-- No expression among the first `N` can come from an actor whose row was null at the
start: such an actor's row is still too small to have been the one expressing. -/
theorem actor_ne_of_rowSup_state_zero (hM : 2 ≤ M) {a₀ : Actor N} (hzero : rowSup u a₀ = 0)
    (hbig : ∀ k, k < N → N * (M - 1) ≤ rowSup (T.state u k) (T.actor k))
    {k : ℕ} (hk : k < N) : T.actor k ≠ a₀ := by
  have hMpos : 0 < M - 1 := by omega
  intro hEq
  have hle : rowSup (T.state u k) a₀ ≤ k * (M - 1) := by
    have h := rowSup_state_le hM T u a₀ 0 (by rw [T.state_zero]; exact hzero) k
    rwa [Nat.zero_add] at h
  have hlt : k * (M - 1) < N * (M - 1) := (Nat.mul_lt_mul_right hMpos).mpr hk
  have hge := hbig k hk
  rw [hEq] at hge
  omega

/-- Two of the first `N` expressions cannot come from the same actor: after expressing, an
actor's row is null and cannot grow back to `N` in fewer than `N` further expressions. -/
theorem actor_ne_actor_of_lt (hM : 2 ≤ M)
    (hbig : ∀ k, k < N → N * (M - 1) ≤ rowSup (T.state u k) (T.actor k))
    {j k : ℕ} (hjk : j < k) (hk : k < N) : T.actor j ≠ T.actor k := by
  have hMpos : 0 < M - 1 := by omega
  intro hEq
  have hzeroj : rowSup (T.state u (j + 1)) (T.actor j) = 0 :=
    rowSup_eq_zero_iff.2 fun p => T.state_succ_actor u j p
  have hle : rowSup (T.state u k) (T.actor j) ≤ (k - j - 1) * (M - 1) := by
    have h := rowSup_state_le hM T u (T.actor j) (j + 1) hzeroj (k - j - 1)
    have hidx : j + 1 + (k - j - 1) = k := by omega
    rwa [hidx] at h
  have hlt : (k - j - 1) * (M - 1) < N * (M - 1) :=
    (Nat.mul_lt_mul_right hMpos).mpr (by omega)
  have hge := hbig k hk
  rw [← hEq] at hge
  omega

/-- **Proposition 5.** For any starting matrix `u ∈ S`, among the first `N` expressions at
least one is made by an actor whose social pressure on the expressed opinion is smaller
than `N`.

The proof is the paper's: if every one of the first `N` expressions came from an actor
carrying pressure at least `N`, then none of them can be the actor `a₀` whose row is null
in `u`, nor can any two of them coincide — which exhibits `N + 1` distinct actors in a
network of `N`. -/
theorem exists_rowSup_actor_lt (hM : 2 ≤ M) (hu : IsState u) :
    ∃ k < N, rowSup (T.state u k) (T.actor k) < N * (M - 1) := by
  by_contra hcon
  have hbig : ∀ k, k < N → N * (M - 1) ≤ rowSup (T.state u k) (T.actor k) := by
    intro k hk
    by_contra h
    exact hcon ⟨k, hk, not_le.mp h⟩
  obtain ⟨a₀, ha₀⟩ := hu.exists_zero_row
  have hzero : rowSup u a₀ = 0 := rowSup_eq_zero_iff.2 ha₀
  have hne : ∀ k, k < N → T.actor k ≠ a₀ :=
    fun _ hk => actor_ne_of_rowSup_state_zero T hM hzero hbig hk
  have hpair : ∀ j k, j < k → k < N → T.actor j ≠ T.actor k :=
    fun _ _ hjk hk => actor_ne_actor_of_lt T hM hbig hjk hk
  -- `a₀` together with the first `N` expressing actors are `N + 1` distinct actors.
  have hinj : Function.Injective
      fun i : Fin (N + 1) => if (i : ℕ) < N then T.actor (i : ℕ) else a₀ := by
    intro i j hij
    have hi' := i.isLt
    have hj' := j.isLt
    simp only at hij
    by_cases hi : (i : ℕ) < N <;> by_cases hj : (j : ℕ) < N
    · rw [if_pos hi, if_pos hj] at hij
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · exact absurd hij (hpair _ _ h hj)
      · exact Fin.val_injective h
      · exact absurd hij.symm (hpair _ _ h hi)
    · rw [if_pos hi, if_neg hj] at hij
      exact absurd hij (hne _ hi)
    · rw [if_neg hi, if_pos hj] at hij
      exact absurd hij.symm (hne _ hj)
    · exact Fin.val_injective (by omega)
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hcard
  omega

end Proposition5

/-!
## The greedy event and Proposition 6

The paper's event `ξₙ^u` says that the `n`-th expression is made by one of the pairs
`(a, o)` maximising the social pressure at that moment. It is a condition on the
realisation, not on its probability, so it is a predicate on trajectories here.
-/

/-- The paper's event `ξₙ^u`: the expression at step `k` is made by an actor/opinion pair
maximising the social pressure, i.e. `(Aₙ, Oₙ) ∈ argmax U_{T_{n-1}}`.

With the index convention of this file, `IsGreedyAt T u k` is the paper's `ξ_{k+1}^u`. -/
def IsGreedyAt (T : Trajectory N M) (u : Pressure N M) (k : ℕ) : Prop :=
  ∀ a o, T.state u k a o ≤ T.state u k (T.actor k) (T.opinion k)

section Proposition6

variable (T : Trajectory N M) {u : Pressure N M}

theorem le_rowSup_cast (v : Pressure N M) (a : Actor N) (p : Opinion M) :
    v a p ≤ (rowSup v a : ℤ) := by
  have h := le_rowSup v a p
  omega

/-- An entry of an actor whose row was null `k` steps ago is at most `k` (unscaled). -/
theorem entry_le_of_state (hM : 2 ≤ M) (a : Actor N) (m : ℕ)
    (hm : rowSup (T.state u m) a = 0) (k : ℕ) (p : Opinion M) :
    T.state u (m + k) a p ≤ (k : ℤ) * ((M : ℤ) - 1) := by
  have h1 : 1 ≤ M := by omega
  have hcast : ((k * (M - 1) : ℕ) : ℤ) = (k : ℤ) * ((M : ℤ) - 1) := by
    push_cast [Nat.cast_sub h1]; ring
  calc T.state u (m + k) a p ≤ (rowSup (T.state u (m + k)) a : ℤ) := le_rowSup_cast _ a p
    _ ≤ ((k * (M - 1) : ℕ) : ℤ) := by exact_mod_cast rowSup_state_le hM T u a m hm k
    _ = (k : ℤ) * ((M : ℤ) - 1) := hcast

/-- One expression raises no entry above `c + (M - 1)`, provided every entry was at most
`c` and `c` is non-negative. Non-negativity is what covers the reset row, whose entries
jump to `0`. -/
theorem le_express_of_le (hM : 2 ≤ M) {v : Pressure N M} {c : ℤ} (hc : 0 ≤ c)
    (h : ∀ a p, v a p ≤ c) (b : Actor N) (o : Opinion M) (a : Actor N) (p : Opinion M) :
    express b o v a p ≤ c + ((M : ℤ) - 1) := by
  have hM' : (1 : ℤ) ≤ (M : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  have hap := h a p
  unfold express
  split_ifs <;> linarith

/-- Iterated form of `le_express_of_le`. -/
theorem le_state_of_le (hM : 2 ≤ M) {m : ℕ} {c : ℤ} (hc : 0 ≤ c)
    (h : ∀ a p, T.state u m a p ≤ c) (k : ℕ) (a : Actor N) (p : Opinion M) :
    T.state u (m + k) a p ≤ c + (k : ℤ) * ((M : ℤ) - 1) := by
  induction k generalizing a p with
  | zero => simpa using h a p
  | succ k ih =>
      have hMnn : (0 : ℤ) ≤ (M : ℤ) - 1 := by
        have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
        omega
      have hstep := le_express_of_le hM (v := T.state u (m + k))
        (c := c + (k : ℤ) * ((M : ℤ) - 1)) (by positivity) (fun a p => ih a p)
        (T.actor (m + k)) (T.opinion (m + k)) a p
      rw [show m + (k + 1) = m + k + 1 from rfl, T.state_succ]
      calc express (T.actor (m + k)) (T.opinion (m + k)) (T.state u (m + k)) a p
          ≤ c + (k : ℤ) * ((M : ℤ) - 1) + ((M : ℤ) - 1) := hstep
        _ = c + ((k : ℤ) + 1) * ((M : ℤ) - 1) := by ring
        _ = c + ((k + 1 : ℕ) : ℤ) * ((M : ℤ) - 1) := by push_cast; ring

/-- The sharp upper bound behind Proposition 6: after `N` greedy expressions every entry is
at most `N - 1` in the paper's coordinates. -/
theorem entry_le_of_greedy (hM : 2 ≤ M) (hgreedy : ∀ k, k < N → IsGreedyAt T u k)
    (a : Actor N) (p : Opinion M) :
    T.state u N a p ≤ ((N : ℤ) - 1) * ((M : ℤ) - 1) := by
  have hMnn : (0 : ℤ) ≤ (M : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  by_cases hdist : ∀ j k, j < k → k < N → T.actor j ≠ T.actor k
  · -- Every actor expresses exactly once, so every row was reset within the first `N` steps.
    have hfinj : Function.Injective fun i : Fin N => T.actor (i : ℕ) := by
      intro i j hij
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · exact absurd hij (hdist _ _ h j.isLt)
      · exact Fin.val_injective h
      · exact absurd hij.symm (hdist _ _ h i.isLt)
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hfinj a
    have hi' : T.actor (i : ℕ) = a := hi
    have hiN := i.isLt
    have hz : rowSup (T.state u ((i : ℕ) + 1)) (T.actor (i : ℕ)) = 0 :=
      rowSup_eq_zero_iff.2 fun q => T.state_succ_actor u _ q
    have hidx : (i : ℕ) + 1 + (N - (i : ℕ) - 1) = N := by omega
    have hle := entry_le_of_state T hM (T.actor (i : ℕ)) ((i : ℕ) + 1) hz
      (N - (i : ℕ) - 1) p
    rw [hidx, hi'] at hle
    refine le_trans hle (mul_le_mul_of_nonneg_right ?_ hMnn)
    have : (N - (i : ℕ) - 1 : ℕ) ≤ N - 1 := by omega
    have hcast : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
      have : 1 ≤ N := by omega
      push_cast [Nat.cast_sub this]; ring
    calc ((N - (i : ℕ) - 1 : ℕ) : ℤ) ≤ ((N - 1 : ℕ) : ℤ) := by exact_mod_cast this
      _ = (N : ℤ) - 1 := hcast
  · -- Some actor expresses twice; greediness at that step caps the whole matrix.
    have hrep : ∃ j k, j < k ∧ k < N ∧ T.actor j = T.actor k := by
      by_contra hno
      exact hdist fun j k hjk hk heq => hno ⟨j, k, hjk, hk, heq⟩
    obtain ⟨j, k, hjk, hk, heq⟩ := hrep
    have hz : rowSup (T.state u (j + 1)) (T.actor j) = 0 :=
      rowSup_eq_zero_iff.2 fun q => T.state_succ_actor u j q
    have hidx : j + 1 + (k - j - 1) = k := by omega
    -- At step `k` the expressing actor's row is small, and greediness makes it the maximum.
    have hmax : ∀ b q, T.state u k b q ≤ ((k - j - 1 : ℕ) : ℤ) * ((M : ℤ) - 1) := by
      intro b q
      have hb := entry_le_of_state T hM (T.actor j) (j + 1) hz (k - j - 1) (T.opinion k)
      rw [hidx, heq] at hb
      exact le_trans (hgreedy k hk b q) hb
    have hnn : (0 : ℤ) ≤ ((k - j - 1 : ℕ) : ℤ) * ((M : ℤ) - 1) := by positivity
    have hprop := le_state_of_le T hM hnn hmax (N - k) a p
    rw [show k + (N - k) = N from by omega] at hprop
    refine le_trans hprop ?_
    have hnat : (k - j - 1) + (N - k) ≤ N - 1 := by omega
    have hcast : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
      have : 1 ≤ N := by omega
      push_cast [Nat.cast_sub this]; ring
    have hsum : ((k - j - 1 : ℕ) : ℤ) + ((N - k : ℕ) : ℤ) ≤ (N : ℤ) - 1 := by
      calc ((k - j - 1 : ℕ) : ℤ) + ((N - k : ℕ) : ℤ)
          = (((k - j - 1) + (N - k) : ℕ) : ℤ) := by push_cast; ring
        _ ≤ ((N - 1 : ℕ) : ℤ) := by exact_mod_cast hnat
        _ = (N : ℤ) - 1 := hcast
    nlinarith

/-- Every entry is bounded below by `-(M-1)` times any upper bound on the entries, because
each row of a state of `S` sums to zero. -/
theorem neg_le_of_forall_le (hM : 2 ≤ M) {v : Pressure N M} (hv : IsState v) {c : ℤ}
    (h : ∀ b q, v b q ≤ c) (a : Actor N) (o : Opinion M) :
    -(((M : ℤ) - 1) * c) ≤ v a o := by
  have h1 : 1 ≤ M := by omega
  have hsplit : v a o + ∑ p ∈ Finset.univ.erase o, v a p = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    exact hv.trust_eq_zero a
  have hcard : (Finset.univ.erase o).card = M - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ, Fintype.card_fin]
  have hbound : ∑ p ∈ Finset.univ.erase o, v a p ≤ ((M : ℤ) - 1) * c := by
    have hsum := Finset.sum_le_card_nsmul (Finset.univ.erase o) (fun p => v a p) c
      (fun p _ => h a p)
    rw [hcard, nsmul_eq_mul] at hsum
    have hcast : (((M - 1 : ℕ)) : ℤ) = (M : ℤ) - 1 := by
      push_cast [Nat.cast_sub h1]; ring
    rwa [hcast] at hsum
  linarith

/-- **Proposition 6.** On the event `⋂_{j ≤ N} ξⱼ^u`, the whole matrix of social pressures
after `N` expressions is confined to `(-MN, N)` entrywise, in the paper's coordinates. -/
theorem entry_mem_of_greedy (hM : 2 ≤ M) (hu : IsState u)
    (hgreedy : ∀ k, k < N → IsGreedyAt T u k) (a : Actor N) (p : Opinion M) :
    -((M : ℤ) * (N : ℤ) * ((M : ℤ) - 1)) < T.state u N a p ∧
      T.state u N a p < (N : ℤ) * ((M : ℤ) - 1) := by
  have hM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hupper := entry_le_of_greedy T hM hgreedy
  have hlower := neg_le_of_forall_le (v := T.state u N) hM (T.isState_state hu N) hupper a p
  have hN : 1 ≤ N := by
    obtain ⟨a₀, -⟩ := hu.exists_zero_row
    have := a₀.isLt
    omega
  have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hx : (1 : ℤ) ≤ (M : ℤ) - 1 := by linarith
  have hy : (0 : ℤ) ≤ (N : ℤ) - 1 := by linarith
  constructor
  · -- `(M-1)(N-1)(M-1) < M N (M-1)`, so the lower bound from the row sums is enough.
    have hkey : ((M : ℤ) - 1) * (((N : ℤ) - 1) * ((M : ℤ) - 1))
        < (M : ℤ) * (N : ℤ) * ((M : ℤ) - 1) := by nlinarith [mul_nonneg hy (by linarith : (0:ℤ) ≤ (M:ℤ) - 1)]
    linarith
  · have hkey : ((N : ℤ) - 1) * ((M : ℤ) - 1) < (N : ℤ) * ((M : ℤ) - 1) := by nlinarith
    linarith [hupper a p]

end Proposition6

end SocialNetwork
