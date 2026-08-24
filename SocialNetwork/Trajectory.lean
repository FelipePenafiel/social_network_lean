/-
Copyright (c) 2026 Felipe Peñafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Defs
import Mathlib.Data.Finset.Lattice.Fold

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

end SocialNetwork
