/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Social pressure matrices and the expression operator

Formalisation of Section 2 of *Metastability and phase transition in a social network model
with multiple opinions* (Penafiel–Laxa, arXiv:2607.19651).

## Scaled coordinates

The paper works with a matrix `u ∈ M_{N,M}(ℝ)` whose entries live in `ℤ + (1/(M-1))ℤ`, which
for `M ≥ 2` is exactly `(1/(M-1))ℤ`. Rather than carry a subgroup of `ℝ` around, we work
throughout with the **scaled** matrix

  `v (a, o) := (M - 1) * u (a, o) ∈ ℤ`.

Under this rescaling the operator `π^{a,o}` of equation (1) becomes an operator on integer
matrices: expressing adds `M - 1` to the expressed column and subtracts `1` from the others.
Every statement about `u` translates to a statement about `v` by a positive rescaling, so no
generality is lost, and all the arithmetic of the paper (in particular the gap estimate
`v (b, o) - y (v) ≤ -1/(M-1)` used in Proposition 8) becomes plain integer arithmetic.

## Main definitions

* `SocialNetwork.Pressure N M` — the scaled social pressure matrices.
* `SocialNetwork.express a o u` — the operator `π^{a,o}` of equation (1), scaled.
* `SocialNetwork.trust`, `SocialNetwork.publicOpinion` — the macroscopic observables of
  Section 4.
* `SocialNetwork.IsState` — membership in the state space `S` of equation (2).

## Main results

* `SocialNetwork.trust_express` — expressing preserves the trust of every actor and zeroes
  the trust of the expressing one; this is the conservation law behind `S`.
* `SocialNetwork.IsState.express` — `S` is stable under every `π^{a,o}`, the claim made just
  after equation (2).
-/

namespace SocialNetwork

open Finset

variable {N M : ℕ}

/-- The actors of the network, `A = {1, ..., N}`. -/
abbrev Actor (N : ℕ) := Fin N

/-- The opinions available in the network, `O = {1, ..., M}`. -/
abbrev Opinion (M : ℕ) := Fin M

/-- A social pressure matrix in scaled coordinates: `u a o` stands for `(M - 1)` times the
social pressure exerted on actor `a` for opinion `o`. -/
abbrev Pressure (N M : ℕ) := Actor N → Opinion M → ℤ

/-- The expression operator `π^{a,o}` of equation (1), in scaled coordinates.

When actor `a` expresses opinion `o`, its own row is reset to zero, every other actor gains
`M - 1` (i.e. `1` before scaling) on the expressed opinion `o`, and loses `1` (i.e.
`1/(M-1)` before scaling) on each of the other opinions. -/
def express (a : Actor N) (o : Opinion M) (u : Pressure N M) : Pressure N M := fun b p =>
  if b = a then 0
  else if p = o then u b p + ((M : ℤ) - 1)
  else u b p - 1

@[simp]
theorem express_self (a : Actor N) (o p : Opinion M) (u : Pressure N M) :
    express a o u a p = 0 := by
  simp [express]

theorem express_of_ne_of_eq {a b : Actor N} (hb : b ≠ a) (o : Opinion M) (u : Pressure N M) :
    express a o u b o = u b o + ((M : ℤ) - 1) := by
  simp [express, hb]

theorem express_of_ne_of_ne {a b : Actor N} {o p : Opinion M} (hb : b ≠ a) (hp : p ≠ o)
    (u : Pressure N M) : express a o u b p = u b p - 1 := by
  simp [express, hb, hp]

-- `simp` closes the `p = o` branch outright and leaves `u b p - 1 = u b p + -1` in the
-- other, so the `<;>` really is doing work here.
set_option linter.unnecessarySeqFocus false in
/-- A uniform rewriting of `express` on the rows that are not reset. Both branches of
equation (1) are packaged into a single expression, which makes the summation arguments
below routine. -/
theorem express_of_ne {a b : Actor N} (hb : b ≠ a) (o p : Opinion M) (u : Pressure N M) :
    express a o u b p = u b p + ((if p = o then (M : ℤ) else 0) - 1) := by
  by_cases hp : p = o <;> simp [express, hb, hp] <;> ring

/-- The *trust* of actor `a`, i.e. the total pressure this actor allocates to all opinions
(Section 4). -/
def trust (u : Pressure N M) (a : Actor N) : ℤ := ∑ o, u a o

/-- The *public opinion* toward `o`, i.e. the total pressure exerted by the population
(Section 4). -/
def publicOpinion (u : Pressure N M) (o : Opinion M) : ℤ := ∑ a, u a o

/-- The increments applied by `π^{a,o}` to a row that is not reset cancel out: one opinion
gains `M - 1` and the remaining `M - 1` opinions lose `1` each. -/
theorem sum_express_increment (o : Opinion M) :
    ∑ p : Opinion M, ((if p = o then (M : ℤ) else 0) - 1) = 0 := by
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- Expressing does not change the trust of the actors who merely listen. -/
theorem trust_express_of_ne {a b : Actor N} (hb : b ≠ a) (o : Opinion M) (u : Pressure N M) :
    trust (express a o u) b = trust u b := by
  have h : ∑ p : Opinion M, (u b p + ((if p = o then (M : ℤ) else 0) - 1))
      = trust u b + ∑ p : Opinion M, ((if p = o then (M : ℤ) else 0) - 1) :=
    Finset.sum_add_distrib
  calc trust (express a o u) b
      = ∑ p : Opinion M, (u b p + ((if p = o then (M : ℤ) else 0) - 1)) :=
        Finset.sum_congr rfl fun p _ => express_of_ne hb o p u
    _ = trust u b + ∑ p : Opinion M, ((if p = o then (M : ℤ) else 0) - 1) := h
    _ = trust u b := by rw [sum_express_increment, add_zero]

/-- Expressing resets the trust of the expressing actor. -/
@[simp]
theorem trust_express_self (a : Actor N) (o : Opinion M) (u : Pressure N M) :
    trust (express a o u) a = 0 := by
  simp [trust]

/-- The conservation law behind the state space `S`: `π^{a,o}` preserves the trust of every
actor except the expressing one, whose trust is reset to zero. -/
theorem trust_express (a b : Actor N) (o : Opinion M) (u : Pressure N M) :
    trust (express a o u) b = if b = a then 0 else trust u b := by
  by_cases hb : b = a
  · subst hb; simp
  · rw [if_neg hb, trust_express_of_ne hb]

/-- Membership in the state space `S` of equation (2).

The condition `min_{a} ‖u (a, ·)‖_∞ = 0` says exactly that some actor carries no social
pressure at all, and the condition `∑_o u (a, o) = 0` says that every actor has vanishing
trust.  The lattice condition `u (a, o) ∈ ℤ + (1/(M-1))ℤ` is automatic in scaled
coordinates, where entries are integers by construction. -/
structure IsState (u : Pressure N M) : Prop where
  /-- Every actor's support for some opinions is exactly offset by reduced support for the
  others (Remark 3). -/
  trust_eq_zero : ∀ a, trust u a = 0
  /-- Some actor carries no social pressure, i.e. `min_a ‖u (a, ·)‖_∞ = 0`. -/
  exists_zero_row : ∃ a, ∀ o, u a o = 0

/-- The state space `S` is stable under every expression operator: this is the claim, made
just after equation (2), that from any starting position the process remains in `S` forever
once every actor has expressed an opinion at least once. -/
theorem IsState.express {u : Pressure N M} (hu : IsState u) (a : Actor N) (o : Opinion M) :
    IsState (SocialNetwork.express a o u) := by
  refine ⟨fun b => ?_, ⟨a, fun p => express_self a o p u⟩⟩
  rw [trust_express]
  by_cases hb : b = a
  · rw [if_pos hb]
  · rw [if_neg hb, hu.trust_eq_zero]

/-- Whatever the starting matrix, one expression already forces a zero row, hence the second
requirement of `S`. -/
theorem exists_zero_row_express (a : Actor N) (o : Opinion M) (u : Pressure N M) :
    ∃ b, ∀ p, express a o u b p = 0 :=
  ⟨a, fun p => express_self a o p u⟩

end SocialNetwork
