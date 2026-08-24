/-
Copyright (c) 2026 Felipe Peñafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The model with communication bias

Formalisation of Section 3 of arXiv:2607.19651: the operator `π_α^{a,o}` of equation (5)
and the state space `S^α` of equation (6).

## The memory representation

Equation (6) describes `S^α` by saying that the row of an actor `a` which has heard `nₐ`
expressions since it last expressed, `cₚ` of which concerned opinion `p`, is

```
u (a, p) = cₚ (1 + γ) - γ nₐ,        γ := 1/(M-1) - α.
```

Rather than take the matrix as primitive and impose this as a constraint, we take the
**memory profile** `(cₚ)ₚ` as the primitive datum and *define* the pressure by the formula
above, with `nₐ := ∑ₚ cₚ`. This has three consequences:

* the constraint `∑ₚ cₚ = nₐ` of equation (6) holds by definition;
* membership in `S^α` is not a proposition to be propagated but a property of the
  representation, so Remark 1 ("`S^α` is stable under every `π_α^{a,o}`") becomes the
  computation `Memory.pressure_hear` below rather than an invariant to maintain;
* the model is visibly a system of interacting point processes with *memory of variable
  length*, which is how the paper positions it.

Nothing here needs division, so the whole section is stated over an arbitrary commutative
ring `K` with a parameter `γ : K`. The bias `α` enters only through the ring identity
`(M - 1) γ = 1 - (M - 1) α`, which is `γ = 1/(M-1) - α` cleared of denominators.

## Main definitions

* `SocialNetwork.Bias.Memory` — the variable-length memory of a single actor.
* `SocialNetwork.Bias.Memory.pressure` — the row of eq. (6).
* `SocialNetwork.Bias.Memory.hear`, `SocialNetwork.Bias.Memory.reset` — the two ways a
  memory changes.

## Main results

* `SocialNetwork.Bias.Memory.pressure_hear` — the memory representation reproduces exactly
  the operator `π_α^{a,o}` of eq. (5); this is the stability half of Remark 1.
* `SocialNetwork.Bias.Memory.sum_pressure_eq` — `∑ₚ u (a, p) = nₐ (M - 1) α`, the trust
  identity of Remark 1. In particular trust vanishes identically iff `α = 0`, recovering
  Remark 3.
-/

namespace SocialNetwork

namespace Bias

open Finset

variable {N M : ℕ} {K : Type*} [CommRing K]

/-- The variable-length memory of a single actor: how many of the expressions heard since
this actor last expressed concerned each opinion. This is `(cₚ)ₚ` in equation (6). -/
@[ext]
structure Memory (M : ℕ) where
  /-- `count p` is the number of expressions of opinion `p` heard since last expressing. -/
  count : Opinion M → ℕ

namespace Memory

/-- The total number `nₐ` of expressions heard since this actor last expressed. The
constraint `∑ₚ cₚ = nₐ` of equation (6) holds by definition. -/
def heard (m : Memory M) : ℕ := ∑ p, m.count p

/-- The memory of an actor that has just expressed: everything is reset to zero. -/
def reset (M : ℕ) : Memory M := ⟨fun _ => 0⟩

@[simp]
theorem count_reset (p : Opinion M) : (reset M).count p = 0 := rfl

@[simp]
theorem heard_reset : (reset M).heard = 0 := by simp [heard]

/-- The memory after hearing one expression of opinion `o`. -/
def hear (o : Opinion M) (m : Memory M) : Memory M :=
  ⟨fun p => m.count p + if p = o then 1 else 0⟩

@[simp]
theorem count_hear (o p : Opinion M) (m : Memory M) :
    (hear o m).count p = m.count p + if p = o then 1 else 0 := rfl

@[simp]
theorem heard_hear (o : Opinion M) (m : Memory M) : (hear o m).heard = m.heard + 1 := by
  simp [heard, Finset.sum_add_distrib]

/-- The social pressure of an actor with memory `m` for opinion `p`, as given by equation
(6): `u (a, p) = cₚ (1 + γ) - γ nₐ`. -/
def pressure (γ : K) (m : Memory M) (p : Opinion M) : K :=
  (m.count p : K) * (1 + γ) - γ * (m.heard : K)

@[simp]
theorem pressure_reset (γ : K) (p : Opinion M) : (reset M).pressure γ p = 0 := by
  simp [pressure]

/-- **The stability half of Remark 1.** Hearing an expression of `o` moves the row exactly
by the operator `π_α^{a,o}` of equation (5): the expressed opinion gains `1`, every other
opinion gains `-γ = -1/(M-1) + α`.

Since the expressing actor's own memory is `reset`, whose pressure is identically zero,
this shows that the memory representation is stable under every `π_α^{a,o}` — which is what
equation (6) asserts about `S^α`. -/
theorem pressure_hear (γ : K) (o : Opinion M) (m : Memory M) (p : Opinion M) :
    (hear o m).pressure γ p = m.pressure γ p + (if p = o then 1 else -γ) := by
  by_cases hp : p = o <;> simp [pressure, hp] <;> ring

/-- The trust `∑ₚ u (a, p)` of an actor with memory `m`, before introducing `α`. -/
theorem sum_pressure (γ : K) (m : Memory M) :
    ∑ p, m.pressure γ p = (m.heard : K) * (1 - ((M : K) - 1) * γ) := by
  have hcount : ∑ p, ((m.count p : K)) = (m.heard : K) := by
    rw [heard]; push_cast; ring
  simp only [pressure, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcount]
  ring

/-- **The trust identity of Remark 1**: `∑ₚ u (a, p) = nₐ (M - 1) α`.

The hypothesis is `γ = 1/(M-1) - α` cleared of denominators, so this holds in any
commutative ring. -/
theorem sum_pressure_eq (γ α : K) (h : ((M : K) - 1) * γ = 1 - ((M : K) - 1) * α)
    (m : Memory M) : ∑ p, m.pressure γ p = (m.heard : K) * (((M : K) - 1) * α) := by
  rw [sum_pressure, h]; ring

/-- **Remark 3**: without communication bias the trust of every actor vanishes identically,
which is the normalisation built into the unbiased state space `S` of equation (2). -/
theorem sum_pressure_eq_zero_of_bias_zero (γ : K) (h : ((M : K) - 1) * γ = 1)
    (m : Memory M) : ∑ p, m.pressure γ p = 0 := by
  rw [sum_pressure, h, sub_self, mul_zero]

/-- A null row is one belonging to an actor that has heard nothing: the easy direction of
the last claim of Remark 1. The converse holds when `(M - 1) α ≠ 0`. -/
@[simp]
theorem pressure_eq_zero_of_heard_eq_zero (γ : K) {m : Memory M} (hm : m.heard = 0)
    (p : Opinion M) : m.pressure γ p = 0 := by
  have hp : m.count p = 0 := by
    rw [heard] at hm
    exact Finset.sum_eq_zero_iff.1 hm p (Finset.mem_univ p)
  simp [pressure, hp, hm]

end Memory

end Bias

end SocialNetwork
