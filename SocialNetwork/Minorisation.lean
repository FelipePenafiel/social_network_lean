/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Doeblin
import SocialNetwork.Markov

/-!
# The Doeblin minorisation of the skeleton chain

`SocialNetwork.Doeblin` proves the criterion in the abstract: a Markov kernel on a countable
space whose `n`-step kernel is bounded below at one state, uniformly over a set carrying the
measures, has at most one invariant probability measure carried by that set.  This file
supplies the minorisation for *this* chain, which is the argument at p. 17 of
arXiv:2607.19651, and concludes the uniqueness half of Theorem 1.2.

The bound proved here is: for every state `v ∈ S`, every `β ≥ 0` and every opinion `o`,

```
κ^{2N} (v, {l^o})  ≥  ζ_β^N · stepFloor^N,
```

where `l^o` is the canonical ladder of Definition 1, `ζ_β` is the constant of Proposition 8
and `stepFloor` is an explicit positive constant depending only on `N`, `M` and `β`.  Nothing
on the right depends on `v`, which is what Doeblin's criterion wants.

## The three ingredients

The paper's `2N` steps split in half, and the halves are proved by different means.

* **The descending sweep is deterministic.**  Let the actors `N-1, N-2, …, 0` express `o` in
  that order.  Each row is reset when its actor expresses and then rises by `M-1` once per
  later expression, so the actor expressing `j`-th from the end ends on the `j`-th rung —
  *whatever the matrix was to begin with*.  This is the paper's (12), and it is
  `SocialNetwork.skeleton_descendJump_eq_ladderOf`: no hypothesis on the starting matrix at
  all.  It is why the target state `l^o` can be a single point.

* **A bounded matrix makes every expression likely.**  The rates of equation (3) are
  exponentials of `β u(a,o)/(M-1)`, so from a matrix with entries at most `R` in absolute
  value the probability of any prescribed pair is at least `e^{-2βR/(M-1)}/(MN)`.  That is
  `SocialNetwork.stepFloor_le_jumpPMF`.  Expressions move entries by at most `M-1` each, so
  the box travels with the sweep and one `R` serves for all `N` steps.

* **Greedy expression produces such a matrix.**  Proposition 6
  (`SocialNetwork.entry_mem_of_mem_greedyEvents`) confines the matrix to `(-MN(M-1), N(M-1))`
  entrywise after `N` greedy expressions, and Proposition 8
  (`SocialNetwork.zeta_pow_le_pathMeasure_greedyEvents`) says that run has probability at
  least `ζ_β^N`, uniformly in the starting state.  This is the only half that needs `v ∈ S`.

## The bridge

Propositions 6 and 8 live on the sample space of realisations, and Doeblin's criterion is
stated for iterates of a kernel, so the two have to be identified:

```
κⁿ (v, A)  =  P^{β,v} (Ũ_n ∈ A).
```

That is `SocialNetwork.iterateKernel_skeletonKernel`, proved by induction on `n` from the
Markov property at time `1` (`SocialNetwork.pathMeasure_restart`).  With it the two halves
compose through `Kernel.comp` rather than on the path space, and the intermediate matrix is
integrated out by `lintegral_mono` against an indicator.

## Main results

* `SocialNetwork.iterateKernel_skeletonKernel` — the bridge.
* `SocialNetwork.skeleton_descendJump_eq_ladderOf` — the paper's (12).
* `SocialNetwork.stepFloor_le_jumpPMF` — one expression, bounded below on a box.
* `SocialNetwork.minorisation_iterateKernel` — **the minorisation**.
* `SocialNetwork.eq_of_invariant_skeletonKernel` — **Theorem 1.2, the uniqueness half**.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ} [NeZero N] [NeZero M] {β : ℝ}

/-! ### The `n`-step kernel as the law of the skeleton -/

section Bridge

/-- **The first expressed pair decomposes an event of the skeleton.**  Conditionally on the
first pair, the matrix at time `n + 1` is the matrix at time `n` of the chain restarted at the
matrix that pair reaches.  This is the Markov property at time `1`. -/
theorem lintegral_pathMeasure_skeleton (β : ℝ) (v : Pressure N M) (n : ℕ)
    (A : Set (Pressure N M)) :
    ∫⁻ w, pathMeasure β w {ω | skeleton w n ω ∈ A} ∂(skeletonKernel β v)
      = pathMeasure β v {ω | skeleton v (n + 1) ω ∈ A} := by
  rw [lintegral_skeletonKernel]
  have hunion : {ω : ℕ → Jump N M | skeleton v (n + 1) ω ∈ A}
      = ⋃ z ∈ (Finset.univ : Finset (Jump N M)),
          ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
            ∩ shiftPath 1 ⁻¹' {ω | skeleton (express z.1 z.2 v) n ω ∈ A}) := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro hω
      refine ⟨ω 0, fun k hk => by rw [Nat.lt_one_iff.1 hk], ?_⟩
      rwa [show n + 1 = 1 + n by omega, skeleton_add, skeleton_succ, skeleton_zero] at hω
    · rintro ⟨z, hz0, hz1⟩
      rw [show n + 1 = 1 + n by omega, skeleton_add, skeleton_succ, skeleton_zero,
        hz0 0 (by omega)]
      exact hz1
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Jump N M)))
      fun z : Jump N M => ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
        ∩ shiftPath 1 ⁻¹' {ω | skeleton (express z.1 z.2 v) n ω ∈ A}) := by
    intro z _ z' _ hne
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    rw [← hω.1 0 (by omega), ← hω'.1 0 (by omega)]
  have hmeas : ∀ z ∈ (Finset.univ : Finset (Jump N M)),
      MeasurableSet ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
        ∩ shiftPath 1 ⁻¹' {ω | skeleton (express z.1 z.2 v) n ω ∈ A}) := fun z _ =>
    (measurableSet_cylinderPath (fun _ => z) 1).inter
      (measurable_shiftPath 1 ((measurable_skeleton _ n) (measurableSet_pressure A)))
  rw [hunion, measure_biUnion_finset hdisj hmeas]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hstep := pathMeasure_restart (β := β) v (fun _ => z) 1
    (E := {ω : ℕ → Jump N M | skeleton (express z.1 z.2 v) n ω ∈ A})
    ((measurable_skeleton (express z.1 z.2 v) n) (measurableSet_pressure A))
  have hone : skeleton v 1 (fun _ => z) = express z.1 z.2 v := by
    rw [skeleton_succ, skeleton_zero]
  have hcyl : pathMeasure β v {ω : ℕ → Jump N M | ∀ k < 1, ω k = z} = jumpPMF β v z := by
    have := pathMeasure_cylinder (u := v) (β := β) (fun _ => z) 1
    simpa using this
  rw [hstep, hone, hcyl]

/-- **The bridge.**  The `n`-step kernel of the skeleton is the law of the matrix at time `n`
under the path measure: `κⁿ (v, A) = P^{β,v} (Ũ_n ∈ A)`.

Everything below is proved on the sample space, where Propositions 6 and 8 live, and consumed
by `SocialNetwork.eq_of_invariant_of_iterate_minorisation`, which is stated for iterates of a
kernel.  This is what carries one to the other. -/
theorem iterateKernel_skeletonKernel (β : ℝ) (A : Set (Pressure N M)) :
    ∀ (n : ℕ) (v : Pressure N M),
      iterateKernel (skeletonKernel β) n v A = pathMeasure β v {ω | skeleton v n ω ∈ A} := by
  intro n
  induction n with
  | zero =>
      intro v
      rw [iterateKernel_zero, Kernel.id_apply,
        Measure.dirac_apply' _ (measurableSet_pressure A)]
      by_cases hv : v ∈ A
      · have huniv : {ω : ℕ → Jump N M | skeleton v 0 ω ∈ A} = Set.univ := by
          ext ω
          simpa using hv
        rw [huniv, measure_univ, Set.indicator_of_mem hv]
        rfl
      · have hempty : {ω : ℕ → Jump N M | skeleton v 0 ω ∈ A} = ∅ := by
          ext ω
          simpa using hv
        rw [hempty, measure_empty, Set.indicator_of_notMem hv]
  | succ n ih =>
      intro v
      rw [iterateKernel_succ_apply' _ n v (measurableSet_pressure A),
        lintegral_congr fun w => ih w, lintegral_pathMeasure_skeleton]

end Bridge


/-! ### The descending sweep -/

section Descend

/-- The actor who makes the `k`-th expression of the descending sweep: `N - 1 - k`, so that
the sweep runs through the actors from `N - 1` down to `0`. -/
def descendActor (N : ℕ) [NeZero N] (k : ℕ) : Actor N :=
  ⟨N - 1 - k, lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne N)) one_pos)⟩

@[simp] theorem descendActor_val (k : ℕ) : ((descendActor N k : Actor N) : ℕ) = N - 1 - k := rfl

/-- The `k`-th expressed pair of the descending sweep of `o`. -/
def descendJump (o : Opinion M) (k : ℕ) : Jump N M := (descendActor N k, o)

omit [NeZero M] in
@[simp] theorem descendJump_fst (o : Opinion M) (k : ℕ) :
    (descendJump (N := N) o k).1 = descendActor N k := rfl

omit [NeZero M] in
@[simp] theorem descendJump_snd (o : Opinion M) (k : ℕ) :
    (descendJump (N := N) o k).2 = o := rfl

/-- The matrix the sweep has reached after `k` of its `N` expressions.  The actors
`N - k, …, N - 1` have already expressed: their rows were reset and have risen once for each
later expression, so they already carry their final ladder values shifted by `k - N`.  The
others have merely listened. -/
def descendState (o : Opinion M) (u : Pressure N M) (k : ℕ) : Pressure N M := fun a p =>
  if N - k ≤ (a : ℕ) then
    (if p = o then ((M : ℤ) - 1) * ((k : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ))
      else -((k : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ)))
  else
    (if p = o then u a p + (k : ℤ) * ((M : ℤ) - 1) else u a p - (k : ℤ))

omit [NeZero N] [NeZero M] in
theorem descendState_of_le (o : Opinion M) (u : Pressure N M) {k : ℕ} {a : Actor N}
    (h : N - k ≤ (a : ℕ)) (p : Opinion M) :
    descendState o u k a p
      = if p = o then ((M : ℤ) - 1) * ((k : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ))
        else -((k : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ)) := if_pos h

omit [NeZero N] [NeZero M] in
theorem descendState_of_not_le (o : Opinion M) (u : Pressure N M) {k : ℕ} {a : Actor N}
    (h : ¬ N - k ≤ (a : ℕ)) (p : Opinion M) :
    descendState o u k a p
      = if p = o then u a p + (k : ℤ) * ((M : ℤ) - 1) else u a p - (k : ℤ) := if_neg h

omit [NeZero M] in
/-- **The paper's (12).**  Following the descending sweep for `k ≤ N` expressions from any
matrix reaches `SocialNetwork.descendState`. -/
theorem skeleton_descendJump (o : Opinion M) (u : Pressure N M) :
    ∀ {k : ℕ}, k ≤ N → skeleton u k (descendJump o) = descendState o u k := by
  intro k
  induction k with
  | zero =>
      intro _
      funext a p
      have ha : ¬ N - 0 ≤ (a : ℕ) := by have := a.isLt; omega
      rw [skeleton_zero, descendState_of_not_le o u ha p]
      by_cases hp : p = o
      · rw [if_pos hp]; push_cast; ring
      · rw [if_neg hp]; push_cast; ring
  | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      rw [skeleton_succ, ih hkN, descendJump_fst, descendJump_snd]
      funext a p
      by_cases hab : a = descendActor N k
      · have ha : (a : ℕ) = N - (k + 1) := by rw [hab, descendActor_val]; omega
        have hcond : N - (k + 1) ≤ (a : ℕ) := by omega
        have hz : ((k : ℕ) + 1 : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ) = 0 := by omega
        rw [hab, express_self, ← hab, descendState_of_le o u hcond p]
        push_cast
        rw [hz]
        by_cases hp : p = o
        · rw [if_pos hp, mul_zero]
        · rw [if_neg hp, neg_zero]
      · have hne : (a : ℕ) ≠ N - 1 - k := fun h => hab (Fin.ext h)
        by_cases hle : N - k ≤ (a : ℕ)
        · have hcond : N - (k + 1) ≤ (a : ℕ) := by omega
          have hsucc : ((k : ℕ) + 1 : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ)
              = ((k : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ)) + 1 := by ring
          rw [descendState_of_le o u hcond p]
          push_cast
          rw [hsucc]
          by_cases hp : p = o
          · rw [hp, express_of_ne_of_eq hab o, descendState_of_le o u hle o, if_pos rfl,
              if_pos rfl]
            ring
          · rw [express_of_ne_of_ne hab hp, descendState_of_le o u hle p, if_neg hp, if_neg hp]
            ring
        · have hcond : ¬ N - (k + 1) ≤ (a : ℕ) := by omega
          rw [descendState_of_not_le o u hcond p]
          push_cast
          by_cases hp : p = o
          · rw [hp, express_of_ne_of_eq hab o, descendState_of_not_le o u hle o, if_pos rfl,
              if_pos rfl]
            ring
          · rw [express_of_ne_of_ne hab hp, descendState_of_not_le o u hle p, if_neg hp,
              if_neg hp]
            ring

omit [NeZero M] in
/-- **The sweep lands on the canonical ladder, from wherever it starts.**  Each row is reset
when its actor expresses and then rises by `M - 1` once per later expression, so the actor who
expresses `j`-th from the end carries exactly the `j`-th rung. -/
theorem skeleton_descendJump_eq_ladderOf (o : Opinion M) (u : Pressure N M) :
    skeleton u N (descendJump o) = ladderOf N o := by
  rw [skeleton_descendJump o u le_rfl]
  funext a p
  have hcond : N - N ≤ (a : ℕ) := by omega
  rw [descendState_of_le o u hcond p]
  have hz : (N : ℤ) - (N : ℤ) + ((a : ℕ) : ℤ) = ((a : ℕ) : ℤ) := by ring
  rw [hz]
  rfl

end Descend


/-! ### One expression, bounded below uniformly on a box -/

section StepFloor

/-- The uniform lower bound on the probability of one prescribed expression, from a matrix
whose entries are at most `R` in absolute value.  The rates of equation (3) are exponentials
of bounded exponents, so their ratio is bounded below:

```
P (A = a, O = o ∣ U = w) = e^{β w(a,o)/(M-1)} / ∑_{b,p} e^{β w(b,p)/(M-1)}
                         ≥ e^{-βR/(M-1)} / (MN · e^{βR/(M-1)}).
```
-/
noncomputable def stepFloor (N M : ℕ) (β : ℝ) (R : ℤ) : ℝ :=
  Real.exp (-(2 * β * (R : ℝ)) / ((M : ℝ) - 1)) / ((M : ℝ) * (N : ℝ))

theorem stepFloor_pos (N M : ℕ) [NeZero N] [NeZero M] (β : ℝ) (R : ℤ) :
    0 < stepFloor N M β R := by
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact div_pos (Real.exp_pos _) (mul_pos hM hN)

/-- **The third ingredient of the minorisation.**  From a matrix confined to a box, every
single expression has probability bounded below, uniformly over the box. -/
theorem stepFloor_le_jumpPMF (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {R : ℤ} {w : Pressure N M}
    (hw : ∀ a p, |w a p| ≤ R) (q : Jump N M) :
    ENNReal.ofReal (stepFloor N M β R) ≤ jumpPMF β w q := by
  have hMpos : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hMN : (0 : ℝ) < (M : ℝ) * (N : ℝ) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact mul_pos hM0 hN0
  have hMN0 : (M : ℝ) * (N : ℝ) ≠ 0 := ne_of_gt hMN
  have hM0 : (M : ℝ) ≠ 0 := fun h => hMN0 (by rw [h, zero_mul])
  have hN0 : (N : ℝ) ≠ 0 := fun h => hMN0 (by rw [h, mul_zero])
  have hM1 : ((M : ℝ) - 1) ≠ 0 := ne_of_gt hMpos
  -- the entry bound, read in `ℝ`
  have hbound : ∀ z : Jump N M, |((w z.1 z.2 : ℤ) : ℝ)| ≤ (R : ℝ) := by
    intro z
    have h := hw z.1 z.2
    calc |((w z.1 z.2 : ℤ) : ℝ)| = ((|w z.1 z.2| : ℤ) : ℝ) := by rw [Int.cast_abs]
      _ ≤ (R : ℝ) := by exact_mod_cast h
  -- the numerator is at least `e^{-βR/(M-1)}`
  have hnum : Real.exp (-(β * (R : ℝ)) / ((M : ℝ) - 1)) ≤ jumpRate β w q.1 q.2 := by
    refine Real.exp_le_exp.2 ?_
    have h := (abs_le.1 (hbound q)).1
    have h1 : -(β * (R : ℝ)) ≤ β * ((w q.1 q.2 : ℤ) : ℝ) := by nlinarith
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (inv_pos.2 hMpos).le
  -- the denominator is at most `MN e^{βR/(M-1)}`
  have hden : (∑ z : Jump N M, jumpRate β w z.1 z.2)
      ≤ (M : ℝ) * (N : ℝ) * Real.exp (β * (R : ℝ) / ((M : ℝ) - 1)) := by
    have hle : ∀ z ∈ (Finset.univ : Finset (Jump N M)),
        jumpRate β w z.1 z.2 ≤ Real.exp (β * (R : ℝ) / ((M : ℝ) - 1)) := by
      intro z _
      refine Real.exp_le_exp.2 ?_
      have h := (abs_le.1 (hbound z)).2
      have h1 : β * ((w z.1 z.2 : ℤ) : ℝ) ≤ β * (R : ℝ) := mul_le_mul_of_nonneg_left h hβ
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h1 (inv_pos.2 hMpos).le
    have h1 := Finset.sum_le_card_nsmul (Finset.univ : Finset (Jump N M))
      (fun z => jumpRate β w z.1 z.2) (Real.exp (β * (R : ℝ) / ((M : ℝ) - 1))) hle
    rw [nsmul_eq_mul] at h1
    have hcard : (((Finset.univ : Finset (Jump N M)).card : ℕ) : ℝ) = (M : ℝ) * (N : ℝ) := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      push_cast
      ring
    rwa [hcard] at h1
  have hS : (0 : ℝ) < ∑ z : Jump N M, jumpRate β w z.1 z.2 :=
    Finset.sum_pos (fun z _ => jumpRate_pos β w z.1 z.2) ⟨q, Finset.mem_univ q⟩
  -- the real inequality
  have hkey : stepFloor N M β R * (∑ z : Jump N M, jumpRate β w z.1 z.2)
      ≤ jumpRate β w q.1 q.2 := by
    calc stepFloor N M β R * (∑ z : Jump N M, jumpRate β w z.1 z.2)
        ≤ stepFloor N M β R
            * ((M : ℝ) * (N : ℝ) * Real.exp (β * (R : ℝ) / ((M : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hden (stepFloor_pos N M β R).le
      _ = Real.exp (-(2 * β * (R : ℝ)) / ((M : ℝ) - 1))
            * Real.exp (β * (R : ℝ) / ((M : ℝ) - 1)) := by
          unfold stepFloor
          field_simp
      _ = Real.exp (-(β * (R : ℝ)) / ((M : ℝ) - 1)) := by
          rw [← Real.exp_add]
          congr 1
          field_simp
          ring
      _ ≤ jumpRate β w q.1 q.2 := hnum
  have hreal : stepFloor N M β R
      ≤ jumpRate β w q.1 q.2 / (∑ z : Jump N M, jumpRate β w z.1 z.2) :=
    (le_div_iff₀ hS).2 hkey
  -- transported to the measure
  have hsum : (∑' z : Jump N M, jumpWeight β w z)
      = ENNReal.ofReal (∑ z : Jump N M, jumpRate β w z.1 z.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun z hz => absurd (Finset.mem_univ z) hz,
      ENNReal.ofReal_sum_of_nonneg fun z _ => (jumpRate_pos β w z.1 z.2).le]
    rfl
  rw [jumpPMF_apply, hsum]
  show ENNReal.ofReal (stepFloor N M β R)
    ≤ ENNReal.ofReal (jumpRate β w q.1 q.2) * _
  rw [← ENNReal.ofReal_inv_of_pos hS, ← ENNReal.ofReal_mul (jumpRate_pos β w q.1 q.2).le,
    ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The box travels with the sweep -/

omit [NeZero N] [NeZero M] in
/-- One expression moves every entry by at most `M - 1`. -/
theorem abs_express_le (hM : 2 ≤ M) {R : ℤ} {w : Pressure N M} (hw : ∀ a p, |w a p| ≤ R)
    (b : Actor N) (o : Opinion M) (a : Actor N) (p : Opinion M) :
    |express b o w a p| ≤ R + ((M : ℤ) - 1) := by
  have hR : 0 ≤ R := le_trans (abs_nonneg _) (hw a p)
  have hM1 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  by_cases hab : a = b
  · rw [hab, express_self, abs_zero]
    omega
  · by_cases hp : p = o
    · rw [hp, express_of_ne_of_eq hab o]
      have h := abs_le.1 (hw a o)
      rw [abs_le]
      omega
    · rw [express_of_ne_of_ne hab hp]
      have h := abs_le.1 (hw a p)
      rw [abs_le]
      omega

omit [NeZero N] [NeZero M] in
/-- After `k` expressions the entries have moved by at most `k (M - 1)`, whatever was
expressed. -/
theorem abs_skeleton_le (hM : 2 ≤ M) {R : ℤ} {w : Pressure N M} (hw : ∀ a p, |w a p| ≤ R)
    (ζ : ℕ → Jump N M) (k : ℕ) (a : Actor N) (p : Opinion M) :
    |skeleton w k ζ a p| ≤ R + (k : ℤ) * ((M : ℤ) - 1) := by
  induction k generalizing a p with
  | zero => simpa using hw a p
  | succ k ih =>
      rw [skeleton_succ]
      have hstep := abs_express_le (R := R + (k : ℤ) * ((M : ℤ) - 1)) hM (fun a p => ih a p)
        (ζ k).1 (ζ k).2 a p
      push_cast
      linarith

end StepFloor


/-! ### The minorisation, and the uniqueness of the invariant measure -/

section Minorisation

omit [NeZero N] [NeZero M] in
/-- The box the matrix is confined to: entries at most `R` in absolute value. -/
def boundedSet (N M : ℕ) (R : ℤ) : Set (Pressure N M) := {w | ∀ a p, |w a p| ≤ R}

/-- The bound of Proposition 6: after `N` greedy expressions the entries lie strictly between
`-MN(M-1)` and `N(M-1)`, hence within `MN(M-1)` of zero. -/
def greedyBound (N M : ℕ) : ℤ := (M : ℤ) * (N : ℤ) * ((M : ℤ) - 1)

/-- **The second half of the minorisation, on the sample space.**  Following the descending
sweep for its `N` expressions has probability at least `stepFloor ^ N`, since every one of
them is made from a matrix still confined to a box. -/
theorem stepFloor_pow_le_pathMeasure_descend (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {R : ℤ}
    {w : Pressure N M} (hw : ∀ a p, |w a p| ≤ R) (o : Opinion M) :
    ENNReal.ofReal (stepFloor N M β (R + (N : ℤ) * ((M : ℤ) - 1))) ^ N
      ≤ pathMeasure β w {ω | ∀ k < N, ω k = descendJump o k} := by
  have hconst : ENNReal.ofReal (stepFloor N M β (R + (N : ℤ) * ((M : ℤ) - 1))) ^ N
      = ∏ _m ∈ Finset.range N,
          ENNReal.ofReal (stepFloor N M β (R + (N : ℤ) * ((M : ℤ) - 1))) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [pathMeasure_cylinder, hconst]
  refine Finset.prod_le_prod' fun m hm => ?_
  refine stepFloor_le_jumpPMF hM hβ (fun a p => ?_) _
  have h := abs_skeleton_le hM hw (descendJump o) m a p
  have hmN : (m : ℤ) ≤ (N : ℤ) := by
    have hm' := Finset.mem_range.1 hm
    exact_mod_cast Nat.le_of_lt hm'
  have hM1 : (0 : ℤ) ≤ (M : ℤ) - 1 := by
    have h2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    omega
  have hstep : (m : ℤ) * ((M : ℤ) - 1) ≤ (N : ℤ) * ((M : ℤ) - 1) :=
    mul_le_mul_of_nonneg_right hmN hM1
  linarith

/-- **The second half of the minorisation.**  From a matrix confined to a box, the `N`-step
kernel charges the canonical ladder `l^o` by at least `stepFloor ^ N`. -/
theorem stepFloor_pow_le_iterateKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {R : ℤ}
    {w : Pressure N M} (hw : ∀ a p, |w a p| ≤ R) (o : Opinion M) :
    ENNReal.ofReal (stepFloor N M β (R + (N : ℤ) * ((M : ℤ) - 1))) ^ N
      ≤ iterateKernel (skeletonKernel β) N w {ladderOf N o} := by
  rw [iterateKernel_skeletonKernel]
  refine le_trans (stepFloor_pow_le_pathMeasure_descend hM hβ hw o) (measure_mono ?_)
  intro ω hω
  show skeleton w N ω ∈ ({ladderOf N o} : Set (Pressure N M))
  rw [Set.mem_singleton_iff, skeleton_congr w N (fun k hk => hω k hk),
    skeleton_descendJump_eq_ladderOf]

/-- **The first half of the minorisation.**  `N` greedy expressions confine the matrix to the
box of Proposition 6, and Proposition 8 says they happen with probability at least
`ζ_β ^ N`. -/
theorem zeta_pow_le_iterateKernel_boundedSet (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {v : Pressure N M} (hv : IsState v) :
    ENNReal.ofReal (zeta N M β) ^ N
      ≤ iterateKernel (skeletonKernel β) N v (boundedSet N M (greedyBound N M)) := by
  rw [iterateKernel_skeletonKernel]
  refine le_trans (zeta_pow_le_pathMeasure_greedyEvents hM hβ N) (measure_mono ?_)
  intro ω hω
  show skeleton v N ω ∈ boundedSet N M (greedyBound N M)
  intro a p
  have h : -((M : ℤ) * (N : ℤ) * ((M : ℤ) - 1)) < skeleton v N ω a p
      ∧ skeleton v N ω a p < (N : ℤ) * ((M : ℤ) - 1) :=
    entry_mem_of_mem_greedyEvents hM hv hω a p
  have hM1 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hmono : (N : ℤ) * ((M : ℤ) - 1) ≤ (M : ℤ) * (N : ℤ) * ((M : ℤ) - 1) := by nlinarith
  rw [abs_le]
  constructor
  · have := h.1
    unfold greedyBound
    linarith
  · have := h.2
    unfold greedyBound
    linarith

/-- **The Doeblin minorisation of the skeleton chain**, the argument at p. 17 of the paper.

From any state, `2N` expressions reach the canonical ladder `l^o` with probability at least
`ζ_β^N · stepFloor^N`, and the bound does not depend on the state.  The first `N` are greedy,
which by Proposition 6 confines the matrix to a box and by Proposition 8 costs at most
`ζ_β^N`; the last `N` are the descending sweep, which from a matrix so confined lands on
`l^o` and costs at most `stepFloor^N` by the boundedness of the exponents in equation (3). -/
theorem minorisation_iterateKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (o : Opinion M)
    {v : Pressure N M} (hv : IsState v) :
    ENNReal.ofReal (zeta N M β) ^ N
        * ENNReal.ofReal (stepFloor N M β (greedyBound N M + (N : ℤ) * ((M : ℤ) - 1))) ^ N
      ≤ iterateKernel (skeletonKernel β) (N + N) v {ladderOf N o} := by
  set c₂ := ENNReal.ofReal (stepFloor N M β (greedyBound N M + (N : ℤ) * ((M : ℤ) - 1))) ^ N
    with hc₂
  rw [iterateKernel_add, Kernel.comp_apply' _ _ _ (measurableSet_pressure _)]
  have hind : ∀ w, Set.indicator (boundedSet N M (greedyBound N M)) (fun _ => c₂) w
      ≤ iterateKernel (skeletonKernel β) N w {ladderOf N o} := by
    intro w
    by_cases hwb : w ∈ boundedSet N M (greedyBound N M)
    · rw [Set.indicator_of_mem hwb, hc₂]
      exact stepFloor_pow_le_iterateKernel hM hβ hwb o
    · rw [Set.indicator_of_notMem hwb]
      exact zero_le
  calc ENNReal.ofReal (zeta N M β) ^ N * c₂
      ≤ iterateKernel (skeletonKernel β) N v (boundedSet N M (greedyBound N M)) * c₂ := by
        gcongr
        exact zeta_pow_le_iterateKernel_boundedSet hM hβ hv
    _ = ∫⁻ w, Set.indicator (boundedSet N M (greedyBound N M)) (fun _ => c₂) w
          ∂(iterateKernel (skeletonKernel β) N v) := by
        rw [lintegral_indicator (measurableSet_pressure _), setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w, iterateKernel (skeletonKernel β) N w {ladderOf N o}
          ∂(iterateKernel (skeletonKernel β) N v) := lintegral_mono hind

/-- **Theorem 1.2, the uniqueness half.**  The skeleton chain has at most one invariant
probability measure carried by the state space `S`.

This is `SocialNetwork.eq_of_invariant_of_iterate_minorisation` fed with
`SocialNetwork.minorisation_iterateKernel`.  Existence is the half that is not here. -/
theorem eq_of_invariant_skeletonKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {μ ν : Measure (Pressure N M)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμS : μ (stateSet N M)ᶜ = 0) (hνS : ν (stateSet N M)ᶜ = 0)
    (hμ : Kernel.Invariant (skeletonKernel β) μ)
    (hν : Kernel.Invariant (skeletonKernel β) ν) : μ = ν := by
  have hpos : 0 < ENNReal.ofReal (zeta N M β) ^ N
      * ENNReal.ofReal (stepFloor N M β (greedyBound N M + (N : ℤ) * ((M : ℤ) - 1))) ^ N := by
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · exact (ENNReal.ofReal_pos.2 (zeta_pos N M β)).ne'
    · exact (ENNReal.ofReal_pos.2 (stepFloor_pos N M β _)).ne'
  exact eq_of_invariant_of_iterate_minorisation (skeletonKernel β) (N + N) hpos
    (fun v hv => minorisation_iterateKernel hM hβ ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ hv)
    hμS hνS hμ hν

end Minorisation

end SocialNetwork
