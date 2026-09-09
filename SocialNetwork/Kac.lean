/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Kac's lemma, in the form the paper uses it

The proof of Proposition 9 of arXiv:2607.19651 opens with

```
1 / μ̃^β (u) = E [R̃^{β,u} (u)] ≥ ∑_{m ≥ (M+1)N} P (R̃^{β,u} (u) ≥ m),
```

citing "the classical Kac's Lemma".  Only the second half of that line is used: the argument
needs an *upper* bound on `μ̃^β (u)`, so it needs `μ̃^β (u) · E [R̃^{β,u} (u)] ≤ 1` and never
the reverse inequality.

That distinction is what makes this file possible.  The *equality* of Kac's lemma is false
without irreducibility — take two absorbing states and the invariant measure `(½, ½)`: the
return time to either is `1`, not `2` — so proving it would first need Doeblin's criterion,
which Mathlib does not have.  The *inequality* holds for every invariant probability measure,
with no irreducibility, no recurrence and no existence theorem, and its proof is the
decomposition of `{the chain visits u before time m}` by the last such visit.

Nothing here mentions the social network, and nothing here is specific to the paper: this is
a statement about a Markov kernel on a countable space.  It is written at that generality
because it is exactly as easy, and because `Kernel.Invariant` is all it consumes.

**No counterpart in the paper**, which cites Kac's lemma rather than proving it.

## Main definitions

* `SocialNetwork.kacAvoid` — `kacAvoid κ u m v` is the probability, from `v`, that the chain
  avoids `u` at each of the times `0, 1, …, m-1`.

## Main results

* `SocialNetwork.kac_identity` — the exact finite-horizon identity behind Kac's lemma: the
  probability of having visited `u` before time `m` decomposes over the last such visit.
* `SocialNetwork.kac_tsum_le` — Kac's inequality, `μ {u} · E_u [R_u] ≤ 1`, with the
  expectation written as `∑_m P_u (R_u > m)`.
* `SocialNetwork.measure_singleton_le_of_avoid` — the shape Proposition 9 wants: a lower
  bound on the probability of avoiding `u` for `m` steps bounds `μ {u}` from above.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace SocialNetwork

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- `kacAvoid κ u m v` is the probability that the chain with kernel `κ`, started at `v`,
avoids `u` at each of the times `0, 1, …, m-1`.  In particular `kacAvoid κ u 0 v = 1`, and
`kacAvoid κ u m v = 0` as soon as `m ≥ 1` and `v = u`.

Written as a recursion on the horizon rather than as a measure on path space: the whole of
Kac's inequality is a statement about finitely many steps, so nothing here needs the
Ionescu-Tulcea construction. -/
noncomputable def kacAvoid (κ : Kernel α α) (u : α) : ℕ → α → ℝ≥0∞
  | 0, _ => 1
  | (m + 1), v => Set.indicator {u}ᶜ (fun v => ∫⁻ w, kacAvoid κ u m w ∂(κ v)) v

omit [Countable α] [MeasurableSingletonClass α] in
@[simp]
theorem kacAvoid_zero (κ : Kernel α α) (u : α) (v : α) : kacAvoid κ u 0 v = 1 := rfl

omit [Countable α] [MeasurableSingletonClass α] in
theorem kacAvoid_succ (κ : Kernel α α) (u : α) (m : ℕ) (v : α) :
    kacAvoid κ u (m + 1) v
      = Set.indicator {u}ᶜ (fun v => ∫⁻ w, kacAvoid κ u m w ∂(κ v)) v := rfl

omit [Countable α] [MeasurableSingletonClass α] in
theorem kacAvoid_succ_of_ne (κ : Kernel α α) {u v : α} (h : v ≠ u) (m : ℕ) :
    kacAvoid κ u (m + 1) v = ∫⁻ w, kacAvoid κ u m w ∂(κ v) :=
  Set.indicator_of_mem (by simpa using h) _

omit [Countable α] [MeasurableSingletonClass α] in
theorem kacAvoid_le_one (κ : Kernel α α) [IsMarkovKernel κ] (u : α) (m : ℕ) (v : α) :
    kacAvoid κ u m v ≤ 1 := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      rw [kacAvoid_succ]
      by_cases h : v ∈ ({u}ᶜ : Set α)
      · rw [Set.indicator_of_mem h]
        calc ∫⁻ w, kacAvoid κ u m w ∂(κ v) ≤ ∫⁻ _, 1 ∂(κ v) := lintegral_mono fun w => ih w
          _ = 1 := by simp
      · rw [Set.indicator_of_notMem h]; simp

omit [Countable α] [MeasurableSingletonClass α] in
/-- Avoiding `u` for longer is harder. -/
theorem kacAvoid_antitone (κ : Kernel α α) [IsMarkovKernel κ] (u : α) :
    ∀ {n m : ℕ}, n ≤ m → ∀ v, kacAvoid κ u m v ≤ kacAvoid κ u n v := by
  intro n m hnm
  induction m generalizing n with
  | zero => intro v; simp [Nat.le_zero.1 hnm]
  | succ m ih =>
      intro v
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using kacAvoid_le_one κ u (m + 1) v
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [kacAvoid_succ, kacAvoid_succ]
        by_cases h : v ∈ ({u}ᶜ : Set α)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
          exact lintegral_mono fun x => ih (by omega) x
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

/-- **Kac's identity at a finite horizon.**  Under an invariant probability measure `μ`, the
event "the chain visits `u` at some time before `m`" decomposes over the *last* such visit:
the visit at time `j` followed by `m - 1 - j` steps that avoid `u` has probability
`μ {u} · P_u (R_u > m - 1 - j)`, the `m` events are disjoint, and what is left over is the
event of never visiting `u` before `m`, of probability `∫ kacAvoid κ u m dμ`.

Invariance enters once, as `∫ (κ g) dμ = ∫ g dμ`; the rest is the splitting of an integral at
the singleton `{u}`.  No irreducibility, no recurrence, no ergodicity. -/
theorem kac_identity (κ : Kernel α α) [IsMarkovKernel κ] (μ : Measure α)
    [IsProbabilityMeasure μ] (hinv : Kernel.Invariant κ μ) (u : α) (m : ℕ) :
    (∑ n ∈ Finset.range m, μ {u} * ∫⁻ w, kacAvoid κ u n w ∂(κ u))
        + ∫⁻ v, kacAvoid κ u m v ∂μ = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      set g : α → ℝ≥0∞ := fun v => ∫⁻ w, kacAvoid κ u m w ∂(κ v) with hg
      -- Invariance, in the form `∫ (κ g) dμ = ∫ g dμ`.
      have hbind : ∫⁻ v, g v ∂μ = ∫⁻ w, kacAvoid κ u m w ∂μ := by
        rw [hg, ← MeasureTheory.Measure.lintegral_bind (Kernel.measurable κ).aemeasurable
          (Measurable.of_discrete (f := kacAvoid κ u m)).aemeasurable, hinv.def]
      -- Splitting that integral at `{u}` is exactly the step of the recursion.
      have hsplit : ∫⁻ v, g v ∂μ = μ {u} * g u + ∫⁻ v, kacAvoid κ u (m + 1) v ∂μ := by
        rw [← MeasureTheory.lintegral_add_compl g (MeasurableSet.singleton u)]
        congr 1
        · rw [Measure.restrict_singleton, MeasureTheory.lintegral_smul_measure,
            MeasureTheory.lintegral_dirac, smul_eq_mul]
        · rw [← MeasureTheory.lintegral_add_compl (kacAvoid κ u (m + 1))
            (MeasurableSet.singleton u)]
          have hzero : ∫⁻ v, kacAvoid κ u (m + 1) v ∂(μ.restrict {u}) = 0 := by
            rw [Measure.restrict_singleton, MeasureTheory.lintegral_smul_measure,
              MeasureTheory.lintegral_dirac, kacAvoid_succ,
              Set.indicator_of_notMem (by simp)]
            simp
          rw [hzero, zero_add]
          refine MeasureTheory.setLIntegral_congr_fun (by measurability) ?_
          intro v hv
          rw [kacAvoid_succ, Set.indicator_of_mem hv]
      rw [Finset.sum_range_succ]
      calc (∑ n ∈ Finset.range m, μ {u} * ∫⁻ w, kacAvoid κ u n w ∂(κ u))
              + μ {u} * ∫⁻ w, kacAvoid κ u m w ∂(κ u)
              + ∫⁻ v, kacAvoid κ u (m + 1) v ∂μ
          = (∑ n ∈ Finset.range m, μ {u} * ∫⁻ w, kacAvoid κ u n w ∂(κ u))
              + (μ {u} * g u + ∫⁻ v, kacAvoid κ u (m + 1) v ∂μ) := by rw [hg]; ring
        _ = (∑ n ∈ Finset.range m, μ {u} * ∫⁻ w, kacAvoid κ u n w ∂(κ u))
              + ∫⁻ v, kacAvoid κ u m v ∂μ := by rw [← hsplit, hbind]
        _ = 1 := ih

/-- **Kac's inequality**, `μ {u} · E_u [R_u] ≤ 1`, with the expectation of the return time
written as `∑_n P_u (R_u > n)`.

This is the half of Kac's lemma that Proposition 9 uses, and the half that does not need
irreducibility. -/
theorem kac_tsum_le (κ : Kernel α α) [IsMarkovKernel κ] (μ : Measure α)
    [IsProbabilityMeasure μ] (hinv : Kernel.Invariant κ μ) (u : α) :
    μ {u} * ∑' n : ℕ, ∫⁻ w, kacAvoid κ u n w ∂(κ u) ≤ 1 := by
  rw [ENNReal.tsum_mul_left.symm]
  refine ENNReal.tsum_le_of_sum_range_le fun m => ?_
  exact le_of_le_of_eq le_self_add (kac_identity κ μ hinv u m)

/-- The shape Proposition 9 wants: a lower bound `p` on the probability of avoiding `u`
along the whole of a run of `n` steps, valid for every `n`, bounds `μ {u}` from above by the
reciprocal of the total.

Stated with an arbitrary lower-bounding sequence `p` rather than with `kacAvoid` itself, since
the bound the paper produces — Proposition 7 for the first `(M+1)N` steps and Remark 5 for
the rest — is a geometric series and not the avoidance probability on the nose. -/
theorem measure_singleton_le_of_avoid (κ : Kernel α α) [IsMarkovKernel κ] (μ : Measure α)
    [IsProbabilityMeasure μ] (hinv : Kernel.Invariant κ μ) (u : α) (p : ℕ → ℝ≥0∞)
    (hp : ∀ n, p n ≤ ∫⁻ w, kacAvoid κ u n w ∂(κ u)) :
    μ {u} * ∑' n : ℕ, p n ≤ 1 :=
  le_trans (by gcongr with n; exact hp n) (kac_tsum_le κ μ hinv u)

end SocialNetwork
