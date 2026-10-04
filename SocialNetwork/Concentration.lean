/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Transfer

/-!
# Theorem 2.1: the invariant measure concentrates on the ladders

The proof at pp. 20–21 of arXiv:2607.19651 writes `μ^β` through equation (13), as `μ̃^β / q_β`
normalised, and bounds the two sums that come out of it:

```
μ^β (L)  =  A / (A + B),     A = ∑_{u ∈ L} μ̃^β (u) / q_β (u),     B = ∑_{u ∉ L} μ̃^β (u) / q_β (u).
```

`A` is bounded below by `μ̃^β (L) / (MN e^{β(N-1)})`, since every rate out of a ladder is at most
`e^{β(N-1)}`, and `μ̃^β (L)` is bounded below by Propositions 7 and 8.  `B` is split by the size
of the largest entry: where it is below `N`, a state off `L` is off `L̂` as well, and
Proposition 9 with Corollary 10 bounds each term; where it is at least `N`, the rate alone is
at least `e^{βN}`.  There are finitely many states of the first kind, and their number does
not depend on `β`.

Everything the proof calls is in the library: equation (13) and `μ̃^β` in
`SocialNetwork.Transfer` and `SocialNetwork.ContinuousTime`, Propositions 7 and 9 and
Corollary 10 in `SocialNetwork.Appendix`, Proposition 8 in `SocialNetwork.Greedy`.  The proof
therefore inherits `sorryAx` from Propositions 7 and 9 and Corollary 10, which is to say from
Lemma 20, and from nothing else.

The statement lived in `SocialNetwork.ContinuousTime`, which comes before equation (13) in the
import order; it is proved here, after it.

## Main statements

* `SocialNetwork.totalRate_le_of_mem_ladderSet` — `q_β (l) ≤ MN e^{β(N-1)}` on `L`.
* `SocialNetwork.IsSteepLadder.isLadder_of_lt` — a state of `L̂` whose entries are below `N` is
  in `L`.
* `SocialNetwork.zeta_pow_le_measure_ladderSet` — `μ̃^β (L) ≥ ζ_β^{(M+1)N}`.
* `SocialNetwork.measure_ladderSet_ge` — **Theorem 2.1**.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ}

/-! ### The three facts about states the proof uses -/

section States

/-- On a ladder every entry is at most `N - 1` in the paper's coordinates: the supported column
takes the values `0, …, N - 1`, and every other entry is non-positive. -/
theorem IsLadder.le (hM : 2 ≤ M) {o : Opinion M} {v : Pressure N M} (hv : IsLadder o v)
    (a : Actor N) (p : Opinion M) :
    v a p ≤ ((M : ℤ) - 1) * ((N : ℤ) - 1) := by
  have hM1 : (1 : ℤ) ≤ (M : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    linarith
  obtain ⟨k, hk⟩ := mem_ladderValues_iff.1 (hv.mem_ladderValues a)
  have hkN : ((k : ℕ) : ℤ) ≤ (N : ℤ) - 1 := by have := k.isLt; omega
  have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
  have hcol : v a o ≤ ((M : ℤ) - 1) * ((N : ℤ) - 1) := by
    rw [hk]
    exact mul_le_mul_of_nonneg_left hkN (by linarith)
  by_cases hp : p = o
  · subst hp
    exact hcol
  · have h0 : 0 ≤ v a o := by
      rw [hk]
      exact mul_nonneg (by linarith) hk0
    have hother := hv.other a p hp
    have hle : v a p ≤ 0 := by
      by_contra hcon
      have hpos := lt_of_not_ge hcon
      nlinarith
    have hrhs : (0 : ℤ) ≤ ((M : ℤ) - 1) * ((N : ℤ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- **Supplies a step the paper asserts.**  The proof of Theorem 2.1 reads "by noting that
`q_β (l) ≤ MN e^{β(N-1)}`, for any `l ∈ L`": each of the `MN` rates is `e^{β u(a,o)}` with
`u (a, o) ≤ N - 1`, by `SocialNetwork.IsLadder.le`. -/
theorem totalRate_le_of_mem_ladderSet (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M}
    (hv : v ∈ ladderSet N M) :
    totalRate β v ≤ ((M * N : ℕ) : ℝ) * Real.exp (β * ((N : ℝ) - 1)) := by
  obtain ⟨o, hv⟩ := hv
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hterm : ∀ p : Jump N M, jumpRate β v p.1 p.2 ≤ Real.exp (β * ((N : ℝ) - 1)) := by
    intro p
    rw [jumpRate]
    refine Real.exp_le_exp.2 ?_
    have h : ((v p.1 p.2 : ℤ) : ℝ) ≤ ((M : ℝ) - 1) * ((N : ℝ) - 1) := by
      exact_mod_cast hv.le hM p.1 p.2
    rw [div_le_iff₀ hM1]
    have := mul_le_mul_of_nonneg_left h hβ
    linarith
  calc totalRate β v = ∑ p : Jump N M, jumpRate β v p.1 p.2 := rfl
    _ ≤ ∑ _p : Jump N M, Real.exp (β * ((N : ℝ) - 1)) := Finset.sum_le_sum fun p _ => hterm p
    _ = ((M * N : ℕ) : ℝ) * Real.exp (β * ((N : ℝ) - 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [Finset.card_univ, Fintype.card_prod, Nat.mul_comm]

/-- A state with an entry of at least `N`, in the paper's coordinates, jumps at total rate at
least `e^{βN}`, hence at least `e^{β(N-1)} e^{β/(M-1)}`.

**Supplies a step the paper asserts**: "for any `u ∉ L`, with `max u(a, o) ≥ N`, we have
`q_β (u) ≥ e^{βN}`".  The weaker form is the one the proof combines with the others. -/
theorem exp_mul_exp_le_totalRate (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M}
    {a : Actor N} {p : Opinion M} (hap : (N : ℤ) * ((M : ℤ) - 1) ≤ v a p) :
    Real.exp (β * ((N : ℝ) - 1)) * Real.exp (β / ((M : ℝ) - 1)) ≤ totalRate β v := by
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have h1 : (N : ℝ) * ((M : ℝ) - 1) ≤ (v a p : ℝ) := by exact_mod_cast hap
  have hterm : Real.exp (β * ((N : ℝ) - 1)) * Real.exp (β / ((M : ℝ) - 1))
      ≤ jumpRate β v a p := by
    rw [← Real.exp_add, jumpRate]
    refine Real.exp_le_exp.2 ?_
    have hdiv : β / ((M : ℝ) - 1) ≤ β := div_le_self hβ (by linarith)
    have hN : β * (N : ℝ) ≤ β * (v a p : ℝ) / ((M : ℝ) - 1) := by
      rw [le_div_iff₀ hM1]
      have := mul_le_mul_of_nonneg_left h1 hβ
      linarith
    linarith
  refine hterm.trans ?_
  rw [totalRate]
  exact Finset.single_le_sum (f := fun p : Jump N M => jumpRate β v p.1 p.2)
    (fun p _ => (jumpRate_pos β v p.1 p.2).le) (Finset.mem_univ (a, p))

/-- A state of `L̂^o` whose `o`-column stays below `N`, in the paper's coordinates, is in `L^o`:
`N` distinct integers in `{0, …, N - 1}` are all of them.

This is the step "for any `u ∉ L` and `max u(a, o) < N`, we have that `u ∉ L̂`" of the proof of
Theorem 2.1, which the paper asserts. -/
theorem IsSteepLadder.isLadder_of_lt (hM : 2 ≤ M) {o : Opinion M} {v : Pressure N M}
    (hv : IsSteepLadder o v) (hlt : ∀ a, v a o < (N : ℤ) * ((M : ℤ) - 1)) :
    IsLadder o v := by
  have hM1 : (1 : ℤ) ≤ (M : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
    linarith
  refine ⟨hv.isState, ?_, hv.other⟩
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨k, hk⟩ := hv.dvd a
    have h0 := hv.nonneg a
    have hl := hlt a
    rw [hk] at h0 hl
    have hk0 : 0 ≤ k := by nlinarith
    have hkN : k < N := by nlinarith
    refine mem_ladderValues_iff.2 ⟨⟨k.toNat, by omega⟩, ?_⟩
    rw [hk]
    simp [Int.toNat_of_nonneg hk0]
  · rw [Finset.card_image_of_injective _ hv.injective, Finset.card_univ, Fintype.card_fin]
    exact Finset.card_image_le.trans (by simp)

/-- **Supplies a step the paper asserts**: the contrapositive the proof of Theorem 2.1 uses. -/
theorem notMem_steepLadderSet_of_lt (hM : 2 ≤ M) {v : Pressure N M} (hv : v ∉ ladderSet N M)
    (hlt : ∀ a p, v a p < (N : ℤ) * ((M : ℤ) - 1)) : v ∉ steepLadderSet N M := by
  rintro ⟨o, ho⟩
  exact hv ⟨o, ho.isLadder_of_lt hM fun a => hlt a o⟩

/-- The box of `SocialNetwork.Minorisation` is finite. -/
theorem boundedSet_finite (R : ℤ) : (boundedSet N M R).Finite := by
  have h : boundedSet N M R
      = Set.univ.pi fun _ : Actor N => Set.univ.pi fun _ : Opinion M => Set.Icc (-R) R := by
    ext w
    simp only [boundedSet, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
  rw [h]
  exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _

/-- A state whose entries are all below `N`, in the paper's coordinates, lies in a box that does
not depend on it: each row sums to zero (Remark 3), so no entry is below `-(M-1)N`.

**Supplies a step the paper asserts**: that `K(N, M) = |{u ∉ L, max u(a, o) < N}|` is finite. -/
theorem IsState.mem_boundedSet_of_lt (hM : 2 ≤ M) {v : Pressure N M} (hv : IsState v)
    (hlt : ∀ a p, v a p < (N : ℤ) * ((M : ℤ) - 1)) :
    v ∈ boundedSet N M (greedyBound N M) := by
  intro a p
  have hM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hrow : v a p + ∑ q ∈ Finset.univ.erase p, v a q = 0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    exact hv.trust_eq_zero a
  have hrest : ∑ q ∈ Finset.univ.erase p, v a q
      ≤ ((M : ℤ) - 1) * ((N : ℤ) * ((M : ℤ) - 1)) := by
    calc ∑ q ∈ Finset.univ.erase p, v a q
        ≤ ∑ _q ∈ Finset.univ.erase p, (N : ℤ) * ((M : ℤ) - 1) :=
          Finset.sum_le_sum fun q _ => (hlt a q).le
      _ = ((M : ℤ) - 1) * ((N : ℤ) * ((M : ℤ) - 1)) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast [Nat.cast_sub (by omega : 1 ≤ M)]
          ring
  have hN0 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hNM : (0 : ℤ) ≤ (N : ℤ) * ((M : ℤ) - 1) := mul_nonneg hN0 (by linarith)
  have hbox : ((M : ℤ) - 1) * ((N : ℤ) * ((M : ℤ) - 1)) ≤ (M : ℤ) * (N : ℤ) * ((M : ℤ) - 1) := by
    nlinarith
  have hlow : (N : ℤ) * ((M : ℤ) - 1) ≤ (M : ℤ) * (N : ℤ) * ((M : ℤ) - 1) := by nlinarith
  rw [abs_le, greedyBound]
  constructor
  · linarith
  · linarith [hlt a p]

end States

/-! ### Theorem 2.1 -/

section Theorem21

variable [NeZero N] [NeZero M]

/-- `μ̃^β (L) ≥ ζ_β^{(M+1)N}` for any invariant probability measure of the skeleton carried by `S`.

**Supplies a step the paper asserts.**  The proof of Theorem 2.1 reads "by using Propositions 7
and 8 we obtain the bound `μ̃^β (L) ≥ ζ_β^{(M+1)N}`".  The step between is invariance under the
`(M+1)N`-step kernel: `μ̃^β (L) = ∑_v μ̃^β (v) P (Ũ_{(M+1)N}^{β,v} ∈ L)`, and from every state of
`S` the greedy run, which lands in `L` by Proposition 7, has probability at least
`ζ_β^{(M+1)N}` by Proposition 8. -/
theorem zeta_pow_le_measure_ladderSet (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {μ : Measure (Pressure N M)} [IsProbabilityMeasure μ] (hμS : IsCarriedByState μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) :
    ENNReal.ofReal (zeta N M β) ^ ((M + 1) * N) ≤ μ (ladderSet N M) := by
  have hn := invariant_iterateKernel (skeletonKernel β) hinv ((M + 1) * N)
  have hae : ∀ᵐ v ∂μ, v ∉ (stateSet N M)ᶜ := measure_eq_zero_iff_ae_notMem.1 hμS
  calc ENNReal.ofReal (zeta N M β) ^ ((M + 1) * N)
      = ∫⁻ _v, ENNReal.ofReal (zeta N M β) ^ ((M + 1) * N) ∂μ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ v, iterateKernel (skeletonKernel β) ((M + 1) * N) v (ladderSet N M) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with v hv
        have hvS : IsState v := by simpa using hv
        rw [iterateKernel_skeletonKernel]
        exact (zeta_pow_le_pathMeasure_greedyEvents hM hβ _).trans
          (measure_mono (greedyEvents_subset_ladder hM hN hvS))
    _ = (μ.bind (iterateKernel (skeletonKernel β) ((M + 1) * N))) (ladderSet N M) :=
        (Measure.bind_apply (measurableSet_pressure _) (Kernel.aemeasurable _)).symm
    _ = μ (ladderSet N M) := by
        rw [show μ.bind (iterateKernel (skeletonKernel β) ((M + 1) * N)) = μ from hn]

/-- **Theorem 2.1.** There is a constant `C > 0` such that for every `β ≥ 0` the invariant
probability measure satisfies `μ^β (L) ≥ 1 - C e^{-β/(M-1)}`.

**Follows the paper's proof of Theorem 2.1** (pp. 20–21).  Equation (13) writes `μ^β` as
`μ̃^β / q_β` normalised, so `μ^β (L) = A / (A + B)` with `A` the sum over `L` and `B` the sum
off it.  On `L` the rate is at most `MN e^{β(N-1)}` and `μ̃^β (L) ≥ ζ_β^{(M+1)N}` by
Propositions 7 and 8, which bounds `A` below.  Off `L`, a state whose entries are below `N` is
off `L̂`, so Proposition 9 (with `q_β ≥ e^{β/(M-1)}` off `0`) and Corollary 10 (at `0`) bound its
term by `C'' e^{-β(N-1+1/(M-1))}`, and there are at most `K(N, M)` such states; a state with an
entry of at least `N` has `q_β ≥ e^{βN}`.  The paper's last step, `1/(1+x) ≥ 1 - x`, is taken on
the complement, as `μ^β (Lᶜ) = B/(A+B) ≤ B/A`; it is the same inequality.

**Supplies the steps the paper asserts**, each marked at its declaration above: the bound on the
rate over `L`, the invariance step behind `μ̃^β (L) ≥ ζ_β^{(M+1)N}`, that a state off `L` with
entries below `N` is off `L̂`, and that there are finitely many of them.

**One constant is changed.**  The paper bounds `ζ_β^{(M+1)N} ≥ (MN)^{-(M+1)N}`, which fails at
`β = 0`, where `ζ_0 = 1/(1 + MN)`.  The bound used is `ζ_β ≥ 1/(1 + MN)`, true for every
`β ≥ 0`; only the value of `C` changes.  At `β = 0` itself, where Proposition 9 and Corollary 10
are not stated, the inequality holds because `C ≥ 1`.

**Rests on** Propositions 7 and 9 and Corollary 10, and so on Lemma 20. -/
theorem measure_ladderSet_ge (hM : 2 ≤ M) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ μ : Measure (Pressure N M),
      IsProbabilityMeasure μ → IsCarriedByState μ → IsInvariantCts β μ →
        ENNReal.ofReal (1 - C * Real.exp (-β / ((M : ℝ) - 1))) ≤ μ (ladderSet N M) := by
  classical
  -- The constants, none of which depends on `β`.
  set n : ℕ := (M + 1) * N
  set F : Set (Pressure N M) := boundedSet N M (greedyBound N M)
  have hFfin : F.Finite := boundedSet_finite _
  set K : ℕ := hFfin.toFinset.card
  set mn : ℝ := ((M * N : ℕ) : ℝ) with hmn
  set C'' : ℝ := ((N * M : ℕ) : ℝ) ^ (n + 2)
  set C : ℝ := mn * (1 + mn) ^ n * ((K : ℝ) * C'' + 1) with hC
  have hNM1 : (1 : ℝ) ≤ ((N * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne M))
  have hmn1 : 1 ≤ mn := by
    rw [hmn]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne N))
  have hC''0 : 0 ≤ C'' := by positivity
  have hC1 : 1 ≤ C := by
    have h1 : 1 ≤ (1 + mn) ^ n := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ (K : ℝ) * C'' + 1 := by
      have : 0 ≤ (K : ℝ) * C'' := by positivity
      linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ mn * (1 + mn) ^ n * ((K : ℝ) * C'' + 1) := by
        gcongr
  refine ⟨C, by linarith, fun β hβ μ hμ hμS hμinv => ?_⟩
  have := hμ
  rcases hβ.eq_or_lt with hβ0 | hβpos
  · -- At `β = 0` the bound says nothing, since `C ≥ 1`.
    subst hβ0
    have h : 1 - C * Real.exp (-0 / ((M : ℝ) - 1)) ≤ 0 := by
      rw [neg_zero, zero_div, Real.exp_zero, mul_one]
      linarith
    rw [ENNReal.ofReal_of_nonpos h]
    exact zero_le
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  obtain ⟨μs, ⟨hsprob, hsS, hsinv⟩, -⟩ := existsUnique_invariantSkeleton (N := N) (M := M) hM hβ
  have := hsprob
  set y : ℝ := Real.exp (β * ((N : ℝ) - 1)) with hy
  set z : ℝ := Real.exp (β / ((M : ℝ) - 1)) with hz
  have hy0 : 0 < y := Real.exp_pos _
  have hz0 : 0 < z := Real.exp_pos _
  have hz1 : 1 ≤ z := Real.one_le_exp (div_nonneg hβ hM1.le)
  set L : Set (Pressure N M) := ladderSet N M
  -- The terms `μ̃^β (u) / q_β (u)` of equation (13), and their sums on and off `L`.
  obtain ⟨w, hw⟩ : ∃ w : Pressure N M → ℝ≥0∞,
      w = fun v => μs {v} / ENNReal.ofReal (totalRate β v) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = ∑' v, L.indicator w v := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = ∑' v, Lᶜ.indicator w v := ⟨_, rfl⟩
  -- Equation (13).
  have h13 : ∀ v, μ {v} = w v / (A + B) := by
    intro v
    rw [invariantCts_eq_of_invariantSkeleton hM hN hβ hμ hμS hμinv hsprob hsS hsinv v, hA, hB,
      ← ENNReal.tsum_add, hw]
    congr 1
    exact tsum_congr fun v => (Set.indicator_self_add_compl_apply L
      (fun v => μs {v} / ENNReal.ofReal (totalRate β v)) v).symm
  -- `μ^β (Lᶜ) = B / (A + B) ≤ B / A`.
  have hLc : μ Lᶜ ≤ B / A := by
    have hsum : ∑' v, Lᶜ.indicator (fun v => μ {v}) v
        = (∑' v, Lᶜ.indicator w v) * (A + B)⁻¹ := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun v => ?_
      by_cases hv : v ∈ Lᶜ
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, h13 v, div_eq_mul_inv]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, zero_mul]
    rw [← Measure.tsum_indicator_apply_singleton μ Lᶜ (measurableSet_pressure _), hsum, ← hB,
      ← div_eq_mul_inv]
    exact ENNReal.div_le_div_left le_self_add B
  -- The sum over `L`: the rate there is at most `MN e^{β(N-1)}`, and `μ̃^β (L) ≥ ζ_β^{(M+1)N}`.
  have hζ0 : 1 / (1 + mn) ≤ zeta N M β := by
    have hmn' : mn = (M : ℝ) * (N : ℝ) := by rw [hmn]; push_cast; ring
    rw [zeta, ← hz, ← hmn', div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hμsL : ENNReal.ofReal ((1 / (1 + mn)) ^ n) ≤ μs L := by
    rw [ENNReal.ofReal_pow (by positivity)]
    exact (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hζ0) n).trans
      (zeta_pow_le_measure_ladderSet hM hN hβ hsS hsinv)
  have hAlow : ENNReal.ofReal ((1 / (1 + mn)) ^ n / (mn * y)) ≤ A := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    refine (ENNReal.div_le_div_right hμsL _).trans ?_
    rw [← Measure.tsum_indicator_apply_singleton μs L (measurableSet_pressure _), div_eq_mul_inv,
      ← ENNReal.tsum_mul_right, hA]
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv : v ∈ L
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, hw, ← div_eq_mul_inv]
      exact ENNReal.div_le_div_left
        (ENNReal.ofReal_le_ofReal (totalRate_le_of_mem_ladderSet hM hβ hv)) _
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, zero_mul]
  -- The sum off `L`, split by the size of the largest entry.
  have hpt : ∀ v, Lᶜ.indicator w v
      ≤ F.indicator (fun _ => ENNReal.ofReal (C'' / (y * z))) v
        + μs {v} * ENNReal.ofReal (1 / (y * z)) := by
    intro v
    by_cases hvL : v ∈ L
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hvL)]
      exact zero_le
    rw [Set.indicator_of_mem (Set.mem_compl hvL), hw]
    beta_reduce
    by_cases hvS : IsState v
    swap
    · -- Off `S`, `μ̃^β` puts no mass.
      have h0 : μs {v} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.2 (by simpa using hvS)) hsS
      rw [h0, ENNReal.zero_div]
      exact zero_le
    by_cases hbig : ∃ a p, (N : ℤ) * ((M : ℤ) - 1) ≤ v a p
    · -- An entry of at least `N`: the rate is at least `e^{βN}`.
      obtain ⟨a, p, hap⟩ := hbig
      have hqv : ENNReal.ofReal (y * z) ≤ ENNReal.ofReal (totalRate β v) :=
        ENNReal.ofReal_le_ofReal (exp_mul_exp_le_totalRate hM hβ hap)
      refine le_trans ?_ le_add_self
      rw [one_div, ENNReal.ofReal_inv_of_pos (mul_pos hy0 hz0), div_eq_mul_inv]
      exact mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 hqv)
    simp only [not_exists, not_le] at hbig
    -- Entries below `N`: the state is off `L̂`, and in the finite set `F`.
    have hvF : v ∈ F := hvS.mem_boundedSet_of_lt hM hbig
    have hvhat : v ∉ steepLadderSet N M := notMem_steepLadderSet_of_lt hM hvL hbig
    refine le_trans ?_ le_self_add
    rw [Set.indicator_of_mem hvF]
    by_cases hv0 : v = 0
    · -- Corollary 10, and `q_β (0) = MN ≥ 1`.
      subst hv0
      have h10 := measure_zero_le hM hN hβpos hsprob hsinv
      have hexp : Real.exp (-β * ((N : ℝ) - 1 + 1 / ((M : ℝ) - 1))) = 1 / (y * z) := by
        rw [hy, hz, ← Real.exp_add, one_div (Real.exp _), ← Real.exp_neg]
        congr 1
        ring
      rw [hexp, mul_one_div] at h10
      have hq1 : 1 ≤ ENNReal.ofReal (totalRate β (0 : Pressure N M)) := by
        rw [totalRate_zero]
        exact ENNReal.one_le_ofReal.2 hmn1
      exact (ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' hq1)).trans h10
    · -- Proposition 9, and `q_β ≥ e^{β/(M-1)}` off `0`.
      have h9 := measure_le_of_notMem_steepLadderSet hM hN hβpos hsprob hsinv hvS hvhat
      have hexp : Real.exp (-β * ((N : ℝ) - 1)) = 1 / y := by
        rw [hy, one_div (Real.exp _), ← Real.exp_neg]
        congr 1
        ring
      rw [hexp] at h9
      have hqv : ENNReal.ofReal z ≤ ENNReal.ofReal (totalRate β v) :=
        ENNReal.ofReal_le_ofReal (exp_le_totalRate hM hβ hvS hv0)
      calc μs {v} / ENNReal.ofReal (totalRate β v)
          ≤ ENNReal.ofReal (((N * M : ℕ) : ℝ) ^ (n + 1) * (1 / y)) / ENNReal.ofReal z :=
            ENNReal.div_le_div h9 hqv
        _ = ENNReal.ofReal (((N * M : ℕ) : ℝ) ^ (n + 1) * (1 / y) / z) :=
            (ENNReal.ofReal_div_of_pos hz0).symm
        _ ≤ ENNReal.ofReal (C'' / (y * z)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hpow : ((N * M : ℕ) : ℝ) ^ (n + 1) ≤ C'' :=
              pow_le_pow_right₀ hNM1 (by omega)
            rw [mul_one_div, div_div]
            exact div_le_div_of_nonneg_right hpow (by positivity)
  have hBup : B ≤ ENNReal.ofReal (((K : ℝ) * C'' + 1) / (y * z)) := by
    calc B ≤ ∑' v, (F.indicator (fun _ => ENNReal.ofReal (C'' / (y * z))) v
            + μs {v} * ENNReal.ofReal (1 / (y * z))) := by
          rw [hB]
          exact ENNReal.tsum_le_tsum hpt
      _ = K * ENNReal.ofReal (C'' / (y * z)) + ENNReal.ofReal (1 / (y * z)) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_measure_singleton μs, one_mul,
            tsum_eq_sum (s := hFfin.toFinset)
              (fun v hv => Set.indicator_of_notMem (by simpa using hv) _),
            Finset.sum_congr rfl fun v hv =>
              Set.indicator_of_mem ((Set.Finite.mem_toFinset hFfin).1 hv) _,
            Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((K : ℝ) * C'' + 1) / (y * z)) := by
          rw [add_div, ENNReal.ofReal_add (by positivity) (by positivity), mul_div_assoc,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  -- Putting the two together.
  have hfinal : μ Lᶜ ≤ ENNReal.ofReal (C * Real.exp (-β / ((M : ℝ) - 1))) := by
    calc μ Lᶜ ≤ B / A := hLc
      _ ≤ ENNReal.ofReal (((K : ℝ) * C'' + 1) / (y * z))
            / ENNReal.ofReal ((1 / (1 + mn)) ^ n / (mn * y)) := ENNReal.div_le_div hBup hAlow
      _ = ENNReal.ofReal ((((K : ℝ) * C'' + 1) / (y * z)) / ((1 / (1 + mn)) ^ n / (mn * y))) :=
          (ENNReal.ofReal_div_of_pos (by positivity)).symm
      _ = ENNReal.ofReal (C * Real.exp (-β / ((M : ℝ) - 1))) := by
          congr 1
          rw [neg_div, Real.exp_neg, ← hz, hC, one_div_pow]
          field_simp
  have hcompl := prob_compl_eq_one_sub (μ := μ) (measurableSet_pressure Lᶜ)
  rw [compl_compl] at hcompl
  rw [hcompl, ENNReal.ofReal_sub _ (mul_nonneg (by linarith) (Real.exp_pos _).le),
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left hfinal 1

end Theorem21

end SocialNetwork
