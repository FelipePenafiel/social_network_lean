/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.ContinuousTime
import SocialNetwork.Favouring
import SocialNetwork.Greedy

/-!
# Appendix A: Proposition 7, and the bound of Remark 5

Appendix A of arXiv:2607.19651 proves Proposition 7 in three moves:

1. **Lemma 19** takes an arbitrary state of `S` to the set `⋃_o S^o` of Definition 5, at the
   first repeat time `τ (u) ≤ N + 1`;
2. **Lemma 20** takes a state of `S^o` to the consensus set `C^o`, in
   `(M-1) (n(u) + 1) - 1 ≤ (M-1) N` further steps;
3. a final step takes `C^o` to a ladder `L^o` in `N` further steps.

The third is `SocialNetwork.isLadder_state`, proved.  The first two are stated here and are
**not** proved: the blueprint records, in the section "Two points in Appendix A that the
formalisation has to fill in", exactly where the written proofs fail to compose, and what
repairs appear to work.  Both repairs change the written arguments rather than their
presentation, so they are recorded rather than guessed at.

This file also proves the bound `η` of Remark 5, in both halves: the deterministic one —
expressing a pair that carries positive pressure keeps a steep ladder steep — and the
probabilistic one, that such a pair is expressed with probability at least `η`.  What is still
unproved is only the *iterate* `η^m`, which needs the conditioning of Proposition 8 again.

## Main definitions

* `SocialNetwork.favouringSet` — `⋃_{o ∈ O} S^o`, the target of Lemma 19.
* `SocialNetwork.consensusUnion` — `⋃_{o ∈ O} C^o`, the target of Lemma 20.
* `SocialNetwork.eta` — the constant `η` of Remark 5.
* `SocialNetwork.positivePressureEvent` — the event `{U_0 (A₁, O₁) > 0}` of Remark 5.

## Main statements

* `SocialNetwork.isFavouring_state_firstRepeat` — **Lemma 19**, unproved.
* `SocialNetwork.isConsensus_state_of_favouring` — **Lemma 20**, unproved.
* `SocialNetwork.isLadder_state_of_greedy` — **Proposition 7**, unproved.
* `SocialNetwork.mem_steepLadderSet_of_positivePressure` — the deterministic half of
  Remark 5, proved.
* `SocialNetwork.eta_le_pathMeasure_positivePressure` — the bound `η` of Remark 5, proved.
* `SocialNetwork.sum_Ico_exp_le_sum_jumpRate` — the comparison it rests on: the worst case
  over `L̂` is attained on `L`.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The unions of Definition 5 and Definition 2 -/

section Sets

/-- `⋃_{o ∈ O} S^o`, the set that Lemma 19 lands in. -/
def favouringSet (N M : ℕ) : Set (Pressure N M) := {v | ∃ o, IsFavouring o v}

/-- `⋃_{o ∈ O} C^o`, the set that Lemma 20 lands in. -/
def consensusUnion (N M : ℕ) : Set (Pressure N M) := {v | ∃ o, IsConsensus o v}

@[simp]
theorem mem_favouringSet {v : Pressure N M} : v ∈ favouringSet N M ↔ ∃ o, IsFavouring o v :=
  Iff.rfl

@[simp]
theorem mem_consensusUnion {v : Pressure N M} : v ∈ consensusUnion N M ↔ ∃ o, IsConsensus o v :=
  Iff.rfl

theorem ladderSet_subset_consensusUnion (hM : 2 ≤ M) (hN : 2 ≤ N) :
    ladderSet N M ⊆ consensusUnion N M :=
  fun _ ⟨o, hu⟩ => ⟨o, hu.isConsensus hM hN⟩

end Sets

/-! ### Lemma 19 -/

section Lemma19

variable (T : Trajectory N M) {u : Pressure N M}

/-- **Lemma 19.**  For any initial matrix `u ∈ S`, the event `ξ^u_{τ(u)}` implies that
`Ũ_{τ(u)}^{β,u} ∈ ⋃_{o ∈ O} S^o`.

Recall the index convention of `SocialNetwork.Trajectory`: `firstRepeat T` is the paper's
`τ (u) - 1`, and `IsGreedyAt T u k` is the paper's `ξ_{k+1}^u`.  So the hypothesis below is
`ξ_{τ(u)}^u` and the conclusion is about `Ũ_{τ(u)}`.

**Unproved.**  The written proof asserts, "by (25)", a sequence of `⌊m⌋ + 1` distinct actors
without giving the construction, and rules out the degenerate case `m = 0` through
`τ (u) = 2` rather than through `m = 0` itself.  The blueprint gives a construction that
works — a first-passage decomposition of the backward walk — and the corrected case split. -/
theorem isFavouring_state_firstRepeat (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u)
    (hgreedy : IsGreedyAt T u (firstRepeat T)) :
    T.state u (firstRepeat T + 1) ∈ favouringSet N M := by
  sorry

end Lemma19

/-! ### Lemma 20 -/

section Lemma20

variable (T : Trajectory N M) {o : Opinion M} {u : Pressure N M}

/-- **Lemma 20.**  For any matrix `u ∈ S^o` with witness `n (u)`, the event
`⋂_{j=1}^{(M-1)(n(u)+1)-1} ξ_j^u` implies `Ũ_{(M-1)(n(u)+1)-1}^{β,u} ∈ C^o`.

**Unproved.**  The induction invariant of the written proof,
`Ũₖ (a, p) ≤ n(u) + r - (k+1)/(M-1)` for `p ≠ o`, is not preserved: the actor that expresses
at step `k` has its row reset to `0`, and at the terminal `k` the bound is negative.  The
blueprint gives the repaired invariant, `max (0, n(u) + r - (k+1)/(M-1))`, together with the
staircase mechanism that replenishes the witnesses. -/
theorem isConsensus_state_of_favouring (hM : 2 ≤ M) (hN : 3 ≤ N) {n : ℕ} {ρ : ℤ}
    {a : Fin n → Actor N} (hu : IsFavouringWith o u n ρ a)
    (hgreedy : ∀ k < (M - 1) * (n + 1) - 1, IsGreedyAt T u k) :
    IsConsensus o (T.state u ((M - 1) * (n + 1) - 1)) := by
  sorry

end Lemma20

/-! ### Proposition 7 -/

section Proposition7

variable (T : Trajectory N M) {u : Pressure N M}

/-- **Proposition 7.**  For any initial matrix `u ∈ S`,

```
⋂_{j=1}^{(M+1)N} ξ_j^u   ⊆   {U_{T_{(M+1)N}}^{β,u} ∈ L}.
```

The three stages are Lemma 19 (which needs `τ (u) ≤ N + 1` steps), Lemma 20 (which needs
`(M-1)(n(u)+1) - 1 ≤ (M-1) N` further steps, since `n (u) ≤ N - 1`), and the final step
`SocialNetwork.isLadder_state` (`N` further steps).  The total is `(M+1) N`.

**Unproved**, because Lemmas 19 and 20 are. -/
theorem isLadder_state_of_greedy (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u)
    (hgreedy : ∀ k < (M + 1) * N, IsGreedyAt T u k) :
    T.state u ((M + 1) * N) ∈ ladderSet N M := by
  sorry

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
/-- **Proposition 7**, as an inclusion of events on the sample space of the skeleton. -/
theorem greedyEvents_subset_ladder (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u) :
    greedyEvents u ((M + 1) * N)
      ⊆ {ω : ℕ → Jump N M | skeleton u ((M + 1) * N) ω ∈ ladderSet N M} :=
  fun _ hω => isLadder_state_of_greedy _ hM hN hu fun k hk => hω k hk

/-- Proposition 7 combined with Proposition 8 and Remark 4: after `(M+1) N` expressions the
skeleton is on a ladder, except on an event of probability at most
`(M+1) N · M N · e^{-β/(M-1)}`.

This is the shape in which Theorem 2 uses the two propositions together. -/
theorem one_sub_le_pathMeasure_ladder (hM : 2 ≤ M) (hN : 3 ≤ N) (hu : IsState u) {β : ℝ}
    (hβ : 0 ≤ β) :
    ENNReal.ofReal
        (1 - (((M + 1) * N : ℕ) : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))))
      ≤ pathMeasure β u {ω : ℕ → Jump N M | skeleton u ((M + 1) * N) ω ∈ ladderSet N M} :=
  le_trans (one_sub_le_pathMeasure_greedyEvents hM hβ ((M + 1) * N))
    (measure_mono (greedyEvents_subset_ladder hM hN hu))

end Proposition7

/-! ### Remark 5 -/

section Remark5

/-- The constant `η` of Remark 5:

```
η = (∑_{j=1}^{N-1} e^{βj}) / (∑_{j=0}^{N-1} e^{βj} + MN).
```

On a ladder, the `N` pressures for the supported opinion are `0, 1, …, N-1`, so the numerator
collects the rates of the `N - 1` actors carrying strictly positive pressure, and the
denominator bounds the total rate: the remaining entries are non-positive, hence have rate at
most `1`, and there are at most `MN` of them. -/
noncomputable def eta (N M : ℕ) (β : ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))) /
    ((∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ))) + ((M * N : ℕ) : ℝ))

theorem eta_nonneg (N M : ℕ) {β : ℝ} : 0 ≤ eta N M β := by
  refine div_nonneg (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) ?_
  exact add_nonneg (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) (Nat.cast_nonneg _)

/-- The denominator of `η` is `1` more than its numerator: `∑_{j=0}^{N-1} e^{βj}` is
`e^0 = 1` plus `∑_{j=1}^{N-1} e^{βj}`. -/
theorem sum_range_eq_one_add_sum_Ico (hN : 1 ≤ N) (β : ℝ) :
    (∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ)))
      = 1 + ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N)]
  simp

/-- A monotone function summed over a finite set of naturals all at least `m` is at least its
sum over `m, m+1, …, m + #s - 1`.

**No counterpart in the paper**, and a Mathlib gap of the same kind as
`SocialNetwork.Bias.sum_range_card_le_sum`, which is the case `m = 0`, `f = id`.  The proof is
the same: induction on the largest element.  Adjoining a new maximum `a` to `s` adds `f a` to
the sum and `f (m + #s)` to the bound, and `m + #s ≤ a` because `s ⊆ Ico m a`. -/
theorem sum_range_add_le_sum {f : ℕ → ℝ} (hf : Monotone f) (m : ℕ) :
    ∀ s : Finset ℕ, (∀ x ∈ s, m ≤ x) →
      ∑ i ∈ Finset.range s.card, f (m + i) ≤ ∑ x ∈ s, f x := by
  intro s
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hs
      have hmem : a ∉ s := fun h => lt_irrefl a (ha a h)
      have hma : m ≤ a := hs a (Finset.mem_insert_self a s)
      have hsub : ∀ x ∈ s, m ≤ x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hcard : m + s.card ≤ a := by
        have h1 : s ⊆ Finset.Ico m a := fun x hx => Finset.mem_Ico.2 ⟨hsub x hx, ha x hx⟩
        have h2 := Finset.card_le_card h1
        rw [Nat.card_Ico] at h2
        omega
      rw [Finset.card_insert_of_notMem hmem, Finset.sum_insert hmem, Finset.sum_range_succ]
      have hih := ih hsub
      have hfa : f (m + s.card) ≤ f a := hf hcard
      linarith

/-- The elementary inequality behind `η`: if the pairs carrying positive pressure have total
rate at least `∑_{j=1}^{N-1} e^{βj}` and the remaining pairs at most `MN`, then the first carry
at least the fraction `η` of the total rate.  This is `SocialNetwork.zeta_le_div_of_le` for
Remark 5. -/
theorem eta_le_div_of_le (N M : ℕ) {β S T : ℝ}
    (hA : 0 < ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)))
    (hAS : (∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))) ≤ S)
    (hT0 : 0 ≤ T) (hT : T ≤ ((M * N : ℕ) : ℝ))
    (hden : (∑ j ∈ Finset.range N, Real.exp (β * (j : ℝ)))
      = 1 + ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))) :
    eta N M β ≤ S / (S + T) := by
  have hS : 0 < S := lt_of_lt_of_le hA hAS
  have hST : 0 < S + T := by linarith
  have hMN : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold eta
  rw [hden, div_le_div_iff₀ (by linarith) hST]
  nlinarith [mul_le_mul_of_nonneg_right hAS hT0, mul_le_mul_of_nonneg_left hT hS.le]

variable [NeZero N] [NeZero M]

/-- The event `{U_0^{β,u} (A₁, O₁) > 0}` of Remark 5: the first expressed pair carries
strictly positive social pressure. -/
def positivePressureEvent (u : Pressure N M) : Set (ℕ → Jump N M) :=
  {ω | 0 < u (ω 0).1 (ω 0).2}

theorem measurableSet_positivePressureEvent (u : Pressure N M) :
    MeasurableSet (positivePressureEvent u) := by
  have h : positivePressureEvent u
      = (fun ω : ℕ → Jump N M => ω 0) ⁻¹' {p : Jump N M | 0 < u p.1 p.2} := rfl
  rw [h]
  exact MeasurableSet.preimage MeasurableSet.of_discrete (measurable_pi_apply 0)

omit [NeZero N] [NeZero M] in
/-- **The deterministic half of Remark 5**: from a steep ladder, an expression by a pair that
carries strictly positive pressure lands on a steep ladder again,

```
{U_0^{β,l̂} (A₁, O₁) > 0} ⊆ {U_{T_1}^{β,l̂} ∈ L̂}.
```

This is `SocialNetwork.IsSteepLadder.express_of_pos` read on the sample space. -/
theorem mem_steepLadderSet_of_positivePressure (hM : 2 ≤ M) {o : Opinion M}
    {l : Pressure N M} (hl : IsSteepLadder o l) :
    positivePressureEvent l ⊆ {ω : ℕ → Jump N M | skeleton l 1 ω ∈ steepLadderSet N M} := by
  intro ω hω
  refine ⟨o, ?_⟩
  have hstate : skeleton l 1 ω = express (ω 0).1 (ω 0).2 l := by
    rw [skeleton, Trajectory.state_succ, Trajectory.state_zero]
    rfl
  rw [hstate]
  exact hl.express_of_pos hM hω

/-- `Y⁺ (v) = {(a, p) ∈ A × O : v (a, p) > 0}`, the pairs carrying strictly positive social
pressure: the pairs whose expression Remark 5 keeps on a steep ladder. -/
def posFinset (v : Pressure N M) : Finset (Jump N M) :=
  Finset.univ.filter fun p => 0 < v p.1 p.2

omit [NeZero N] [NeZero M] in
theorem mem_posFinset {v : Pressure N M} {p : Jump N M} :
    p ∈ posFinset v ↔ 0 < v p.1 p.2 := by simp [posFinset]

omit [NeZero N] [NeZero M] in
theorem positivePressureEvent_eq_preimage (l : Pressure N M) :
    positivePressureEvent l
      = (fun ω : ℕ → Jump N M => ω 0) ⁻¹' (posFinset l : Set (Jump N M)) := by
  ext ω
  simp [positivePressureEvent, posFinset]

omit [NeZero N] [NeZero M] in
/-- On a steep ladder the pairs carrying positive pressure have total rate at least
`∑_{j=1}^{N-1} e^{βj}`.

**This is the comparison Remark 5 makes**: the worst case over `L̂` is attained on `L`.  On a
steep ladder the `o`-column is `N` pairwise distinct non-negative integers, one of them `0`, so
the `N-1` positive ones are `N-1` distinct integers `≥ 1`; being distinct, they dominate
`1, 2, …, N-1` term by term once sorted, and `j ↦ e^{βj}` is increasing.  On a ladder they are
exactly `1, …, N-1`, which is the worst case.  Every other entry is non-positive, by the
`other` field of Definition 4, so it contributes nothing to this sum. -/
theorem sum_Ico_exp_le_sum_jumpRate (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ))
      ≤ ∑ p ∈ posFinset l, jumpRate β l p.1 p.2 := by
  have hMZ : (0 : ℤ) < (M : ℤ) - 1 := one_lt_of_two_le hM
  have hMR : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  -- the `o`-column in the unscaled coordinates of the paper: `l (a, o) = (M-1) c a`
  have hexists : ∀ a : Actor N, ∃ k : ℕ, l a o = ((M : ℤ) - 1) * (k : ℤ) := by
    intro a
    obtain ⟨k, hk⟩ := hl.dvd a
    have h0 : (0 : ℤ) ≤ ((M : ℤ) - 1) * k := hk ▸ hl.nonneg a
    have hknn : 0 ≤ k := by nlinarith
    exact ⟨k.toNat, by rw [hk, Int.toNat_of_nonneg hknn]⟩
  choose c hc using hexists
  have hcinj : Function.Injective c := fun a b hab =>
    hl.injective (show l a o = l b o by rw [hc a, hc b, hab])
  have hrate : ∀ a : Actor N, jumpRate β l a o = Real.exp (β * (c a : ℝ)) := by
    intro a
    have hcast : ((l a o : ℤ) : ℝ) = ((M : ℝ) - 1) * (c a : ℝ) := by
      rw [hc a]; push_cast; ring
    unfold jumpRate
    rw [hcast]
    congr 1
    rw [div_eq_iff (ne_of_gt hMR)]
    ring
  -- the positive pairs are the actors off the bottom of the `o`-column
  obtain ⟨a₀, ha₀⟩ := hl.exists_zero
  have hpaeq : (Finset.univ.filter fun a : Actor N => 0 < l a o) = Finset.univ.erase a₀ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro hpos hcon
      rw [hcon, ha₀] at hpos
      exact lt_irrefl 0 hpos
    · intro hne
      rcases lt_or_eq_of_le (hl.nonneg a) with hlt | heq
      · exact hlt
      · exact absurd (hl.injective (show l a o = l a₀ o by rw [← heq, ha₀])) hne
  have hcard : (Finset.univ.filter fun a : Actor N => 0 < l a o).card = N - 1 := by
    rw [hpaeq, Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ,
      Fintype.card_fin]
  -- rewrite the sum over pairs as a sum over those actors
  have hposF : posFinset l
      = (Finset.univ.filter fun a : Actor N => 0 < l a o).image (fun a => (a, o)) := by
    ext p
    simp only [mem_posFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp
      have h2 : p.2 = o := hl.opinion_eq_of_pos hM hp
      exact ⟨p.1, by rw [← h2]; exact hp, by rw [← h2]⟩
    · rintro ⟨a, hapos, rfl⟩
      exact hapos
  have hstep : ∑ p ∈ posFinset l, jumpRate β l p.1 p.2
      = ∑ a ∈ Finset.univ.filter (fun a : Actor N => 0 < l a o),
          Real.exp (β * (c a : ℝ)) := by
    rw [hposF, Finset.sum_image fun a _ b _ hab => by simpa using hab]
    exact Finset.sum_congr rfl fun a _ => hrate a
  -- the values `c a` are pairwise distinct naturals, all at least `1`
  have hsum : ∑ a ∈ Finset.univ.filter (fun a : Actor N => 0 < l a o),
        Real.exp (β * (c a : ℝ))
      = ∑ x ∈ (Finset.univ.filter fun a : Actor N => 0 < l a o).image c,
        Real.exp (β * (x : ℝ)) := by
    rw [Finset.sum_image fun a _ b _ hab => hcinj hab]
  have hcardimg : ((Finset.univ.filter fun a : Actor N => 0 < l a o).image c).card = N - 1 := by
    rw [Finset.card_image_of_injective _ hcinj, hcard]
  have hge1 : ∀ x ∈ (Finset.univ.filter fun a : Actor N => 0 < l a o).image c, 1 ≤ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have hapos : 0 < l a o := (Finset.mem_filter.1 ha).2
    rcases Nat.eq_zero_or_pos (c a) with h0 | h0
    · exfalso
      have hzero : l a o = 0 := by rw [hc a, h0]; simp
      linarith
    · exact h0
  have hmono : Monotone fun j : ℕ => Real.exp (β * (j : ℝ)) := fun i j hij =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hβ)
  have hkey := sum_range_add_le_sum hmono 1 _ hge1
  rw [hcardimg] at hkey
  rw [hstep, hsum, Finset.sum_Ico_eq_sum_range]
  exact hkey

omit [NeZero N] [NeZero M] in
/-- The pairs that carry no positive pressure have total rate at most `MN`: each of them has a
non-positive entry, hence a rate at most `1`, and there are at most `MN` of them.

**Supplies a step the paper asserts**: the denominator of `η` is written down in Remark 5
without argument.  It is the same counting as in Proposition 8. -/
theorem sum_jumpRate_compl_le {β : ℝ} (hβ : 0 ≤ β) (hM : 2 ≤ M) (v : Pressure N M) :
    ∑ p ∈ Finset.univ \ posFinset v, jumpRate β v p.1 p.2 ≤ ((M * N : ℕ) : ℝ) := by
  have hMR : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hle : ∀ p ∈ Finset.univ \ posFinset v, jumpRate β v p.1 p.2 ≤ 1 := by
    intro p hp
    have hnp : v p.1 p.2 ≤ 0 :=
      not_lt.1 fun hcon => (Finset.mem_sdiff.1 hp).2 (mem_posFinset.2 hcon)
    have hcast : ((v p.1 p.2 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hnp
    have hexp : β * ((v p.1 p.2 : ℤ) : ℝ) / ((M : ℝ) - 1) ≤ 0 := by
      rw [div_le_iff₀ hMR]
      nlinarith
    calc jumpRate β v p.1 p.2 = Real.exp (β * ((v p.1 p.2 : ℤ) : ℝ) / ((M : ℝ) - 1)) := rfl
      _ ≤ Real.exp 0 := Real.exp_le_exp.2 hexp
      _ = 1 := Real.exp_zero
  have hcard : (((Finset.univ \ posFinset v).card : ℕ) : ℝ) ≤ ((M * N : ℕ) : ℝ) := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ \ posFinset v))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_comm] at h
    exact_mod_cast h
  calc ∑ p ∈ Finset.univ \ posFinset v, jumpRate β v p.1 p.2
      ≤ (Finset.univ \ posFinset v).card • (1 : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hle
    _ = (((Finset.univ \ posFinset v).card : ℕ) : ℝ) := by simp
    _ ≤ ((M * N : ℕ) : ℝ) := hcard

/-- **Remark 5**, the bound `η`, at the level of one expression: from any steep ladder the
first expressed pair carries positive pressure with probability at least `η`. -/
theorem eta_le_jumpPMF_posFinset (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ENNReal.ofReal (eta N M β) ≤ (jumpPMF β l).toMeasure (posFinset l) := by
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ posFinset l, jumpRate β l p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (jumpRate_pos β l p.1 p.2).le
  have hT0 : (0 : ℝ) ≤ ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (jumpRate_pos β l p.1 p.2).le
  have hApos : 0 < ∑ j ∈ Finset.Ico 1 N, Real.exp (β * (j : ℝ)) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _)
      ⟨1, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
  have hAS := sum_Ico_exp_le_sum_jumpRate hM hβ hl
  have hT := sum_jumpRate_compl_le hβ hM l
  have hSpos : (0 : ℝ) < ∑ p ∈ posFinset l, jumpRate β l p.1 p.2 :=
    lt_of_lt_of_le hApos hAS
  have hreal : eta N M β
      ≤ (∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
        / ((∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
          + ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2) :=
    eta_le_div_of_le N M hApos hAS hT0 hT
      (sum_range_eq_one_add_sum_Ico (N := N) (by omega) β)
  -- transport the real inequality to the Gibbs law of equation (3)
  have hw : ∀ s : Finset (Jump N M),
      (∑ p ∈ s, jumpWeight β l p) = ENNReal.ofReal (∑ p ∈ s, jumpRate β l p.1 p.2) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β l p.1 p.2).le]
    rfl
  have hsplit : (∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
      + (∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2)
      = ∑ p : Jump N M, jumpRate β l p.1 p.2 := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ _)
  have hST : (0 : ℝ) < (∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
      + ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2 := by linarith
  have htsum : (∑' q : Jump N M, jumpWeight β l q)
      = ENNReal.ofReal ((∑ p ∈ posFinset l, jumpRate β l p.1 p.2)
        + ∑ p ∈ Finset.univ \ posFinset l, jumpRate β l p.1 p.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp,
      hw Finset.univ, hsplit]
  rw [PMF.toMeasure_apply_finset]
  simp only [jumpPMF_apply]
  rw [← Finset.sum_mul, hw (posFinset l), htsum, ← ENNReal.ofReal_inv_of_pos hST,
    ← ENNReal.ofReal_mul hS0, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Remark 5**, the bound `η`: from any steep ladder the first expressed pair carries
positive pressure with probability at least `η`.

Follows the paper's argument, which is a comparison: the worst case over `L̂` is attained on
`L`, where the `N` pressures for the supported opinion are exactly `0, 1, …, N-1`.  That
comparison is `SocialNetwork.sum_Ico_exp_le_sum_jumpRate`; the denominator is
`SocialNetwork.sum_jumpRate_compl_le`, and the two are combined by the elementary inequality
`SocialNetwork.eta_le_div_of_le`.

**Supplies a step the paper asserts**: that the worst case over `L̂` is attained on `L`.  Remark
5 writes the two inequalities down in a single line and argues neither. -/
theorem eta_le_pathMeasure_positivePressure (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) :
    ENNReal.ofReal (eta N M β) ≤ pathMeasure β l (positivePressureEvent l) := by
  rw [positivePressureEvent_eq_preimage l, pathMeasure_preimage_zero]
  exact eta_le_jumpPMF_posFinset hM hN hβ hl

/-- Iterating Remark 5: from a steep ladder, the skeleton stays on `L̂` for `m` steps with
probability at least `η^m`.  This is the estimate that Proposition 9 uses to keep the process
away from a state `u ∉ L̂`. -/
theorem eta_pow_le_pathMeasure_steepLadder (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsSteepLadder o l) (m : ℕ) :
    ENNReal.ofReal (eta N M β) ^ m
      ≤ pathMeasure β l {ω : ℕ → Jump N M | ∀ k ≤ m, skeleton l k ω ∈ steepLadderSet N M} := by
  sorry

end Remark5

/-! ### Proposition 9 and Corollary 10 -/

section Proposition9

variable [NeZero N] [NeZero M]

/-- **Proposition 9.**  For any `β > 0` and any `u ∉ L̂`, the invariant measure of the
skeleton satisfies `μ̃^β (u) ≤ C' e^{-β(N-1)}`, with `C' = (NM)^{(M+1)N+1}`.

The paper's proof is Kac's lemma — `1 / μ̃^β (u) = E [R̃^{β,u} (u)]` — followed by a lower
bound on the return time built from Proposition 7 (reach `L` without visiting `u`) and
Remark 5 (stay in `L̂` afterwards).  Mathlib has no Kac lemma.

**Unproved**, and stated for an arbitrary invariant probability measure of the skeleton rather
than for a named `μ̃^β`, since its existence is itself Theorem 1.2. -/
theorem measure_le_of_notMem_steepLadderSet (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {μ : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) {u : Pressure N M}
    (hu : u ∉ steepLadderSet N M) :
    μ {u} ≤ ENNReal.ofReal
      ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 1)) * Real.exp (-β * ((N : ℝ) - 1))) := by
  sorry

/-- **Corollary 10.**  `μ̃^β (0) ≤ C'' e^{-β(N-1+1/(M-1))}` with `C'' = (NM) C'`.

The extra `1/(M-1)` in the exponent comes from the observation that the zero matrix can only
be entered from a state in which one actor has a null row and every other actor carries `-1`
on one opinion and `1/(M-1)` on the others — a state whose maximum is `1/(M-1)`.

**Unproved**, since Proposition 9 is. -/
theorem measure_zero_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 < β)
    {μ : Measure (Pressure N M)} (hμ : IsProbabilityMeasure μ)
    (hinv : Kernel.Invariant (skeletonKernel β) μ) :
    μ {(0 : Pressure N M)} ≤ ENNReal.ofReal
      ((((N * M : ℕ) : ℝ) ^ ((M + 1) * N + 2)) *
        Real.exp (-β * ((N : ℝ) - 1 + 1 / ((M : ℝ) - 1)))) := by
  sorry

end Proposition9

end SocialNetwork
