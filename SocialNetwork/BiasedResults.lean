/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedModel
import SocialNetwork.ContinuousTime
import SocialNetwork.Greedy

/-!
# Section 3 and Appendix C: the results for the biased model

The statements of arXiv:2607.19651 about the model with communication bias: Theorem 4 of
Section 3, Theorems 16, 17, 18 of Section 5.4, and Propositions 21–24, Theorem 25,
Proposition 26, Theorem 27, Lemmas 28, 29, Corollary 30 and Theorem 31 of Appendix C.

The construction mirrors `SocialNetwork.Skeleton` and `SocialNetwork.ContinuousTime`, with the
memory profile of `SocialNetwork.BiasedModel` as the state: it is countable and discrete, so
the same shortcuts apply — every subset is measurable and every function out of it is
measurable — and the chain is again driven by the expressed pairs, so a realisation determines
the profile at every time by definition.

Everything that is a definition is built; the theorems of the paper are stated and carry a
`sorry`, for the same reasons as in the unbiased case (no Doeblin criterion, no Kac lemma, no
Poisson point process in Mathlib).

## Main definitions

* `SocialNetwork.Bias.stateAfter` — the profile after `n` expressions.
* `SocialNetwork.Bias.biasedGenerator` — the generator `G̃` of equation (7).
* `SocialNetwork.Bias.biasedSkeletonKernel` — the skeleton of the biased model.
* `SocialNetwork.Bias.biasedPathMeasure` — the law of a realisation.
* `SocialNetwork.Bias.IsBiasedGreedyAt` — the event `ξ_n^{α,u}` of Proposition 17.
* `SocialNetwork.Bias.IsNearGreedyAt` — the event `ξ̃_n^{α,u}` of Remark 7, with its slack
  of `1/(2γ)`.

## Main statements

Proposition 21, Proposition 22, Proposition 23, Proposition 24, Theorem 4, Theorem 16,
Proposition 17, Proposition 18, Theorem 25, Proposition 26, Theorem 27, Lemma 28, Lemma 29,
Corollary 30, Theorem 31 — all stated, none proved.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The discrete measurable structure on profiles -/

section Measurable

instance : Countable (Memory M) :=
  Function.Injective.countable (f := Memory.count) fun a b h => by
    cases a; cases b; simpa using h

instance : MeasurableSpace (Memory M) := ⊤

instance : DiscreteMeasurableSpace (Memory M) := ⟨fun _ => trivial⟩

theorem measurableSet_profile (s : Set (Profile N M)) : MeasurableSet s :=
  MeasurableSet.of_discrete

theorem measurable_of_profile {γ : Type*} [MeasurableSpace γ] (f : Profile N M → γ) :
    Measurable f := Measurable.of_discrete

end Measurable

/-! ### Replaying a realisation -/

section Replay

/-- The profile after the first `n` expressions of a realisation, started at `u`.  This is the
biased skeleton `Ũ_n^{α,β,u}`. -/
def stateAfter (u : Profile N M) (ω : ℕ → Jump N M) : ℕ → Profile N M
  | 0 => u
  | n + 1 => Profile.express (ω n).1 (ω n).2 (stateAfter u ω n)

@[simp]
theorem stateAfter_zero (u : Profile N M) (ω : ℕ → Jump N M) : stateAfter u ω 0 = u := rfl

theorem stateAfter_succ (u : Profile N M) (ω : ℕ → Jump N M) (n : ℕ) :
    stateAfter u ω (n + 1) = Profile.express (ω n).1 (ω n).2 (stateAfter u ω n) := rfl

/-- `S^α` is preserved along any realisation: **Remark 1**, iterated. -/
theorem isBiasedState_stateAfter {u : Profile N M} (hu : IsBiasedState u) (ω : ℕ → Jump N M)
    (n : ℕ) : IsBiasedState (stateAfter u ω n) := by
  induction n with
  | zero => exact hu
  | succ n ih => exact ih.express _ _

/-- The profile after `n` expressions only depends on the first `n` expressed pairs. -/
theorem stateAfter_congr (u : Profile N M) {ω ω' : ℕ → Jump N M} :
    ∀ n : ℕ, (∀ k < n, ω k = ω' k) → stateAfter u ω n = stateAfter u ω' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [stateAfter_succ, stateAfter_succ, ih fun k hk => h k (by omega), h n (by omega)]

/-- Read a finite history `(A₁, O₁), …, (A_{n+1}, O_{n+1})` back as a realisation, by repeating
the last pair forever.  Only the entries of index `≤ n` are ever used.  This is
`SocialNetwork.Trajectory.ofHistory` without the detour through `Trajectory`, the biased chain
being driven by profiles rather than by matrices. -/
def ofHistoryPath {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) : ℕ → Jump N M :=
  fun k => h ⟨min k n, Finset.mem_Iic.2 (min_le_right k n)⟩

theorem ofHistoryPath_apply {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) {j : ℕ} (hj : j ≤ n) :
    ofHistoryPath h j = h ⟨j, Finset.mem_Iic.2 hj⟩ := by
  have hmin : (⟨min j n, Finset.mem_Iic.2 (min_le_right j n)⟩ : Finset.Iic n)
      = ⟨j, Finset.mem_Iic.2 hj⟩ := Subtype.ext (min_eq_left hj)
  simp only [ofHistoryPath, hmin]

/-- Replay a finite history, repeating its last pair forever. -/
def stateAfterHistory (u : Profile N M) {n : ℕ} (h : (i : Finset.Iic n) → Jump N M)
    (k : ℕ) : Profile N M :=
  stateAfter u (ofHistoryPath h) k

/-- Truncating a realisation to its first `n + 1` entries and reading the result back as a
realisation changes no profile up to time `n + 1`.  This is what makes the greedy events of
the biased model cylinders. -/
theorem stateAfter_ofHistoryPath_frestrictLe (u : Profile N M) (ω : ℕ → Jump N M) {n k : ℕ}
    (hk : k ≤ n + 1) :
    stateAfter u (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) k
      = stateAfter u ω k :=
  stateAfter_congr u k fun j hj => by
    rw [ofHistoryPath_apply _ (show j ≤ n by omega), Preorder.frestrictLe_apply]

end Replay

/-! ### Equation (7): the generator `G̃` -/

section Generator

/-- The jump rate `exp (β u (a, o))` of equation (7), at the profile `P`. -/
noncomputable def biasedJumpRate (γ β : ℝ) (P : Profile N M) (a : Actor N) (o : Opinion M) :
    ℝ := Real.exp (β * P.pressure γ a o)

theorem biasedJumpRate_pos (γ β : ℝ) (P : Profile N M) (a : Actor N) (o : Opinion M) :
    0 < biasedJumpRate γ β P a o := Real.exp_pos _

/-- The total jump rate out of the profile `P`. -/
noncomputable def biasedTotalRate (γ β : ℝ) (P : Profile N M) : ℝ :=
  ∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2

variable [NeZero N] [NeZero M]

theorem biasedTotalRate_pos (γ β : ℝ) (P : Profile N M) : 0 < biasedTotalRate γ β P :=
  Finset.sum_pos (fun p _ => biasedJumpRate_pos γ β P p.1 p.2) (univ_jump_nonempty N M)

end Generator

section GeneratorDef

/-- **Equation (7)**, the generator `G̃` of the biased Markov jump process:

```
G̃ f (u) = ∑_{o ∈ O} ∑_{a ∈ A} exp (β u (a, o)) [f (π_α^{a,o} (u)) - f (u)].
```
-/
noncomputable def biasedGenerator (γ β : ℝ) (f : Profile N M → ℝ) (P : Profile N M) : ℝ :=
  ∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2 * (f (Profile.express p.1 p.2 P) - f P)

@[simp]
theorem biasedGenerator_const (γ β : ℝ) (c : ℝ) (P : Profile N M) :
    biasedGenerator γ β (fun _ => c) P = 0 := by simp [biasedGenerator]

theorem biasedGenerator_eq (γ β : ℝ) (f : Profile N M → ℝ) (P : Profile N M) :
    biasedGenerator γ β f P
      = (∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2 * f (Profile.express p.1 p.2 P))
        - biasedTotalRate γ β P * f P := by
  rw [biasedGenerator, biasedTotalRate, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end GeneratorDef

/-! ### The biased skeleton -/

section Skeleton

variable [NeZero N] [NeZero M]

/-- The weight of the pair `(a, o)` at the profile `P`, as an extended non-negative real. -/
noncomputable def biasedJumpWeight (γ β : ℝ) (P : Profile N M) (p : Jump N M) : ℝ≥0∞ :=
  ENNReal.ofReal (biasedJumpRate γ β P p.1 p.2)

theorem tsum_biasedJumpWeight_ne_zero (γ β : ℝ) (P : Profile N M) :
    (∑' p : Jump N M, biasedJumpWeight γ β P p) ≠ 0 := by
  rw [Ne, ENNReal.tsum_eq_zero]
  intro h
  obtain ⟨p, -⟩ := univ_jump_nonempty N M
  exact (ENNReal.ofReal_pos.2 (biasedJumpRate_pos γ β P p.1 p.2)).ne' (h p)

theorem tsum_biasedJumpWeight_ne_top (γ β : ℝ) (P : Profile N M) :
    (∑' p : Jump N M, biasedJumpWeight γ β P p) ≠ ∞ := by
  rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp]
  exact ENNReal.sum_ne_top.2 fun p _ => ENNReal.ofReal_ne_top

/-- The law of the pair `(A_n^α, O_n^α)` given the current profile. -/
noncomputable def biasedJumpPMF (γ β : ℝ) (P : Profile N M) : PMF (Jump N M) :=
  PMF.normalize (biasedJumpWeight γ β P) (tsum_biasedJumpWeight_ne_zero γ β P)
    (tsum_biasedJumpWeight_ne_top γ β P)

theorem biasedJumpPMF_apply (γ β : ℝ) (P : Profile N M) (p : Jump N M) :
    biasedJumpPMF γ β P p
      = biasedJumpWeight γ β P p * (∑' q : Jump N M, biasedJumpWeight γ β P q)⁻¹ := rfl

/-- The transition kernel of the biased skeleton. -/
noncomputable def biasedSkeletonKernel (γ β : ℝ) : Kernel (Profile N M) (Profile N M) :=
  Kernel.ofFunOfCountable fun P =>
    ((biasedJumpPMF γ β P).map fun p => Profile.express p.1 p.2 P).toMeasure

instance isMarkovKernel_biasedSkeletonKernel (γ β : ℝ) :
    IsMarkovKernel (biasedSkeletonKernel (N := N) (M := M) γ β) :=
  ⟨fun P => by
    show IsProbabilityMeasure (PMF.toMeasure _)
    infer_instance⟩

/-- The kernel driving the biased chain by its expressed pairs. -/
noncomputable def biasedDrivingKernel (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Jump N M) (Jump N M) :=
  Kernel.ofFunOfCountable fun h => (biasedJumpPMF γ β (stateAfterHistory u h (n + 1))).toMeasure

instance isMarkovKernel_biasedDrivingKernel (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    IsMarkovKernel (biasedDrivingKernel γ β u n) :=
  ⟨fun h => by
    show IsProbabilityMeasure (PMF.toMeasure _)
    infer_instance⟩

/-- The law of a realisation `(A_n^α, O_n^α)_n` of the biased skeleton started at `u`. -/
noncomputable def biasedPathMeasure (γ β : ℝ) (u : Profile N M) : Measure (ℕ → Jump N M) :=
  Kernel.traj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) 0 ∘ₘ
    ((biasedJumpPMF γ β u).toMeasure.map toHistoryZero)

instance isProbabilityMeasure_biasedPathMeasure (γ β : ℝ) (u : Profile N M) :
    IsProbabilityMeasure (biasedPathMeasure γ β u) := by
  rw [biasedPathMeasure]
  have : IsProbabilityMeasure
      ((biasedJumpPMF γ β u).toMeasure.map (toHistoryZero (N := N) (M := M))) :=
    Measure.isProbabilityMeasure_map measurable_toHistoryZero.aemeasurable
  infer_instance

end Skeleton

/-! ### The greedy events of Proposition 17 and Remark 7 -/

section GreedyEvents

/-- The event `ξ_n^{α,u}` of Proposition 17: the `n`-th expressed pair maximises the social
pressure, exactly as in the unbiased model. -/
def IsBiasedGreedyAt (γ : ℝ) (u : Profile N M) (ω : ℕ → Jump N M) (k : ℕ) : Prop :=
  ∀ a o, (stateAfter u ω k).pressure γ a o
    ≤ (stateAfter u ω k).pressure γ (ω k).1 (ω k).2

/-- The event `ξ̃_n^{α,u}` of **Remark 7**: the `n`-th expressed pair is within `1/(2γ)` of the
maximum social pressure.

The slack is what makes a uniform lower bound on `P (ξ̃_n^{α,u})` available in the biased
model, where the entries no longer live on a lattice of mesh `1/(M-1)`. -/
def IsNearGreedyAt (γ : ℝ) (u : Profile N M) (ω : ℕ → Jump N M) (k : ℕ) : Prop :=
  ∀ a o, (stateAfter u ω k).pressure γ a o - 1 / (2 * γ)
    < (stateAfter u ω k).pressure γ (ω k).1 (ω k).2

/-- `⋂_{j=1}^{n} ξ_j^{α,u}`, as a subset of the sample space. -/
def biasedGreedyEvents (γ : ℝ) (u : Profile N M) (n : ℕ) : Set (ℕ → Jump N M) :=
  {ω | ∀ k < n, IsBiasedGreedyAt γ u ω k}

/-- `⋂_{j=1}^{n} ξ̃_j^{α,u}`, as a subset of the sample space. -/
def nearGreedyEvents (γ : ℝ) (u : Profile N M) (n : ℕ) : Set (ℕ → Jump N M) :=
  {ω | ∀ k < n, IsNearGreedyAt γ u ω k}

/-- The greedy event at step `k` only constrains the first `k + 1` expressed pairs, so reading
it off a truncated realisation gives the same answer. -/
theorem isBiasedGreedyAt_ofHistoryPath_frestrictLe (γ : ℝ) (u : Profile N M)
    (ω : ℕ → Jump N M) {n k : ℕ} (hk : k ≤ n) :
    IsBiasedGreedyAt γ u
        (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) k
      ↔ IsBiasedGreedyAt γ u ω k := by
  have hstate := stateAfter_ofHistoryPath_frestrictLe u ω (n := n) (k := k) (by omega)
  have hjump : ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω) k = ω k := by
    rw [ofHistoryPath_apply _ hk, Preorder.frestrictLe_apply]
  simp only [IsBiasedGreedyAt, hstate, hjump]

/-- The near-greedy event at step `k` only constrains the first `k + 1` expressed pairs. -/
theorem isNearGreedyAt_ofHistoryPath_frestrictLe (γ : ℝ) (u : Profile N M)
    (ω : ℕ → Jump N M) {n k : ℕ} (hk : k ≤ n) :
    IsNearGreedyAt γ u
        (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) k
      ↔ IsNearGreedyAt γ u ω k := by
  have hstate := stateAfter_ofHistoryPath_frestrictLe u ω (n := n) (k := k) (by omega)
  have hjump : ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω) k = ω k := by
    rw [ofHistoryPath_apply _ hk, Preorder.frestrictLe_apply]
  simp only [IsNearGreedyAt, hstate, hjump]

theorem biasedGreedyEvents_eq_preimage (γ : ℝ) (u : Profile N M) (n : ℕ) :
    biasedGreedyEvents γ u n =
      Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹'
        {h | ∀ k < n, IsBiasedGreedyAt γ u (ofHistoryPath h) k} := by
  ext ω
  simp only [biasedGreedyEvents, Set.mem_setOf_eq, Set.mem_preimage]
  exact ⟨fun hω k hk => (isBiasedGreedyAt_ofHistoryPath_frestrictLe γ u ω hk.le).2 (hω k hk),
    fun hω k hk => (isBiasedGreedyAt_ofHistoryPath_frestrictLe γ u ω hk.le).1 (hω k hk)⟩

theorem nearGreedyEvents_eq_preimage (γ : ℝ) (u : Profile N M) (n : ℕ) :
    nearGreedyEvents γ u n =
      Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹'
        {h | ∀ k < n, IsNearGreedyAt γ u (ofHistoryPath h) k} := by
  ext ω
  simp only [nearGreedyEvents, Set.mem_setOf_eq, Set.mem_preimage]
  exact ⟨fun hω k hk => (isNearGreedyAt_ofHistoryPath_frestrictLe γ u ω hk.le).2 (hω k hk),
    fun hω k hk => (isNearGreedyAt_ofHistoryPath_frestrictLe γ u ω hk.le).1 (hω k hk)⟩

/-- The near-greedy event constrains only the first `n` coordinates, so it is measurable.

**No counterpart in the paper**, which does not address measurability. -/
theorem measurableSet_nearGreedyEvents (γ : ℝ) (u : Profile N M) (n : ℕ) :
    MeasurableSet (nearGreedyEvents γ u n) := by
  rw [nearGreedyEvents_eq_preimage]
  exact Preorder.measurable_frestrictLe n MeasurableSet.of_discrete

/-- The greedy event constrains only the first `n` coordinates, so it is measurable.

**No counterpart in the paper**, which does not address measurability. -/
theorem measurableSet_biasedGreedyEvents (γ : ℝ) (u : Profile N M) (n : ℕ) :
    MeasurableSet (biasedGreedyEvents γ u n) := by
  rw [biasedGreedyEvents_eq_preimage]
  exact Preorder.measurable_frestrictLe n MeasurableSet.of_discrete

end GreedyEvents

/-! ### Propositions 21 to 24 -/

section Propositions

variable [NeZero N] [NeZero M]

/-- Along a realisation an actor hears at most one expression per step, so `nₐ` grows by at
most one; it is reset, not incremented, in the step where the actor expresses. -/
theorem heard_stateAfter_le (u : Profile N M) (ω : ℕ → Jump N M) (a : Actor N) (m k : ℕ) :
    (stateAfter u ω (m + k)).heard a ≤ (stateAfter u ω m).heard a + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + (k + 1) = m + k + 1 by ring, stateAfter_succ]
      by_cases ha : a = (ω (m + k)).1
      · rw [ha, Profile.heard_express_self]; omega
      · rw [Profile.heard_express_of_ne ha]; omega

/-- Expressing resets the number of expressions heard. -/
theorem heard_stateAfter_expressed (u : Profile N M) (ω : ℕ → Jump N M) (j : ℕ) :
    (stateAfter u ω (j + 1)).heard (ω j).1 = 0 := by
  rw [stateAfter_succ, Profile.heard_express_self]

/-- **Proposition 21.**  Among the first `N` expressions of the biased model, at least one
comes from an actor whose social pressure on the expressed opinion is below `N`.

The proof is that of Proposition 5, which is combinatorial and does not see the bias. -/
theorem exists_pressure_lt (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) {u : Profile N M}
    (hu : IsBiasedState u) (ω : ℕ → Jump N M) :
    ∃ k < N, ∀ o, (stateAfter u ω k).pressure γ (ω k).1 o < (N : ℝ) := by
  by_contra hcon
  push_neg at hcon
  -- every one of the first `N` expressions comes from an actor that has heard `≥ N`
  have hbig : ∀ k, k < N → N ≤ (stateAfter u ω k).heard (ω k).1 := by
    intro k hk
    obtain ⟨o, ho⟩ := hcon k hk
    have h := le_trans ho (Profile.pressure_le_heard hγ (stateAfter u ω k) (ω k).1 o)
    exact_mod_cast h
  obtain ⟨a₀, ha₀⟩ := hu.exists_zero_row
  -- the actor with the null row has heard at most `k < N` by time `k`, so never expresses
  have hne : ∀ k, k < N → (ω k).1 ≠ a₀ := by
    intro k hk hEq
    have h1 := heard_stateAfter_le u ω a₀ 0 k
    rw [Nat.zero_add, stateAfter_zero, ha₀, Nat.zero_add] at h1
    have h2 := hbig k hk
    rw [hEq] at h2
    omega
  -- an actor that expressed at step `j` has heard only `k - j - 1 < N` by step `k`
  have hpair : ∀ j k, j < k → k < N → (ω j).1 ≠ (ω k).1 := by
    intro j k hjk hk hEq
    have h0 := heard_stateAfter_expressed u ω j
    have h1 := heard_stateAfter_le u ω (ω j).1 (j + 1) (k - j - 1)
    rw [h0, Nat.zero_add, show j + 1 + (k - j - 1) = k by omega, hEq] at h1
    have h2 := hbig k hk
    omega
  -- `a₀` and the first `N` expressing actors are `N + 1` distinct actors
  have hinj : Function.Injective
      fun i : Fin (N + 1) => if (i : ℕ) < N then (ω (i : ℕ)).1 else a₀ := by
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

/-- **Proposition 22.**  On `⋂_{j=1}^{N} ξ̃_j^{α,u}`, the whole matrix is confined to
`(-MN, N)` entrywise after `N` expressions.

**Unproved, and it does not follow from Proposition 6 as Appendix C asserts.**  Proposition 6
splits on whether the first `N` expressions come from distinct actors.  The distinct case
transports unchanged.  In the repeat case, an actor expressing at steps `j < k < N` has heard
`k - j - 1` expressions at step `k`, and greediness makes its entry the maximum of the whole
matrix, so the matrix is capped at `(k - j - 1) + (N - k) = N - j - 1 ≤ N - 1`.  Under `ξ̃`
the expressed pair is only within `1/(2γ)` of the maximum, so the same chain gives
`N - 1 + 1/(2γ)`, which is below `N` only for `γ ≥ 1/2`.  In this regime
`γ = 1/(M-1) - α < 1/(M-1)`, so that fails for every `M ≥ 3`.

The statement is not obviously false: `u (a, p) ≤ n_a` makes the slack self-correcting, since
a large maximum forces an actor that has heard a lot to express, which resets it.  The
blueprint records what a proof would have to use, and what weaker constant would do instead. -/
theorem entry_mem_of_nearGreedy (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    {u : Profile N M} (hu : IsBiasedState u) :
    nearGreedyEvents γ u N ⊆
      {ω | ∀ a p, -((M : ℝ) * (N : ℝ)) < (stateAfter u ω N).pressure γ a p ∧
        (stateAfter u ω N).pressure γ a p < (N : ℝ)} := by
  sorry

/-- **Proposition 23.**  There is a horizon `C (α, M, N)` after which a run of near-greedy
expressions has taken the biased process onto a ladder `L_α`. -/
theorem exists_horizon_isBiasedLadder (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℕ, 0 < C ∧ ∀ u : Profile N M, IsBiasedState u →
      nearGreedyEvents γ u C ⊆ {ω | stateAfter u ω C ∈ biasedLadderSet N M γ} := by
  sorry

/-- The constant `ζ_{α,β} = e^{β/(2γ)} / (e^{β/(2γ)} + MN)` of Proposition 24. -/
noncomputable def biasedZeta (N M : ℕ) (γ β : ℝ) : ℝ :=
  Real.exp (β / (2 * γ)) / (Real.exp (β / (2 * γ)) + ((M * N : ℕ) : ℝ))

/-- The maximum social pressure over all pairs: the biased counterpart of
`SocialNetwork.entrySup`. -/
noncomputable def pressureSup (γ : ℝ) (P : Profile N M) : ℝ :=
  Finset.univ.sup' (univ_jump_nonempty N M) fun p : Jump N M => P.pressure γ p.1 p.2

theorem le_pressureSup (γ : ℝ) (P : Profile N M) (a : Actor N) (o : Opinion M) :
    P.pressure γ a o ≤ pressureSup γ P :=
  Finset.le_sup' (fun p : Jump N M => P.pressure γ p.1 p.2) (Finset.mem_univ (a, o))

theorem exists_pressureSup (γ : ℝ) (P : Profile N M) :
    ∃ a o, P.pressure γ a o = pressureSup γ P := by
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_mem_eq_sup' (univ_jump_nonempty N M) fun p : Jump N M => P.pressure γ p.1 p.2
  exact ⟨p.1, p.2, hp.symm⟩

/-- The pairs the near-greedy event admits: those within `1/(2γ)` of the maximum.  This is to
`ξ̃` what `SocialNetwork.argmaxFinset` is to `ξ`. -/
noncomputable def nearArgmaxFinset (γ : ℝ) (P : Profile N M) : Finset (Jump N M) :=
  Finset.univ.filter fun p => pressureSup γ P - 1 / (2 * γ) < P.pressure γ p.1 p.2

theorem mem_nearArgmaxFinset {γ : ℝ} {P : Profile N M} {p : Jump N M} :
    p ∈ nearArgmaxFinset γ P ↔ pressureSup γ P - 1 / (2 * γ) < P.pressure γ p.1 p.2 := by
  simp [nearArgmaxFinset]

/-- `Ỹ_γ (P)` is not empty: the maximising pair is in it, the slack being positive. -/
theorem nearArgmaxFinset_nonempty {γ : ℝ} (hγ : 0 < γ) (P : Profile N M) :
    (nearArgmaxFinset γ P).Nonempty := by
  obtain ⟨a, o, hao⟩ := exists_pressureSup γ P
  refine ⟨(a, o), mem_nearArgmaxFinset.2 ?_⟩
  have : (0 : ℝ) < 1 / (2 * γ) := by positivity
  simp only [hao]
  linarith

/-- The near-greedy event at step `k` says exactly that the pair expressed then lies in
`Ỹ_γ (Ũ_k^{α,u})`. -/
theorem isNearGreedyAt_iff_mem (γ : ℝ) (u : Profile N M) (ω : ℕ → Jump N M) (k : ℕ) :
    IsNearGreedyAt γ u ω k ↔ ω k ∈ nearArgmaxFinset γ (stateAfter u ω k) := by
  rw [mem_nearArgmaxFinset]
  constructor
  · intro h
    obtain ⟨a, o, hao⟩ := exists_pressureSup γ (stateAfter u ω k)
    rw [← hao]
    exact h a o
  · intro h a o
    have := le_pressureSup γ (stateAfter u ω k) a o
    linarith

/-- The elementary inequality behind Proposition 24, the twin of
`SocialNetwork.zeta_le_div_of_le` with the lattice gap `1/(M-1)` replaced by the slack
`1/(2γ)` that the event `ξ̃` carries. -/
theorem biasedZeta_le_div_of_le (N M : ℕ) (γ β : ℝ) {A S T : ℝ} (hA : 0 < A) (hAS : A ≤ S)
    (hT0 : 0 ≤ T) (hT : T ≤ ((M * N : ℕ) : ℝ) * (A * Real.exp (-(β / (2 * γ))))) :
    biasedZeta N M γ β ≤ S / (S + T) := by
  have hE : (0 : ℝ) < Real.exp (β / (2 * γ)) := Real.exp_pos _
  have hc : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := by positivity
  have hS : (0 : ℝ) < S := lt_of_lt_of_le hA hAS
  have hST : (0 : ℝ) < S + T := by linarith
  rw [Real.exp_neg] at hT
  have hinv : Real.exp (β / (2 * γ)) * (Real.exp (β / (2 * γ)))⁻¹ = 1 := mul_inv_cancel₀ hE.ne'
  have key : Real.exp (β / (2 * γ)) * T ≤ ((M * N : ℕ) : ℝ) * A := by
    calc Real.exp (β / (2 * γ)) * T
        ≤ Real.exp (β / (2 * γ)) * (((M * N : ℕ) : ℝ) * (A * (Real.exp (β / (2 * γ)))⁻¹)) :=
          mul_le_mul_of_nonneg_left hT hE.le
      _ = ((M * N : ℕ) : ℝ) * A * (Real.exp (β / (2 * γ)) * (Real.exp (β / (2 * γ)))⁻¹) := by
          ring
      _ = ((M * N : ℕ) : ℝ) * A := by rw [hinv, mul_one]
  have key2 : ((M * N : ℕ) : ℝ) * A ≤ ((M * N : ℕ) : ℝ) * S := mul_le_mul_of_nonneg_left hAS hc
  unfold biasedZeta
  rw [div_le_div_iff₀ (by linarith) hST]
  nlinarith [key, key2]

/-- **The one-step bound of Proposition 24.**  Whatever the current profile, the pair chosen at
the next expression is within `1/(2γ)` of the maximum with probability at least `ζ_{α,β}`.

**Follows the paper's proof of Proposition 8**, with the lattice gap `1/(M-1)` replaced by the
slack the event carries.  That substitution is the whole point of Remark 7: in the biased model
the entries no longer lie on a lattice, so the gap has to be put into the event by hand. -/
theorem biasedZeta_le_biasedJumpPMF_nearArgmaxFinset {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    (P : Profile N M) :
    ENNReal.ofReal (biasedZeta N M γ β)
      ≤ (biasedJumpPMF γ β P).toMeasure (nearArgmaxFinset γ P) := by
  -- a maximising pair, and the weight it carries
  obtain ⟨a₀, o₀, ha₀⟩ := exists_pressureSup γ P
  have hmaxrate : biasedJumpRate γ β P a₀ o₀ = Real.exp (β * pressureSup γ P) := by
    unfold biasedJumpRate
    rw [ha₀]
  have hp₀ : (a₀, o₀) ∈ nearArgmaxFinset γ P := by
    refine mem_nearArgmaxFinset.2 ?_
    have : (0 : ℝ) < 1 / (2 * γ) := by positivity
    simp only [ha₀]
    linarith
  -- every other pair is below the maximum by at least the slack
  have hnonmax : ∀ p ∈ Finset.univ \ nearArgmaxFinset γ P,
      biasedJumpRate γ β P p.1 p.2
        ≤ Real.exp (β * pressureSup γ P) * Real.exp (-(β / (2 * γ))) := by
    intro p hp
    have hle : P.pressure γ p.1 p.2 ≤ pressureSup γ P - 1 / (2 * γ) :=
      not_lt.1 fun hcon => (Finset.mem_sdiff.1 hp).2 (mem_nearArgmaxFinset.2 hcon)
    unfold biasedJumpRate
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : β * P.pressure γ p.1 p.2 ≤ β * (pressureSup γ P - 1 / (2 * γ)) :=
      mul_le_mul_of_nonneg_left hle hβ
    have h2 : β * (pressureSup γ P - 1 / (2 * γ))
        = β * pressureSup γ P + -(β / (2 * γ)) := by ring
    linarith [h2 ▸ h1]
  -- the two partial sums
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le
  have hT0 : (0 : ℝ) ≤ ∑ p ∈ Finset.univ \ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le
  have hAS : Real.exp (β * pressureSup γ P)
      ≤ ∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2 := by
    rw [← hmaxrate]
    exact Finset.single_le_sum (fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le) hp₀
  have hcard : (((Finset.univ \ nearArgmaxFinset γ P).card : ℕ) : ℝ) ≤ ((M * N : ℕ) : ℝ) := by
    have h := Finset.card_le_card (Finset.subset_univ (Finset.univ \ nearArgmaxFinset γ P))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_comm] at h
    exact_mod_cast h
  have hT : (∑ p ∈ Finset.univ \ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
      ≤ ((M * N : ℕ) : ℝ)
        * (Real.exp (β * pressureSup γ P) * Real.exp (-(β / (2 * γ)))) := by
    have h1 := Finset.sum_le_card_nsmul (Finset.univ \ nearArgmaxFinset γ P)
      (fun p => biasedJumpRate γ β P p.1 p.2)
      (Real.exp (β * pressureSup γ P) * Real.exp (-(β / (2 * γ)))) hnonmax
    rw [nsmul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hreal : biasedZeta N M γ β
      ≤ (∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
        / ((∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
          + ∑ p ∈ Finset.univ \ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2) :=
    biasedZeta_le_div_of_le N M γ β (Real.exp_pos _) hAS hT0 hT
  -- transport it to the measure
  have hw : ∀ s : Finset (Jump N M),
      (∑ p ∈ s, biasedJumpWeight γ β P p)
        = ENNReal.ofReal (∑ p ∈ s, biasedJumpRate γ β P p.1 p.2) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le]
    rfl
  have hsplit : (∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
      + (∑ p ∈ Finset.univ \ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
      = ∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2 := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ _)
  have hST : (0 : ℝ) < (∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
      + ∑ p ∈ Finset.univ \ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2 := by
    have hpos := Real.exp_pos (β * pressureSup γ P)
    linarith
  have htsum : (∑' q : Jump N M, biasedJumpWeight γ β P q)
      = ENNReal.ofReal ((∑ p ∈ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
        + ∑ p ∈ Finset.univ \ nearArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp,
      hw Finset.univ, hsplit]
  rw [PMF.toMeasure_apply_finset]
  simp only [biasedJumpPMF_apply]
  rw [← Finset.sum_mul, hw (nearArgmaxFinset γ P), htsum, ← ENNReal.ofReal_inv_of_pos hST,
    ← ENNReal.ofReal_mul hS0, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

theorem biasedDrivingKernel_apply (γ β : ℝ) (u : Profile N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Jump N M) :
    biasedDrivingKernel γ β u n h
      = (biasedJumpPMF γ β (stateAfterHistory u h (n + 1))).toMeasure := rfl

/-! #### The induction of Propositions 17 and 24

Both `ξ^{α,u}` and `ξ̃^{α,u}` say that the expressed pair lies in a set attached to the profile
reached at that moment, and the induction of Proposition 8 uses nothing else about them.  It is
therefore run once here, for an arbitrary such choice, and instantiated twice: at
`SocialNetwork.Bias.biasedArgmaxFinset` for Proposition 17, and at
`SocialNetwork.Bias.nearArgmaxFinset` for Proposition 24. -/

section Iterate

variable {γ β : ℝ} {u : Profile N M}

/-- The event that each of the first `m` expressed pairs lies in `S` at the profile reached
then. -/
def stepEvents (S : Profile N M → Finset (Jump N M)) (u : Profile N M) (m : ℕ) :
    Set (ℕ → Jump N M) :=
  {ω | ∀ k < m, ω k ∈ S (stateAfter u ω k)}

/-- The same event, read on histories of the first `n + 1` expressed pairs. -/
def stepHistory (S : Profile N M → Finset (Jump N M)) (u : Profile N M) (n : ℕ) :
    Set ((i : Finset.Iic n) → Jump N M) :=
  {h | ∀ k ≤ n, ofHistoryPath h k ∈ S (stateAfter u (ofHistoryPath h) k)}

theorem measurableSet_stepHistory (S : Profile N M → Finset (Jump N M)) (u : Profile N M)
    (n : ℕ) : MeasurableSet (stepHistory S u n) := MeasurableSet.of_discrete

/-- `⋂_{j=1}^{n+1}` of the event is the cylinder over `stepHistory S u n`. -/
theorem stepEvents_succ_eq_preimage (S : Profile N M → Finset (Jump N M)) (u : Profile N M)
    (n : ℕ) :
    stepEvents S u (n + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹' stepHistory S u n := by
  have key : ∀ (ω : ℕ → Jump N M) (k : ℕ), k ≤ n →
      (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω) k
        ∈ S (stateAfter u (ofHistoryPath
            (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) k)
        ↔ ω k ∈ S (stateAfter u ω k)) := by
    intro ω k hk
    rw [stateAfter_ofHistoryPath_frestrictLe u ω (by omega),
      ofHistoryPath_apply _ hk, Preorder.frestrictLe_apply]
  ext ω
  simp only [stepEvents, stepHistory, Set.mem_setOf_eq, Set.mem_preimage]
  exact ⟨fun hω k hk => (key ω k hk).2 (hω k (by omega)),
    fun hω k hk => (key ω k (by omega)).1 (hω k (by omega))⟩

theorem measurableSet_stepEvents (S : Profile N M → Finset (Jump N M)) (u : Profile N M)
    (m : ℕ) : MeasurableSet (stepEvents S u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : stepEvents S u 0 = Set.univ := by ext ω; simp [stepEvents]
    rw [h0]
    exact MeasurableSet.univ
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [stepEvents_succ_eq_preimage]
    exact Preorder.measurable_frestrictLe n (measurableSet_stepHistory S u n)

theorem ofHistoryPath_eq {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h) {j : ℕ}
    (hj : j ≤ n) : ofHistoryPath x j = ofHistoryPath h j := by
  rw [ofHistoryPath_apply _ (show j ≤ n + 1 by omega), ofHistoryPath_apply _ hj, ← hx,
    Preorder.frestrictLe₂_apply]

theorem stateAfter_ofHistoryPath_eq {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (u : Profile N M) {k : ℕ} (hk : k ≤ n + 1) :
    stateAfter u (ofHistoryPath x) k = stateAfter u (ofHistoryPath h) k :=
  stateAfter_congr u k fun j hj => ofHistoryPath_eq hx (by omega)

/-- If a history of length `n + 2` restricts to one in `stepHistory S u n` and its last
coordinate lies in `S` at the profile that history reaches, then it is in
`stepHistory S u (n + 1)`. -/
theorem mem_stepHistory_succ {S : Profile N M → Finset (Jump N M)} {n : ℕ}
    {x : (i : Finset.Iic (n + 1)) → Jump N M} {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (hh : h ∈ stepHistory S u n)
    (hlast : x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ S (stateAfterHistory u h (n + 1))) :
    x ∈ stepHistory S u (n + 1) := by
  intro k hk
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · have hkn : k ≤ n := by omega
    rw [stateAfter_ofHistoryPath_eq hx u (k := k) (by omega), ofHistoryPath_eq hx hkn]
    exact hh k hkn
  · have hkeq : k = n + 1 := le_antisymm hk hge
    subst hkeq
    rw [stateAfter_ofHistoryPath_eq hx u (k := n + 1) le_rfl,
      ofHistoryPath_apply _ (le_refl (n + 1))]
    exact hlast

/-- **The induction step**, for any one-step bound `c` that holds at every profile. -/
theorem le_partialTraj_succ {S : Profile N M → Finset (Jump N M)} {c : ℝ}
    (hone : ∀ P : Profile N M, ENNReal.ofReal c ≤ (biasedJumpPMF γ β P).toMeasure (S P))
    (n : ℕ) {h : (i : Finset.Iic n) → Jump N M} (hh : h ∈ stepHistory S u n) :
    ENNReal.ofReal c
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) n (n + 1) h
          (stepHistory S u (n + 1)) := by
  have hmapA : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (biasedDrivingKernel γ β u) n (n + 1) h).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      = Measure.dirac h := by
    rw [Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Jump N M) h
      (Nat.le_succ n), Kernel.partialTraj_self, Kernel.id_apply]
  have hAone : Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
      (biasedDrivingKernel γ β u) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h}) = 1 := by
    have hm := Measure.map_apply
      (μ := Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (biasedDrivingKernel γ β u) n (n + 1) h)
      (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      (measurableSet_singleton h)
    rw [hmapA] at hm
    rw [← hm]
    exact Measure.dirac_apply_of_mem rfl
  have hAcompl : Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
      (biasedDrivingKernel γ β u) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})ᶜ = 0 :=
    (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hAone
  have hmapB : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (biasedDrivingKernel γ β u) n (n + 1) h).map
      (fun x : (i : Finset.Iic (n + 1)) → Jump N M => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      = biasedDrivingKernel γ β u n h := by
    rw [← Kernel.map_apply _ Measurable.of_discrete, Kernel.map_partialTraj_succ_self]
  have hB : ENNReal.ofReal c
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
          (biasedDrivingKernel γ β u) n (n + 1) h
          ((fun x : (i : Finset.Iic (n + 1)) → Jump N M =>
              x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            (S (stateAfterHistory u h (n + 1)))) := by
    rw [← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete, hmapB,
      biasedDrivingKernel_apply]
    exact hone _
  exact le_measure_of_inter hAcompl hB fun x hx => mem_stepHistory_succ hx.1 hh hx.2

/-- The law of the first `n + 1` expressed pairs of the biased chain. -/
noncomputable def biasedHistoryMeasure (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    Measure ((i : Finset.Iic n) → Jump N M) :=
  Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) 0 n ∘ₘ
    ((biasedJumpPMF γ β u).toMeasure.map toHistoryZero)

theorem le_historyMeasure_zero {S : Profile N M → Finset (Jump N M)} {c : ℝ}
    (hone : ∀ P : Profile N M, ENNReal.ofReal c ≤ (biasedJumpPMF γ β P).toMeasure (S P)) :
    ENNReal.ofReal c ≤ biasedHistoryMeasure γ β u 0 (stepHistory S u 0) := by
  have hpre : toHistoryZero ⁻¹' stepHistory S u 0 = (S u : Set (Jump N M)) := by
    ext z
    have hz : ofHistoryPath (toHistoryZero z) 0 = z := rfl
    constructor
    · intro hzz
      have h0 := hzz 0 le_rfl
      rwa [hz, stateAfter_zero] at h0
    · intro hzz k hk
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      rw [hz, stateAfter_zero]
      exact hzz
  unfold biasedHistoryMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply measurable_toHistoryZero MeasurableSet.of_discrete, hpre]
  exact hone u

theorem pow_le_historyMeasure {S : Profile N M → Finset (Jump N M)} {c : ℝ}
    (hone : ∀ P : Profile N M, ENNReal.ofReal c ≤ (biasedJumpPMF γ β P).toMeasure (S P))
    (n : ℕ) :
    ENNReal.ofReal c ^ (n + 1) ≤ biasedHistoryMeasure γ β u n (stepHistory S u n) := by
  induction n with
  | zero => simpa using le_historyMeasure_zero hone
  | succ n ih =>
      have hstep : biasedHistoryMeasure γ β u (n + 1) (stepHistory S u (n + 1))
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (biasedDrivingKernel γ β u) n (n + 1) h
              (stepHistory S u (n + 1)) ∂(biasedHistoryMeasure γ β u n) := by
        unfold biasedHistoryMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_stepHistory S u (n + 1)) (Kernel.aemeasurable _)]
      rw [hstep]
      calc ENNReal.ofReal c ^ (n + 1 + 1)
          = ENNReal.ofReal c * ENNReal.ofReal c ^ (n + 1) := by ring
        _ ≤ ENNReal.ofReal c * biasedHistoryMeasure γ β u n (stepHistory S u n) := by gcongr
        _ = ∫⁻ h, (stepHistory S u n).indicator (fun _ => ENNReal.ofReal c) h
              ∂(biasedHistoryMeasure γ β u n) := by
            rw [lintegral_indicator (measurableSet_stepHistory S u n), setLIntegral_const]
        _ ≤ ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (biasedDrivingKernel γ β u) n (n + 1) h
              (stepHistory S u (n + 1)) ∂(biasedHistoryMeasure γ β u n) := by
            refine lintegral_mono fun h => ?_
            by_cases hh : h ∈ stepHistory S u n
            · rw [Set.indicator_of_mem hh]
              exact le_partialTraj_succ hone n hh
            · rw [Set.indicator_of_notMem hh]
              exact zero_le

/-- **The iteration of Proposition 8**, in the biased model and for any one-step bound.

The paper does it by conditioning on `Ũ_{m-1} = v` in eq. (10); here it goes along the
finite-horizon kernels of the Ionescu–Tulcea construction, Mathlib offering no decomposition
of that shape.  It is the same Markov property through the formalism that exists. -/
theorem pow_le_pathMeasure_stepEvents {S : Profile N M → Finset (Jump N M)} {c : ℝ}
    (hone : ∀ P : Profile N M, ENNReal.ofReal c ≤ (biasedJumpPMF γ β P).toMeasure (S P))
    (m : ℕ) :
    ENNReal.ofReal c ^ m ≤ biasedPathMeasure γ β u (stepEvents S u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have huniv : stepEvents S u 0 = Set.univ := by
      ext ω
      simp [stepEvents]
    rw [pow_zero, huniv, measure_univ]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hmap : (biasedPathMeasure γ β u).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n)
        = biasedHistoryMeasure γ β u n := by
      unfold biasedHistoryMeasure biasedPathMeasure
      rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
        Kernel.traj_map_frestrictLe]
    rw [stepEvents_succ_eq_preimage, ← Measure.map_apply
      (Preorder.measurable_frestrictLe n) (measurableSet_stepHistory S u n), hmap]
    exact pow_le_historyMeasure hone n

end Iterate

/-- The paper's `Y (u) = {(a, o) : u (a, o) = y (u)}`, for the biased model. -/
noncomputable def biasedArgmaxFinset (γ : ℝ) (P : Profile N M) : Finset (Jump N M) :=
  Finset.univ.filter fun p => P.pressure γ p.1 p.2 = pressureSup γ P

theorem mem_biasedArgmaxFinset {γ : ℝ} {P : Profile N M} {p : Jump N M} :
    p ∈ biasedArgmaxFinset γ P ↔ P.pressure γ p.1 p.2 = pressureSup γ P := by
  simp [biasedArgmaxFinset]

theorem isBiasedGreedyAt_iff_mem (γ : ℝ) (u : Profile N M) (ω : ℕ → Jump N M) (k : ℕ) :
    IsBiasedGreedyAt γ u ω k ↔ ω k ∈ biasedArgmaxFinset γ (stateAfter u ω k) := by
  rw [mem_biasedArgmaxFinset]
  constructor
  · intro h
    refine le_antisymm (le_pressureSup γ (stateAfter u ω k) _ _) ?_
    obtain ⟨a, o, hao⟩ := exists_pressureSup γ (stateAfter u ω k)
    rw [← hao]
    exact h a o
  · intro h a o
    rw [h]
    exact le_pressureSup γ (stateAfter u ω k) a o

/-- **The one-step bound of Proposition 17.**  The maximising pairs are the most probable of
the `NM` choices, so they are chosen with probability at least `(NM)⁻¹`.

**Follows the paper's proof of Proposition 17**, which is the whole of its probabilistic
content: "each `ξ_j^{α,u}` is the most probable of the `NM` choices". -/
theorem inv_le_biasedJumpPMF_biasedArgmaxFinset {γ β : ℝ} (hβ : 0 ≤ β) (P : Profile N M) :
    ENNReal.ofReal (1 / ((N * M : ℕ) : ℝ))
      ≤ (biasedJumpPMF γ β P).toMeasure (biasedArgmaxFinset γ P) := by
  obtain ⟨a₀, o₀, ha₀⟩ := exists_pressureSup γ P
  have hcardpos : (0 : ℝ) < ((N * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_neZero N) (Nat.pos_of_neZero M)
  have hmaxrate : biasedJumpRate γ β P a₀ o₀ = Real.exp (β * pressureSup γ P) := by
    unfold biasedJumpRate
    rw [ha₀]
  have hp₀ : (a₀, o₀) ∈ biasedArgmaxFinset γ P := mem_biasedArgmaxFinset.2 ha₀
  -- every rate is at most the maximal one
  have hle : ∀ p : Jump N M,
      biasedJumpRate γ β P p.1 p.2 ≤ Real.exp (β * pressureSup γ P) := by
    intro p
    unfold biasedJumpRate
    exact Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (le_pressureSup γ P p.1 p.2) hβ)
  have hS0 : (0 : ℝ) ≤ ∑ p ∈ biasedArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2 :=
    Finset.sum_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le
  have hAS : Real.exp (β * pressureSup γ P)
      ≤ ∑ p ∈ biasedArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2 := by
    rw [← hmaxrate]
    exact Finset.single_le_sum (fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le) hp₀
  have htot : (∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2)
      ≤ ((N * M : ℕ) : ℝ) * Real.exp (β * pressureSup γ P) := by
    have h1 := Finset.sum_le_card_nsmul (Finset.univ : Finset (Jump N M))
      (fun p => biasedJumpRate γ β P p.1 p.2) (Real.exp (β * pressureSup γ P))
      (fun p _ => hle p)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin] at h1
    exact_mod_cast h1
  have htotpos : (0 : ℝ) < ∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2 :=
    Finset.sum_pos (fun p _ => biasedJumpRate_pos γ β P p.1 p.2) (univ_jump_nonempty N M)
  have hreal : 1 / ((N * M : ℕ) : ℝ)
      ≤ (∑ p ∈ biasedArgmaxFinset γ P, biasedJumpRate γ β P p.1 p.2)
        / (∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2) := by
    rw [div_le_div_iff₀ hcardpos htotpos]
    nlinarith [Real.exp_pos (β * pressureSup γ P)]
  -- transport it to the measure
  have hw : ∀ t : Finset (Jump N M),
      (∑ p ∈ t, biasedJumpWeight γ β P p)
        = ENNReal.ofReal (∑ p ∈ t, biasedJumpRate γ β P p.1 p.2) := by
    intro t
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le]
    rfl
  have htsum : (∑' q : Jump N M, biasedJumpWeight γ β P q)
      = ENNReal.ofReal (∑ p : Jump N M, biasedJumpRate γ β P p.1 p.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun p hp => absurd (Finset.mem_univ p) hp, hw Finset.univ]
  rw [PMF.toMeasure_apply_finset]
  simp only [biasedJumpPMF_apply]
  rw [← Finset.sum_mul, hw (biasedArgmaxFinset γ P), htsum,
    ← ENNReal.ofReal_inv_of_pos htotpos, ← ENNReal.ofReal_mul hS0, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hreal

/-- `ξ^{α,u}` is the step event attached to `Y`. -/
theorem biasedGreedyEvents_eq_stepEvents (γ : ℝ) (u : Profile N M) (m : ℕ) :
    biasedGreedyEvents γ u m = stepEvents (biasedArgmaxFinset γ) u m := by
  ext ω
  simp only [biasedGreedyEvents, stepEvents, Set.mem_setOf_eq]
  exact ⟨fun hω k hk => (isBiasedGreedyAt_iff_mem γ u ω k).1 (hω k hk),
    fun hω k hk => (isBiasedGreedyAt_iff_mem γ u ω k).2 (hω k hk)⟩

/-- `P (⋂_{j=1}^{m} ξ_j^{α,u}) ≥ (NM)^{-m}`: the probabilistic half of Proposition 17. -/
theorem inv_pow_le_biasedPathMeasure_biasedGreedyEvents {γ β : ℝ} (hβ : 0 ≤ β)
    (u : Profile N M) (m : ℕ) :
    ENNReal.ofReal (1 / ((N * M : ℕ) : ℝ)) ^ m
      ≤ biasedPathMeasure γ β u (biasedGreedyEvents γ u m) := by
  rw [biasedGreedyEvents_eq_stepEvents]
  exact pow_le_pathMeasure_stepEvents (fun P => inv_le_biasedJumpPMF_biasedArgmaxFinset hβ P) m

/-- `ξ̃^{α,u}` is the step event attached to `Ỹ_γ`. -/
theorem nearGreedyEvents_eq_stepEvents (γ : ℝ) (u : Profile N M) (m : ℕ) :
    nearGreedyEvents γ u m = stepEvents (nearArgmaxFinset γ) u m := by
  ext ω
  simp only [nearGreedyEvents, stepEvents, Set.mem_setOf_eq]
  exact ⟨fun hω k hk => (isNearGreedyAt_iff_mem γ u ω k).1 (hω k hk),
    fun hω k hk => (isNearGreedyAt_iff_mem γ u ω k).2 (hω k hk)⟩

/-- **Proposition 24.**  `P (⋂_{j=1}^{m} ξ̃_j^{α,u}) ≥ (ζ_{α,β})^m`.

**Follows the paper's proof of Proposition 8**, which Appendix C invokes for this statement.
The lattice gap `1/(M-1)` is replaced by the slack `1/(2γ)` that the event `ξ̃` carries — the
substitution Remark 7 is designed for, the entries of the biased model no longer lying on a
lattice. -/
theorem biasedZeta_pow_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    (u : Profile N M) (m : ℕ) :
    ENNReal.ofReal (biasedZeta N M γ β) ^ m
      ≤ biasedPathMeasure γ β u (nearGreedyEvents γ u m) := by
  rw [nearGreedyEvents_eq_stepEvents]
  exact pow_le_pathMeasure_stepEvents
    (fun P => biasedZeta_le_biasedJumpPMF_nearArgmaxFinset hγ hβ P) m

end Propositions

/-! ### The biased process in continuous time

A direct mirror of `SocialNetwork.ContinuousTime`: the realisation carries the holding times
alongside the expressed pairs, the holding time from a profile `P` being exponential with the
total rate of equation (7) at `P`. -/

section BiasedContinuousTime

variable [NeZero N] [NeZero M]

/-- Replay the expressed pairs of a finite history of steps. -/
def stateAfterStepHistory (u : Profile N M) {n : ℕ} (h : (i : Finset.Iic n) → Step N M)
    (k : ℕ) : Profile N M :=
  stateAfterHistory u (fun i => (h i).1) k

theorem measurable_stateAfterStepHistory (u : Profile N M) (n k : ℕ) :
    Measurable fun h : (i : Finset.Iic n) → Step N M => stateAfterStepHistory u h k :=
  (Measurable.of_discrete
      (f := fun h : (i : Finset.Iic n) → Jump N M => stateAfterHistory u h k)).comp
    (measurable_stepHistoryJumps n)

/-- The law of one step of the biased process from the profile `P`. -/
noncomputable def biasedStepLaw (γ β : ℝ) (P : Profile N M) : Measure (Step N M) :=
  (biasedJumpPMF γ β P).toMeasure.prod (expMeasure (biasedTotalRate γ β P))

instance isProbabilityMeasure_biasedStepLaw (γ β : ℝ) (P : Profile N M) :
    IsProbabilityMeasure (biasedStepLaw γ β P) := by
  have : IsProbabilityMeasure (expMeasure (biasedTotalRate γ β P)) :=
    isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β P)
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- The kernel driving the biased process in continuous time. -/
noncomputable def biasedCtsDrivingKernel (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Step N M) (Step N M) where
  toFun h := biasedStepLaw γ β (stateAfterStepHistory u h (n + 1))
  measurable' :=
    (Measurable.of_discrete (f := fun P : Profile N M => biasedStepLaw γ β P)).comp
      (measurable_stateAfterStepHistory u n (n + 1))

theorem biasedCtsDrivingKernel_apply (γ β : ℝ) (u : Profile N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Step N M) :
    biasedCtsDrivingKernel γ β u n h = biasedStepLaw γ β (stateAfterStepHistory u h (n + 1)) :=
  rfl

instance isMarkovKernel_biasedCtsDrivingKernel (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    IsMarkovKernel (biasedCtsDrivingKernel γ β u n) :=
  ⟨fun h => by rw [biasedCtsDrivingKernel_apply]; infer_instance⟩

/-- The law of a realisation of the biased process in continuous time. -/
noncomputable def biasedCtsPathMeasure (γ β : ℝ) (u : Profile N M) :
    Measure (ℕ → Step N M) :=
  Kernel.traj (X := fun _ : ℕ => Step N M) (biasedCtsDrivingKernel γ β u) 0 ∘ₘ
    ((biasedStepLaw γ β u).map toStepHistoryZero)

instance isProbabilityMeasure_biasedCtsPathMeasure (γ β : ℝ) (u : Profile N M) :
    IsProbabilityMeasure (biasedCtsPathMeasure γ β u) := by
  rw [biasedCtsPathMeasure]
  have : IsProbabilityMeasure
      ((biasedStepLaw γ β u).map (toStepHistoryZero (N := N) (M := M))) :=
    Measure.isProbabilityMeasure_map measurable_toStepHistoryZero.aemeasurable
  infer_instance

/-- The profile of the biased process at time `t`. -/
noncomputable def biasedProcess (u : Profile N M) (t : ℝ) (ω : ℕ → Step N M) : Profile N M :=
  stateAfter u (fun n => (ω n).1) (jumpCount ω t)

/-- The hitting time `R^{α,β,u} (θ) = inf {t ≥ 0 : U_t^{α,β,u} ∈ θ}`. -/
noncomputable def biasedHittingTimeCts (u : Profile N M) (θ : Set (Profile N M))
    (ω : ℕ → Step N M) : ℝ≥0∞ :=
  sInf ((fun t : ℝ => ENNReal.ofReal t) '' {t : ℝ | 0 ≤ t ∧ biasedProcess u t ω ∈ θ})

/-- `P (R^{α,β,u} (θ) > t)`. -/
noncomputable def biasedProbHittingGT (γ β : ℝ) (u : Profile N M) (θ : Set (Profile N M))
    (t : ℝ≥0∞) : ℝ≥0∞ :=
  biasedCtsPathMeasure γ β u {ω | t < biasedHittingTimeCts u θ ω}

/-- `E (R^{α,β,u} (θ))`. -/
noncomputable def biasedExpHittingTimeCts (γ β : ℝ) (u : Profile N M)
    (θ : Set (Profile N M)) : ℝ≥0∞ :=
  ∫⁻ ω, biasedHittingTimeCts u θ ω ∂(biasedCtsPathMeasure γ β u)

end BiasedContinuousTime

/-! ### Section 5.4: the negative-bias regime -/

section NegativeBias

variable [NeZero N] [NeZero M]

/-- **Theorem 16.**  For any `β ≥ 0`, any `α < 0` and any starting profile `u ∈ S^α`, the jump
times of the biased process satisfy `P (sup {Tₘ : m ≥ 1} = ∞) = 1`.

The proof is that of Theorem 1, once Proposition 21 replaces Proposition 5. -/
theorem biasedNonExplosion (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    biasedCtsPathMeasure γ β u {ω | explosionTime ω = ⊤} = 1 := by
  sorry

theorem pressureSup_le {γ : ℝ} {Q : Profile N M} {c : ℝ}
    (h : ∀ a p, Q.pressure γ a p ≤ c) : pressureSup γ Q ≤ c :=
  Finset.sup'_le _ _ fun q _ => h q.1 q.2

/-- A state of `S^α` carries a non-negative maximum: the actor that has heard nothing has a
null row. -/
theorem pressureSup_nonneg {γ : ℝ} {P : Profile N M} (hP : IsBiasedState P) :
    0 ≤ pressureSup γ P := by
  obtain ⟨a, ha⟩ := hP.exists_zero_row
  have h0 : P.pressure γ a (0 : Opinion M) = 0 :=
    Memory.pressure_eq_zero_of_heard_eq_zero γ ha _
  rw [← h0]
  exact le_pressureSup γ P a 0

/-- One expression raises the maximum by at most one: the expressing actor's row is reset, and
every other actor gains `1` on the expressed opinion and loses `γ` on the others. -/
theorem pressureSup_express_le {γ : ℝ} (hγ : 0 < γ) {P : Profile N M} (hP : IsBiasedState P)
    (a₀ : Actor N) (o₀ : Opinion M) :
    pressureSup γ (Profile.express a₀ o₀ P) ≤ pressureSup γ P + 1 := by
  have hnn := pressureSup_nonneg (γ := γ) hP
  refine pressureSup_le fun b q => ?_
  by_cases hq : b = a₀
  · have hzero : (Profile.express a₀ o₀ P).pressure γ b q = 0 := by
      show (Profile.express a₀ o₀ P b).pressure γ q = 0
      rw [hq, Profile.express_self, Memory.pressure_reset]
    rw [hzero]
    linarith
  · have heq : (Profile.express a₀ o₀ P).pressure γ b q
        = P.pressure γ b q + (if q = o₀ then 1 else -γ) := by
      show (Profile.express a₀ o₀ P b).pressure γ q = _
      rw [Profile.express_of_ne hq, Memory.pressure_hear]
      rfl
    have hb := le_pressureSup γ P b q
    rw [heq]
    split <;> linarith

/-- Iterating `pressureSup_express_le` along a realisation. -/
theorem pressureSup_stateAfter_le {γ : ℝ} (hγ : 0 < γ) {u : Profile N M}
    (hu : IsBiasedState u) (ω : ℕ → Jump N M) (k t : ℕ) :
    pressureSup γ (stateAfter u ω (k + t)) ≤ pressureSup γ (stateAfter u ω k) + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hst : IsBiasedState (stateAfter u ω (k + t)) := isBiasedState_stateAfter hu ω _
      have hstep : pressureSup γ (stateAfter u ω (k + t + 1))
          ≤ pressureSup γ (stateAfter u ω (k + t)) + 1 := by
        rw [stateAfter_succ]
        exact pressureSup_express_le hγ hst _ _
      rw [show k + (t + 1) = k + t + 1 by ring]
      push_cast
      linarith

/-- **The deterministic half of Proposition 17.**  On `⋂_{j=1}^{N} ξ_j^{α,u}`, every entry of
the profile reached after `N` expressions is at most `N`.

**Follows the paper's proof of Proposition 6**, which Section 5.4 invokes, in its two cases.
Here the quantity that resets and grows by one per step is `nₐ`, and `u (a, p) ≤ nₐ` is what
connects it to the entries.  Unlike Proposition 22, the chain closes: greediness is exact, so
the maximum at the repeat time is the expressing actor's own entry, with no slack to
absorb. -/
theorem pressure_stateAfter_le_of_biasedGreedy (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    {u : Profile N M} (hu : IsBiasedState u) {ω : ℕ → Jump N M}
    (hgreedy : ∀ k, k < N → IsBiasedGreedyAt γ u ω k) (a : Actor N) (p : Opinion M) :
    (stateAfter u ω N).pressure γ a p ≤ (N : ℝ) := by
  by_cases hdist : ∀ j k, j < k → k < N → (ω j).1 ≠ (ω k).1
  · -- every actor expressed once, so every row was reset within the first `N` steps
    have hinj : Function.Injective fun i : Fin N => (ω (i : ℕ)).1 := by
      intro i j hij
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · exact absurd hij (hdist _ _ h j.isLt)
      · exact Fin.val_injective h
      · exact absurd hij.symm (hdist _ _ h i.isLt)
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj a
    have hi' : (ω (i : ℕ)).1 = a := hi
    have hz := heard_stateAfter_expressed u ω (i : ℕ)
    rw [hi'] at hz
    have hiN := i.isLt
    have hle := heard_stateAfter_le u ω a ((i : ℕ) + 1) (N - (i : ℕ) - 1)
    rw [hz, Nat.zero_add, show (i : ℕ) + 1 + (N - (i : ℕ) - 1) = N by omega] at hle
    have hcast : ((stateAfter u ω N).heard a : ℝ) ≤ (N : ℝ) := by
      have hnat : (stateAfter u ω N).heard a ≤ N := by omega
      exact_mod_cast hnat
    exact le_trans (Profile.pressure_le_heard hγ _ a p) hcast
  · -- some actor expressed twice; greediness at that step caps the whole profile
    push_neg at hdist
    obtain ⟨j, k, hjk, hk, heq⟩ := hdist
    have hz := heard_stateAfter_expressed u ω j
    have hle := heard_stateAfter_le u ω (ω j).1 (j + 1) (k - j - 1)
    rw [hz, Nat.zero_add, show j + 1 + (k - j - 1) = k by omega, heq] at hle
    have hgk := (isBiasedGreedyAt_iff_mem γ u ω k).1 (hgreedy k hk)
    have hsup : pressureSup γ (stateAfter u ω k) ≤ ((k - j - 1 : ℕ) : ℝ) := by
      rw [← mem_biasedArgmaxFinset.1 hgk]
      refine le_trans (Profile.pressure_le_heard hγ _ _ _) ?_
      exact_mod_cast hle
    have hgrow := pressureSup_stateAfter_le hγ hu ω k (N - k)
    rw [show k + (N - k) = N by omega] at hgrow
    have hnat : (k - j - 1) + (N - k) ≤ N := by omega
    have hcast : ((k - j - 1 : ℕ) : ℝ) + ((N - k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnat
    have hfin : pressureSup γ (stateAfter u ω N) ≤ (N : ℝ) := by linarith
    exact le_trans (le_pressureSup γ (stateAfter u ω N) a p) hfin

/-- **Proposition 17.**  For `α < 0`, after `N` expressions the biased process is in the
bounded set `B_N^α` with probability at least `(NM)^{-N}`.

The event `⋂_{j=1}^{N} ξ_j^{α,u}` forces it, and each `ξ_j^{α,u}` is the most probable of the
`NM` choices, so has probability at least `(MN)^{-1}`.

**Follows the paper's proof of Proposition 17**: `pressure_stateAfter_le_of_biasedGreedy` is
the first half and `inv_le_biasedJumpPMF_biasedArgmaxFinset` the second. -/
theorem measure_biasedBounded_ge (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 1 / ((M : ℝ) - 1) < γ) (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    ENNReal.ofReal ((((N * M : ℕ) : ℝ)) ^ (-(N : ℤ)))
      ≤ biasedPathMeasure γ β u {ω | stateAfter u ω N ∈ biasedBounded N M γ} := by
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hγ0 : 0 < γ := lt_trans (by positivity) hγ
  have hcpos : (0 : ℝ) < ((N * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < N) (by omega : 0 < M)
  have hz : ((N * M : ℕ) : ℝ) ^ (-(N : ℤ)) = (1 / ((N * M : ℕ) : ℝ)) ^ N := by
    rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]
  rw [hz, ENNReal.ofReal_pow (by positivity)]
  refine le_trans (inv_pow_le_biasedPathMeasure_biasedGreedyEvents hβ u N) (measure_mono ?_)
  intro ω hω
  exact ⟨isBiasedState_stateAfter hu ω N,
    fun a p => pressure_stateAfter_le_of_biasedGreedy hM hN hγ0 hu
      (fun k hk => hω k hk) a p⟩

/-- **Proposition 18.**  For `α < 0`, from any profile in `B_N^α` there is a uniformly positive
chance that a single actor expresses forever after. -/
theorem inf_measure_forall_eq_first_pos (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 1 / ((M : ℝ) - 1) < γ) (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Profile N M, u ∈ biasedBounded N M γ →
      ENNReal.ofReal c
        ≤ biasedPathMeasure γ β u {ω | ∀ j, (ω j).1 = (ω 0).1} := by
  sorry

/-- **Theorem 4.1.**  For `α < 0`, almost surely all but one actor eventually stop expressing:

```
P (⋃_{n ≥ 1} ⋂_{m ≥ n} {A_n^α = A_m^α}) = 1.
```
-/
theorem biasedAbsorption (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 < β) {u : Profile N M} (hu : IsBiasedState u) :
    biasedPathMeasure γ β u {ω | ∃ n, ∀ m, n ≤ m → (ω m).1 = (ω n).1} = 1 := by
  sorry

end NegativeBias

/-! ### Appendix C: the positive-bias regime `0 < α < 1/(M-1)` -/

section PositiveBias

variable [NeZero N] [NeZero M]

/-- Invariance of a measure for the biased skeleton. -/
def IsBiasedInvariant (γ β : ℝ) (μ : Measure (Profile N M)) : Prop :=
  Kernel.Invariant (biasedSkeletonKernel γ β) μ

/-- A measure carried by `S^α`. -/
def IsCarriedByBiasedState (μ : Measure (Profile N M)) : Prop :=
  μ (biasedStateSet N M)ᶜ = 0

/-- **Theorem 25.**  For `0 < α < 1/(M-1)` the biased process does not explode and has a
unique invariant probability measure `μ_{β,α}`. -/
theorem existsUnique_biasedInvariant (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β) :
    ∃! μ : Measure (Profile N M),
      IsProbabilityMeasure μ ∧ IsCarriedByBiasedState μ ∧ IsBiasedInvariant γ β μ := by
  sorry

/-- **Proposition 26.**  For `0 < α < 1/(M-1)`, `β > 0` and `u ∉ L̂_α`, the invariant measure
of the biased skeleton satisfies `μ̃_{α,β} (u) ≤ C̃ e^{-β(N-1)}`. -/
theorem biasedMeasure_le_of_notMem_steepLadder (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 0 < γ) (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β)
    {μ : Measure (Profile N M)} (hμ : IsProbabilityMeasure μ) (hinv : IsBiasedInvariant γ β μ)
    {u : Profile N M} (hu : u ∉ biasedSteepLadderSet N M γ) :
    ∃ C : ℝ, 0 < C ∧ μ {u} ≤ ENNReal.ofReal (C * Real.exp (-β * ((N : ℝ) - 1))) := by
  sorry

/-- **Theorem 27.1.**  For `0 < α < 1/(M-1)` there is a constant `C > 0` with
`μ_{α,β} (L_α) ≥ 1 - C e^{-β (M-1) α}`.

The exponent is `(M-1) α` rather than `1/(M-1)`, by Remark 8: that is the smallest maximum a
non-null row of `S^α` can have, hence the smallest jump rate exponent. -/
theorem biasedMeasure_ladderSet_ge (hM : 2 ≤ M) (hN : 3 ≤ N) {γ α : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ μ : Measure (Profile N M),
      IsProbabilityMeasure μ → IsCarriedByBiasedState μ → IsBiasedInvariant γ β μ →
        ENNReal.ofReal (1 - C * Real.exp (-β * (((M : ℝ) - 1) * α)))
          ≤ μ (biasedLadderSet N M γ) := by
  sorry

/-- **Theorem 27.2.**  For every fixed `δ > 0`,
`sup_{u ∈ S^α} P (R^{α,β,u} (L_α) > e^{-β (M-1) α (1-δ)}) → 0` as `β → +∞`.

The zero matrix does not have to be excluded here: by Remark 1 it is not in `S^α`. -/
theorem tendsto_biasedHittingTime (hM : 2 ≤ M) (hN : 3 ≤ N) {γ α : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ u ∈ biasedStateSet N M,
        biasedProbHittingGT γ β u (biasedLadderSet N M γ)
          (ENNReal.ofReal (Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ)))))
      Filter.atTop (nhds 0) := by
  sorry

/-- **Lemma 28.**  `P (R^{α,β,u} (L_α) > 2β) ≤ C e^{-β/(2γ)}`. -/
theorem biasedProbHitting_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    ∃ C : ℝ, 0 < C ∧
      biasedPathMeasure γ β u {ω | ∀ k, k ≤ Nat.ceil (2 * β) →
          stateAfter u ω k ∉ biasedLadderSet N M γ}
        ≤ ENNReal.ofReal (C * Real.exp (-β / (2 * γ))) := by
  sorry

/-- **Lemma 29.1.**  From a biased ladder supporting `o`, the consensus for another opinion is
not reached before time `t` with probability at least
`exp (-2 t N³ (M+1)³ e^{-β/(2γ)})`. -/
theorem le_biasedProbHittingGT (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {l : Profile N M}
    (hl : IsBiasedLadder γ o l) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.exp
        (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / (2 * γ))))
      ≤ biasedProbHittingGT γ β l (biasedConsensusSetOther N γ o) (ENNReal.ofReal t) := by
  sorry

/-- **Lemma 29.2.**  From a biased consensus state for `o`, the consensus for another opinion
is reached before time `t` with probability at most
`(N² M + 2 t N³ (M+1)³) e^{-β/(2γ)}`. -/
theorem biasedProbHittingLE_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {u : Profile N M}
    (hu : IsBiasedConsensus γ o u) {t : ℝ} (ht : 0 < t) :
    biasedCtsPathMeasure γ β u
        {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal t}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
          Real.exp (-β / (2 * γ))) := by
  sorry

/-- The characteristic time `c_{α,β}` of Appendix C. -/
def IsBiasedCharacteristicTime (γ β : ℝ) (o : Opinion M) (c : ℝ) : Prop :=
  0 < c ∧ ∀ l : Profile N M, IsBiasedLadder γ o l →
    biasedProbHittingGT γ β l (biasedConsensusSetOther N γ o) (ENNReal.ofReal c)
      = ENNReal.ofReal (Real.exp (-1))

/-- **Corollary 30.**  `c_{α,β} ≥ (1/2) N^{-3} (M+1)^{-3} e^{β/(2γ)}`. -/
theorem le_biasedCharacteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {c : ℝ}
    (hc : IsBiasedCharacteristicTime (N := N) γ β o c) :
    (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ * Real.exp (β / (2 * γ)) ≤ c := by
  sorry

/-- **Theorem 31.**  Metastability for the biased model: for `0 < α < 1/(M-1)` there are
`β₀, C₁ > 0` and `C₂ > 0`, depending only on `α`, `M` and `N`, such that the rescaled exit
time from a biased consensus set is exponential of parameter one up to `C₁ β³ e^{-C₂ β}`. -/
theorem biasedMetastability (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) :
    ∃ β₀ C₁ C₂ : ℝ, 0 < β₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ o : Opinion M, ∀ u : Profile N M, IsBiasedConsensus γ o u →
        (∀ t : ℝ, 0 ≤ t →
          |(biasedProbHittingGT γ β u (biasedConsensusSetOther N γ o)
              (ENNReal.ofReal t *
                biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o))).toReal
            - Real.exp (-t)| ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β)) ∧
        ∀ v : Profile N M, IsBiasedConsensus γ o v →
          |(biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o)).toReal /
              (biasedExpHittingTimeCts γ β v (biasedConsensusSetOther N γ o)).toReal - 1|
            ≤ C₁ * β ^ 3 * Real.exp (-C₂ * β) := by
  sorry

end PositiveBias

end Bias

end SocialNetwork
