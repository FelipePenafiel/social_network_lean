/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedModel
import SocialNetwork.ContinuousTime

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

/-- **Proposition 21.**  Among the first `N` expressions of the biased model, at least one
comes from an actor whose social pressure on the expressed opinion is below `N`.

The proof is that of Proposition 5, which is combinatorial and does not see the bias. -/
theorem exists_pressure_lt (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) {u : Profile N M}
    (hu : IsBiasedState u) (ω : ℕ → Jump N M) :
    ∃ k < N, ∀ o, (stateAfter u ω k).pressure γ (ω k).1 o < (N : ℝ) := by
  sorry

/-- **Proposition 22.**  On `⋂_{j=1}^{N} ξ̃_j^{α,u}`, the whole matrix is confined to
`(-MN, N)` entrywise after `N` expressions. -/
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

/-- **Proposition 24.**  `P (⋂_{j=1}^{m} ξ̃_j^{α,u}) ≥ (ζ_{α,β})^m`.

The proof is that of Proposition 8, with the lattice gap `1/(M-1)` replaced by the slack
`1/(2γ)` built into the event `ξ̃`. -/
theorem biasedZeta_pow_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    (u : Profile N M) (m : ℕ) :
    ENNReal.ofReal (biasedZeta N M γ β) ^ m
      ≤ biasedPathMeasure γ β u (nearGreedyEvents γ u m) := by
  sorry

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

/-- **Proposition 17.**  For `α < 0`, after `N` expressions the biased process is in the
bounded set `B_N^α` with probability at least `(NM)^{-N}`.

The event `⋂_{j=1}^{N} ξ_j^{α,u}` forces it, and each `ξ_j^{α,u}` is the most probable of the
`NM` choices, so has probability at least `(MN)^{-1}`. -/
theorem measure_biasedBounded_ge (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 1 / ((M : ℝ) - 1) < γ) (hβ : 0 ≤ β) {u : Profile N M} (hu : IsBiasedState u) :
    ENNReal.ofReal ((((N * M : ℕ) : ℝ)) ^ (-(N : ℤ)))
      ≤ biasedPathMeasure γ β u {ω | stateAfter u ω N ∈ biasedBounded N M γ} := by
  sorry

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
