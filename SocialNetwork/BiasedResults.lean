/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedModel
import SocialNetwork.ContinuousTime
import SocialNetwork.Frequencies
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

Every numbered statement of Section 3 and Appendix C is stated here.  Which of them are
proved is recorded in `STATUS.md`, which is generated from the blueprint and checked by CI;
this docstring deliberately does not duplicate it, since a hand-kept list drifts.  What is
unproved is unproved for the reasons of the unbiased case (no Doeblin criterion, no Kac
lemma, no Poisson point process in Mathlib) except where `FOR-THE-AUTHORS.md` says
otherwise.

## Main definitions

* `SocialNetwork.Bias.stateAfter` — the profile after `n` expressions.
* `SocialNetwork.Bias.biasedGenerator` — the generator `G̃` of equation (7).
* `SocialNetwork.Bias.biasedSkeletonKernel` — the skeleton of the biased model.
* `SocialNetwork.Bias.biasedPathMeasure` — the law of a realisation.
* `SocialNetwork.Bias.IsBiasedGreedyAt` — the event `ξ_n^{α,u}` of Proposition 17.
* `SocialNetwork.Bias.IsNearGreedyAt` — the event `ξ̃_n^{α,u}` of Remark 7, with its slack
  of `1/(2γ)`.
* `SocialNetwork.Bias.soloPath` — the realisation in which a single actor expresses for
  ever, which carries the proof of Proposition 18.
* `SocialNetwork.Bias.shiftPath` — the realisation shifted in time, and with it
  `SocialNetwork.Bias.pathMeasure_restart`, the Markov property at a deterministic time.
* `SocialNetwork.Bias.sameFrom` — the event that a single actor performs every expression
  from a given one on, which is what Theorem 4 part 1 is about.

## Main statements

Theorem 4, Theorem 16, Propositions 17, 18, 21, 22, 23 and 24, Theorem 25,
Proposition 26, Theorem 27, Lemmas 28 and 29, Corollary 30 and Theorem 31 — all stated.
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

omit [NeZero N] [NeZero M] in
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
  simp only [biasedGreedyEvents, Set.mem_ofPred_eq, Set.mem_preimage]
  exact ⟨fun hω k hk => (isBiasedGreedyAt_ofHistoryPath_frestrictLe γ u ω hk.le).2 (hω k hk),
    fun hω k hk => (isBiasedGreedyAt_ofHistoryPath_frestrictLe γ u ω hk.le).1 (hω k hk)⟩

theorem nearGreedyEvents_eq_preimage (γ : ℝ) (u : Profile N M) (n : ℕ) :
    nearGreedyEvents γ u n =
      Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹'
        {h | ∀ k < n, IsNearGreedyAt γ u (ofHistoryPath h) k} := by
  ext ω
  simp only [nearGreedyEvents, Set.mem_ofPred_eq, Set.mem_preimage]
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

omit [NeZero N] [NeZero M] in
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

omit [NeZero N] [NeZero M] in
/-- Expressing resets the number of expressions heard. -/
theorem heard_stateAfter_expressed (u : Profile N M) (ω : ℕ → Jump N M) (j : ℕ) :
    (stateAfter u ω (j + 1)).heard (ω j).1 = 0 := by
  rw [stateAfter_succ, Profile.heard_express_self]

omit [NeZero N] [NeZero M] in
/-- **Proposition 21.**  Among the first `N` expressions of the biased model, at least one
comes from an actor whose social pressure on the expressed opinion is below `N`.

The proof is that of Proposition 5, which is combinatorial and does not see the bias. -/
theorem exists_pressure_lt (_hM : 2 ≤ M) (_hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ) {u : Profile N M}
    (hu : IsBiasedState u) (ω : ℕ → Jump N M) :
    ∃ k < N, ∀ o, (stateAfter u ω k).pressure γ (ω k).1 o < (N : ℝ) := by
  by_contra hcon
  push Not at hcon
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

/-- The event that the `k`-th expressed pair lies in `S k` at the profile reached then, for
every `k < m`.

The set is allowed to depend on the step as well as on the profile: at a constant `S` this is
the event `⋂_{j=1}^{m} ξ_j` of Propositions 17 and 24, and at the singleton
`S k _ = {ζ k}` it is the cylinder `{ω : ω_k = ζ_k for k < m}` of Proposition 18. -/
def stepEvents (S : ℕ → Profile N M → Finset (Jump N M)) (u : Profile N M) (m : ℕ) :
    Set (ℕ → Jump N M) :=
  {ω | ∀ k < m, ω k ∈ S k (stateAfter u ω k)}

/-- The same event, read on histories of the first `n + 1` expressed pairs. -/
def stepHistory (S : ℕ → Profile N M → Finset (Jump N M)) (u : Profile N M) (n : ℕ) :
    Set ((i : Finset.Iic n) → Jump N M) :=
  {h | ∀ k ≤ n, ofHistoryPath h k ∈ S k (stateAfter u (ofHistoryPath h) k)}

omit [NeZero N] [NeZero M] in
theorem measurableSet_stepHistory (S : ℕ → Profile N M → Finset (Jump N M)) (u : Profile N M)
    (n : ℕ) : MeasurableSet (stepHistory S u n) := MeasurableSet.of_discrete

omit [NeZero N] [NeZero M] in
/-- `⋂_{j=1}^{n+1}` of the event is the cylinder over `stepHistory S u n`. -/
theorem stepEvents_succ_eq_preimage (S : ℕ → Profile N M → Finset (Jump N M))
    (u : Profile N M) (n : ℕ) :
    stepEvents S u (n + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹' stepHistory S u n := by
  have key : ∀ (ω : ℕ → Jump N M) (k : ℕ), k ≤ n →
      (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω) k
        ∈ S k (stateAfter u (ofHistoryPath
            (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)) k)
        ↔ ω k ∈ S k (stateAfter u ω k)) := by
    intro ω k hk
    rw [stateAfter_ofHistoryPath_frestrictLe u ω (by omega),
      ofHistoryPath_apply _ hk, Preorder.frestrictLe_apply]
  ext ω
  simp only [stepEvents, stepHistory, Set.mem_ofPred_eq, Set.mem_preimage]
  exact ⟨fun hω k hk => (key ω k hk).2 (hω k (by omega)),
    fun hω k hk => (key ω k (by omega)).1 (hω k (by omega))⟩

omit [NeZero N] [NeZero M] in
theorem measurableSet_stepEvents (S : ℕ → Profile N M → Finset (Jump N M)) (u : Profile N M)
    (m : ℕ) : MeasurableSet (stepEvents S u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : stepEvents S u 0 = Set.univ := by ext ω; simp [stepEvents]
    rw [h0]
    exact MeasurableSet.univ
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [stepEvents_succ_eq_preimage]
    exact Preorder.measurable_frestrictLe n (measurableSet_stepHistory S u n)

omit [NeZero N] [NeZero M] in
theorem ofHistoryPath_eq {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h) {j : ℕ}
    (hj : j ≤ n) : ofHistoryPath x j = ofHistoryPath h j := by
  rw [ofHistoryPath_apply _ (show j ≤ n + 1 by omega), ofHistoryPath_apply _ hj, ← hx,
    Preorder.frestrictLe₂_apply]

omit [NeZero N] [NeZero M] in
theorem stateAfter_ofHistoryPath_eq {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (u : Profile N M) {k : ℕ} (hk : k ≤ n + 1) :
    stateAfter u (ofHistoryPath x) k = stateAfter u (ofHistoryPath h) k :=
  stateAfter_congr u k fun j hj => ofHistoryPath_eq hx (by omega)

omit [NeZero N] [NeZero M] in
/-- If a history of length `n + 2` restricts to one in `stepHistory S u n` and its last
coordinate lies in `S (n + 1)` at the profile that history reaches, then it is in
`stepHistory S u (n + 1)`. -/
theorem mem_stepHistory_succ {S : ℕ → Profile N M → Finset (Jump N M)} {n : ℕ}
    {x : (i : Finset.Iic (n + 1)) → Jump N M} {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (hh : h ∈ stepHistory S u n)
    (hlast : x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ S (n + 1) (stateAfterHistory u h (n + 1))) :
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

/-- The one-step kernel of the Ionescu-Tulcea construction leaves the history it is given
untouched: everything but the extensions of `h` is null. -/
theorem partialTraj_compl_null (n : ℕ) (h : (i : Finset.Iic n) → Jump N M) :
    Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) n (n + 1) h
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})ᶜ = 0 := by
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
  exact (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hAone

/-- The last coordinate of that one-step kernel is the jump law at the profile the history
reaches. -/
theorem partialTraj_map_last (n : ℕ) (h : (i : Finset.Iic n) → Jump N M) :
    (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (biasedDrivingKernel γ β u) n (n + 1) h).map
      (fun x : (i : Finset.Iic (n + 1)) → Jump N M => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      = (biasedJumpPMF γ β (stateAfterHistory u h (n + 1))).toMeasure := by
  rw [← Kernel.map_apply _ Measurable.of_discrete, Kernel.map_partialTraj_succ_self,
    biasedDrivingKernel_apply]

/-- **The induction step**, for whatever one-step bound holds at the profile this history
reaches. -/
theorem le_partialTraj_succ {S : ℕ → Profile N M → Finset (Jump N M)} {c : ℝ≥0∞}
    (n : ℕ) {h : (i : Finset.Iic n) → Jump N M} (hh : h ∈ stepHistory S u n)
    (hone : c ≤ (biasedJumpPMF γ β (stateAfterHistory u h (n + 1))).toMeasure
      (S (n + 1) (stateAfterHistory u h (n + 1)))) :
    c ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) n (n + 1) h
          (stepHistory S u (n + 1)) := by
  have hB : c
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
          (biasedDrivingKernel γ β u) n (n + 1) h
          ((fun x : (i : Finset.Iic (n + 1)) → Jump N M =>
              x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            (S (n + 1) (stateAfterHistory u h (n + 1)))) := by
    rw [← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      partialTraj_map_last]
    exact hone
  exact le_measure_of_inter (partialTraj_compl_null n h) hB
    fun x hx => mem_stepHistory_succ hx.1 hh hx.2

/-- The law of the first `n + 1` expressed pairs of the biased chain. -/
noncomputable def biasedHistoryMeasure (γ β : ℝ) (u : Profile N M) (n : ℕ) :
    Measure ((i : Finset.Iic n) → Jump N M) :=
  Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) 0 n ∘ₘ
    ((biasedJumpPMF γ β u).toMeasure.map toHistoryZero)

theorem le_historyMeasure_zero {S : ℕ → Profile N M → Finset (Jump N M)} {c : ℝ≥0∞}
    (hone : c ≤ (biasedJumpPMF γ β u).toMeasure (S 0 u)) :
    c ≤ biasedHistoryMeasure γ β u 0 (stepHistory S u 0) := by
  have hpre : toHistoryZero ⁻¹' stepHistory S u 0 = (S 0 u : Set (Jump N M)) := by
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
  exact hone

/-- The one-step bound, in the form the induction consumes: it may depend on the step and on
the whole past, as long as the past is admissible. -/
def IsStepBound (γ β : ℝ) (S : ℕ → Profile N M → Finset (Jump N M)) (u : Profile N M)
    (c : ℕ → ℝ≥0∞) : Prop :=
  ∀ (m : ℕ) (ω : ℕ → Jump N M), (∀ k < m, ω k ∈ S k (stateAfter u ω k)) →
    c m ≤ (biasedJumpPMF γ β (stateAfter u ω m)).toMeasure (S m (stateAfter u ω m))

theorem prod_le_historyMeasure {S : ℕ → Profile N M → Finset (Jump N M)} {c : ℕ → ℝ≥0∞}
    (hone : IsStepBound γ β S u c) (n : ℕ) :
    ∏ m ∈ Finset.range (n + 1), c m ≤ biasedHistoryMeasure γ β u n (stepHistory S u n) := by
  induction n with
  | zero =>
      have h0 := hone 0 (fun _ => default) (by omega)
      rw [stateAfter_zero] at h0
      simpa using le_historyMeasure_zero h0
  | succ n ih =>
      have hstep : biasedHistoryMeasure γ β u (n + 1) (stepHistory S u (n + 1))
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (biasedDrivingKernel γ β u) n (n + 1) h
              (stepHistory S u (n + 1)) ∂(biasedHistoryMeasure γ β u n) := by
        unfold biasedHistoryMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_stepHistory S u (n + 1)) (Kernel.aemeasurable _)]
      rw [hstep]
      calc ∏ m ∈ Finset.range (n + 1 + 1), c m
          = c (n + 1) * ∏ m ∈ Finset.range (n + 1), c m := by
            rw [Finset.prod_range_succ]; ring
        _ ≤ c (n + 1) * biasedHistoryMeasure γ β u n (stepHistory S u n) := by gcongr
        _ = ∫⁻ h, (stepHistory S u n).indicator (fun _ => c (n + 1)) h
              ∂(biasedHistoryMeasure γ β u n) := by
            rw [lintegral_indicator (measurableSet_stepHistory S u n), setLIntegral_const]
        _ ≤ ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (biasedDrivingKernel γ β u) n (n + 1) h
              (stepHistory S u (n + 1)) ∂(biasedHistoryMeasure γ β u n) := by
            refine lintegral_mono fun h => ?_
            by_cases hh : h ∈ stepHistory S u n
            · rw [Set.indicator_of_mem hh]
              exact le_partialTraj_succ n hh
                (hone (n + 1) (ofHistoryPath h) fun k hk => hh k (by omega))
            · rw [Set.indicator_of_notMem hh]
              exact zero_le

/-- **The iteration of Proposition 8**, in the biased model and for any one-step bound.

The paper does it by conditioning on `Ũ_{m-1} = v` in eq. (10); here it goes along the
finite-horizon kernels of the Ionescu–Tulcea construction, Mathlib offering no decomposition
of that shape.  It is the same Markov property through the formalism that exists. -/
theorem prod_le_pathMeasure_stepEvents {S : ℕ → Profile N M → Finset (Jump N M)}
    {c : ℕ → ℝ≥0∞} (hone : IsStepBound γ β S u c) (m : ℕ) :
    ∏ j ∈ Finset.range m, c j ≤ biasedPathMeasure γ β u (stepEvents S u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have huniv : stepEvents S u 0 = Set.univ := by
      ext ω
      simp [stepEvents]
    rw [Finset.range_zero, Finset.prod_empty, huniv, measure_univ]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hmap : (biasedPathMeasure γ β u).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n)
        = biasedHistoryMeasure γ β u n := by
      unfold biasedHistoryMeasure biasedPathMeasure
      rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
        Kernel.traj_map_frestrictLe]
    rw [stepEvents_succ_eq_preimage, ← Measure.map_apply
      (Preorder.measurable_frestrictLe n) (measurableSet_stepHistory S u n), hmap]
    exact prod_le_historyMeasure hone n

/-- The iteration at a bound that does not depend on the step: Propositions 17 and 24. -/
theorem pow_le_pathMeasure_stepEvents {S : Profile N M → Finset (Jump N M)} {c : ℝ}
    (hone : ∀ P : Profile N M, ENNReal.ofReal c ≤ (biasedJumpPMF γ β P).toMeasure (S P))
    (m : ℕ) :
    ENNReal.ofReal c ^ m ≤ biasedPathMeasure γ β u (stepEvents (fun _ => S) u m) := by
  have := prod_le_pathMeasure_stepEvents (u := u) (S := fun _ => S)
    (c := fun _ => ENNReal.ofReal c) (fun k ω _ => hone _) m
  simpa using this

/-- **The probability of following a prescribed sequence of expressed pairs** is at least the
product of the one-step probabilities along it.  This is equation (21) of the paper, whose
right-hand side it bounds term by term. -/
theorem prod_le_pathMeasure_cylinder (ζ : ℕ → Jump N M) (n : ℕ) :
    ∏ m ∈ Finset.range n, biasedJumpPMF γ β (stateAfter u ζ m) (ζ m)
      ≤ biasedPathMeasure γ β u {ω | ∀ k < n, ω k = ζ k} := by
  classical
  have hev : {ω : ℕ → Jump N M | ∀ k < n, ω k = ζ k}
      = stepEvents (fun k _ => ({ζ k} : Finset (Jump N M))) u n := by
    ext ω
    simp [stepEvents]
  rw [hev]
  refine prod_le_pathMeasure_stepEvents (S := fun k _ => ({ζ k} : Finset (Jump N M)))
    (c := fun m => biasedJumpPMF γ β (stateAfter u ζ m) (ζ m)) (fun m ω hω => ?_) n
  have hst : stateAfter u ω m = stateAfter u ζ m :=
    stateAfter_congr u m fun j hj => Finset.mem_singleton.1 (hω j hj)
  rw [hst]
  refine le_of_eq ?_
  rw [Finset.coe_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (ζ m))]

/-! #### The exact law of a cylinder

The bound above is in fact an equality, and Proposition 18 needed only the inequality.  The
equality is what the Markov property of Theorem 4 rests on, so it is proved here, by the same
induction with the one-step kernel evaluated at a singleton. -/

/-- The one-step kernel of the Ionescu-Tulcea construction, at a singleton: it is the jump
probability of the last coordinate, and zero unless the history is the one it was given. -/
theorem partialTraj_singleton (n : ℕ) (h : (i : Finset.Iic n) → Jump N M)
    (x : (i : Finset.Iic (n + 1)) → Jump N M) :
    Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (biasedDrivingKernel γ β u) n (n + 1) h {x}
      = if Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h then
          biasedJumpPMF γ β (stateAfterHistory u h (n + 1)) (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
        else 0 := by
  by_cases hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h
  · rw [if_pos hx]
    have hset : ({x} : Set ((i : Finset.Iic (n + 1)) → Jump N M))
        = (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})
          ∩ ((fun y : (i : Finset.Iic (n + 1)) → Jump N M =>
              y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩}) := by
      ext y
      constructor
      · rintro rfl
        exact ⟨hx, rfl⟩
      · rintro ⟨hy1, hy2⟩
        have hy1' : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) y
            = Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x := by
          rw [hy1, hx]
        refine funext fun i => ?_
        rcases Nat.lt_or_ge (i : ℕ) (n + 1) with hi | hi
        · have hi' : (i : ℕ) ≤ n := by omega
          have hcast : (⟨(i : ℕ), Finset.mem_Iic.2 (by omega : (i : ℕ) ≤ n + 1)⟩ :
              Finset.Iic (n + 1)) = i := Subtype.ext rfl
          have := congrFun hy1' ⟨(i : ℕ), Finset.mem_Iic.2 hi'⟩
          rw [Preorder.frestrictLe₂_apply, Preorder.frestrictLe₂_apply, hcast] at this
          exact this
        · have hieq : i = (⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic (n + 1)) :=
            Subtype.ext (le_antisymm (Finset.mem_Iic.1 i.2) hi)
          rw [hieq]
          exact hy2
    rw [hset]
    have hcap : Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (biasedDrivingKernel γ β u) n (n + 1) h
        ((Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})
          ∩ ((fun y : (i : Finset.Iic (n + 1)) → Jump N M =>
              y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩}))
        = Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
            (biasedDrivingKernel γ β u) n (n + 1) h
            ((fun y : (i : Finset.Iic (n + 1)) → Jump N M =>
                y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
              {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩}) := by
      refine le_antisymm (measure_mono Set.inter_subset_right) ?_
      have hcover : ((fun y : (i : Finset.Iic (n + 1)) → Jump N M =>
            y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
          {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩})
          ⊆ ((Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})
              ∩ ((fun y : (i : Finset.Iic (n + 1)) → Jump N M =>
                  y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
                {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩}))
            ∪ (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M)
                (Nat.le_succ n) ⁻¹' {h})ᶜ := by
        intro y hy
        by_cases hA : y ∈ (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M)
            (Nat.le_succ n) ⁻¹' {h})
        · exact Or.inl ⟨hA, hy⟩
        · exact Or.inr hA
      refine le_trans (measure_mono hcover) (le_trans (measure_union_le _ _) ?_)
      rw [partialTraj_compl_null n h, add_zero]
    rw [hcap, ← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      partialTraj_map_last, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  · rw [if_neg hx]
    refine measure_mono_null (fun y hy => ?_) (partialTraj_compl_null n h)
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx

/-- **The law of a finite history**: the probability of one prescribed history is the product
of the one-step probabilities along it. -/
theorem historyMeasure_singleton (n : ℕ) (x : (i : Finset.Iic n) → Jump N M) :
    biasedHistoryMeasure γ β u n {x}
      = ∏ m ∈ Finset.range (n + 1),
          biasedJumpPMF γ β (stateAfterHistory u x m) (ofHistoryPath x m) := by
  induction n with
  | zero =>
      have h0 : biasedHistoryMeasure γ β u 0
          = (biasedJumpPMF γ β u).toMeasure.map toHistoryZero := by
        unfold biasedHistoryMeasure
        rw [Kernel.partialTraj_self, Measure.id_comp]
      have hpre : toHistoryZero ⁻¹' ({x} : Set ((i : Finset.Iic 0) → Jump N M))
          = ({ofHistoryPath x 0} : Set (Jump N M)) := by
        ext z
        constructor
        · intro hz
          have := congrFun hz ⟨0, Finset.mem_Iic.2 le_rfl⟩
          simpa [ofHistoryPath] using this
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          funext i
          have hi : i = (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0) :=
            Subtype.ext (Nat.le_zero.1 (Finset.mem_Iic.1 i.2))
          rw [hi, hz]
          rfl
      rw [h0, Measure.map_apply measurable_toHistoryZero (measurableSet_singleton x), hpre,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Finset.prod_range_one]
      rfl
  | succ n ih =>
      have hstep : biasedHistoryMeasure γ β u (n + 1) {x}
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (biasedDrivingKernel γ β u) n (n + 1) h {x}
              ∂(biasedHistoryMeasure γ β u n) := by
        unfold biasedHistoryMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _)]
      set h₀ := Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x with hh₀
      have hind : (fun h : (i : Finset.Iic n) → Jump N M =>
            Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (biasedDrivingKernel γ β u) n (n + 1) h {x})
          = Set.indicator {h₀} (fun _ =>
              biasedJumpPMF γ β (stateAfterHistory u h₀ (n + 1))
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)) := by
        funext h
        rw [partialTraj_singleton n h x]
        by_cases hc : h = h₀
        · rw [if_pos hc.symm, Set.indicator_of_mem (Set.mem_singleton_iff.2 hc), hc]
        · rw [if_neg fun hh => hc hh.symm, Set.indicator_of_notMem (by simpa using hc)]
      have hlhs : biasedHistoryMeasure γ β u (n + 1) {x}
          = biasedJumpPMF γ β (stateAfterHistory u h₀ (n + 1))
              (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
            * ∏ m ∈ Finset.range (n + 1),
                biasedJumpPMF γ β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m) := by
        rw [hstep, hind, lintegral_indicator (measurableSet_singleton h₀), setLIntegral_const,
          ih h₀]
      have hprod : ∀ m ∈ Finset.range (n + 1),
          biasedJumpPMF γ β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m)
            = biasedJumpPMF γ β (stateAfterHistory u x m) (ofHistoryPath x m) := by
        intro m hm
        have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        have h1 : stateAfterHistory u h₀ m = stateAfterHistory u x m :=
          (stateAfter_ofHistoryPath_eq (hx := hh₀.symm) u (k := m) (by omega)).symm
        have h2 : ofHistoryPath h₀ m = ofHistoryPath x m :=
          (ofHistoryPath_eq (hx := hh₀.symm) hmn).symm
        rw [h1, h2]
      have hlast : biasedJumpPMF γ β (stateAfterHistory u h₀ (n + 1))
          (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
          = biasedJumpPMF γ β (stateAfterHistory u x (n + 1)) (ofHistoryPath x (n + 1)) := by
        rw [ofHistoryPath_apply x (le_refl (n + 1)),
          show stateAfterHistory u h₀ (n + 1) = stateAfterHistory u x (n + 1) from
            (stateAfter_ofHistoryPath_eq (hx := hh₀.symm) u (k := n + 1) le_rfl).symm]
      rw [hlhs, Finset.prod_congr rfl hprod, hlast,
        Finset.prod_range_succ (f := fun m =>
          biasedJumpPMF γ β (stateAfterHistory u x m) (ofHistoryPath x m)) (n := n + 1)]
      ring

/-- **The law of a cylinder**: the probability of following a prescribed sequence of expressed
pairs for `n` steps is exactly the product of the one-step probabilities along it. -/
theorem pathMeasure_cylinder (ζ : ℕ → Jump N M) (n : ℕ) :
    biasedPathMeasure γ β u {ω | ∀ k < n, ω k = ζ k}
      = ∏ m ∈ Finset.range n, biasedJumpPMF γ β (stateAfter u ζ m) (ζ m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have huniv : {ω : ℕ → Jump N M | ∀ k < 0, ω k = ζ k} = Set.univ := by
      ext ω
      simp
    rw [huniv, Finset.range_zero, Finset.prod_empty, measure_univ]
  · obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
    have hset : {ω : ℕ → Jump N M | ∀ k < b + 1, ω k = ζ k}
        = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹'
          {(fun i : Finset.Iic b => ζ (i : ℕ))} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
        Preorder.frestrictLe_apply]
      constructor
      · intro hω i
        exact hω (i : ℕ) (Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2))
      · intro hω k hk
        exact hω ⟨k, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 hk)⟩
    have hmap : (biasedPathMeasure γ β u).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b)
        = biasedHistoryMeasure γ β u b := by
      unfold biasedHistoryMeasure biasedPathMeasure
      rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe b),
        Kernel.traj_map_frestrictLe]
    rw [hset, ← Measure.map_apply (Preorder.measurable_frestrictLe b)
      (measurableSet_singleton _), hmap, historyMeasure_singleton]
    refine Finset.prod_congr rfl fun m hm => ?_
    have hmb : m ≤ b := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hpath : ∀ j ≤ b, ofHistoryPath (fun i : Finset.Iic b => ζ (i : ℕ)) j = ζ j :=
      fun j hj => by rw [ofHistoryPath_apply _ hj]
    have hstate : stateAfterHistory u (fun i : Finset.Iic b => ζ (i : ℕ)) m = stateAfter u ζ m :=
      stateAfter_congr u m fun j hj => hpath j (by omega)
    rw [hstate, hpath m hmb]

end Iterate

/-! ### The Markov property at a deterministic time

The proof of Theorem 4 invokes "the strong Markov property at time `T_N`".  For the skeleton
`T_N` is the deterministic index `N` — everything in that argument is about the sequence
`(A_m)` — so what is needed there is the *simple* Markov property, which is what this section
proves.  The genuine stopping times of the argument are the failure times, and the strong
Markov property at those is obtained further down by decomposing over their countably many
values, which is the standard discrete-time argument. -/

section Markov

variable {γ β : ℝ}

omit [NeZero N] [NeZero M] in
theorem measurableSet_cylinderPath (ζ : ℕ → Jump N M) (n : ℕ) :
    MeasurableSet {ω : ℕ → Jump N M | ∀ k < n, ω k = ζ k} := by
  have h : {ω : ℕ → Jump N M | ∀ k < n, ω k = ζ k}
      = ⋂ k ∈ Finset.range n, {ω : ℕ → Jump N M | ω k = ζ k} := by
    ext ω
    simp
  rw [h]
  refine MeasurableSet.biInter (Finset.range n).countable_toSet fun k _ => ?_
  show MeasurableSet ((fun ω : ℕ → Jump N M => ω k) ⁻¹' {ζ k})
  exact measurable_pi_apply k (measurableSet_singleton (ζ k))

/-- The realisation shifted by `n` expressions. -/
def shiftPath (n : ℕ) (ω : ℕ → Jump N M) : ℕ → Jump N M := fun i => ω (n + i)

omit [NeZero N] [NeZero M] in
@[simp]
theorem shiftPath_apply (n : ℕ) (ω : ℕ → Jump N M) (i : ℕ) : shiftPath n ω i = ω (n + i) := rfl

omit [NeZero N] [NeZero M] in
theorem measurable_shiftPath (n : ℕ) : Measurable (shiftPath (N := N) (M := M) n) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (n + i)

omit [NeZero N] [NeZero M] in
/-- The profile after `n + i` expressions is the one the shifted realisation reaches in `i`
expressions from the profile after `n`. -/
theorem stateAfter_add (u : Profile N M) (ω : ℕ → Jump N M) (n i : ℕ) :
    stateAfter u ω (n + i) = stateAfter (stateAfter u ω n) (shiftPath n ω) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show n + (i + 1) = n + i + 1 by ring, stateAfter_succ, ih, stateAfter_succ]
      rfl

/-- The realisation that follows `ζ` for `n` expressions and `w` afterwards. -/
def concatPath (n : ℕ) (ζ w : ℕ → Jump N M) : ℕ → Jump N M :=
  fun k => if k < n then ζ k else w (k - n)

omit [NeZero N] [NeZero M] in
theorem concatPath_of_lt {n : ℕ} (ζ w : ℕ → Jump N M) {k : ℕ} (hk : k < n) :
    concatPath n ζ w k = ζ k := if_pos hk

omit [NeZero N] [NeZero M] in
theorem concatPath_add (n : ℕ) (ζ w : ℕ → Jump N M) (i : ℕ) :
    concatPath n ζ w (n + i) = w i := by
  rw [concatPath, if_neg (by omega)]
  congr 1
  omega

omit [NeZero N] [NeZero M] in
@[simp]
theorem shiftPath_concatPath (n : ℕ) (ζ w : ℕ → Jump N M) :
    shiftPath n (concatPath n ζ w) = w :=
  funext fun i => concatPath_add n ζ w i

omit [NeZero N] [NeZero M] in
theorem stateAfter_concatPath (u : Profile N M) (n : ℕ) (ζ w : ℕ → Jump N M) :
    stateAfter u (concatPath n ζ w) n = stateAfter u ζ n :=
  stateAfter_congr u n fun _ hj => concatPath_of_lt ζ w hj

omit [NeZero N] [NeZero M] in
/-- Following `ζ` for `n` steps and then `w` for `c` more is following the concatenation for
`n + c`. -/
theorem cylinder_inter_shift (n c : ℕ) (ζ w : ℕ → Jump N M) :
    ({ω : ℕ → Jump N M | ∀ k < n, ω k = ζ k} ∩
        shiftPath n ⁻¹' {ω : ℕ → Jump N M | ∀ k < c, ω k = w k})
      = {ω : ℕ → Jump N M | ∀ k < n + c, ω k = concatPath n ζ w k} := by
  ext ω
  constructor
  · rintro ⟨h1, h2⟩ k hk
    by_cases hkn : k < n
    · rw [h1 k hkn, concatPath_of_lt ζ w hkn]
    · have hk' : k - n < c := by omega
      have h3 := h2 (k - n) hk'
      rw [shiftPath_apply, show n + (k - n) = k by omega] at h3
      rw [h3, concatPath, if_neg hkn]
  · intro hω
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hω k (by omega), concatPath_of_lt ζ w hk]
    · rw [shiftPath_apply, hω (n + k) (by omega), concatPath_add]

/-- The restart identity on cylinders. -/
theorem pathMeasure_cylinder_restart (u : Profile N M) (ζ w : ℕ → Jump N M) (n c : ℕ) :
    biasedPathMeasure γ β u ({ω | ∀ k < n, ω k = ζ k} ∩
        shiftPath n ⁻¹' {ω | ∀ k < c, ω k = w k})
      = biasedPathMeasure γ β u {ω | ∀ k < n, ω k = ζ k}
        * biasedPathMeasure γ β (stateAfter u ζ n) {ω | ∀ k < c, ω k = w k} := by
  rw [cylinder_inter_shift, pathMeasure_cylinder, pathMeasure_cylinder, pathMeasure_cylinder,
    Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun m hm => ?_
    have hmn : m < n := Finset.mem_range.1 hm
    rw [stateAfter_congr u m fun _ hj => concatPath_of_lt ζ w (by omega),
      concatPath_of_lt ζ w hmn]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [stateAfter_add, shiftPath_concatPath, stateAfter_concatPath, concatPath_add]

omit [NeZero N] [NeZero M] in
/-- A cylinder is the preimage of a singleton history. -/
theorem cylinder_eq_frestrictLe (b : ℕ) (h : (i : Finset.Iic b) → Jump N M) :
    Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h}
      = {ω : ℕ → Jump N M | ∀ k < b + 1, ω k = ofHistoryPath h k} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff,
    Preorder.frestrictLe_apply]
  constructor
  · intro hω k hk
    rw [ofHistoryPath_apply h (Nat.lt_succ_iff.1 hk)]
    exact hω ⟨k, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 hk)⟩
  · intro hω i
    rw [hω (i : ℕ) (Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)),
      ofHistoryPath_apply h (Finset.mem_Iic.1 i.2)]

/-- **The Markov property at a deterministic time.**  Given that the first `n` expressed pairs
are those of `ζ`, the rest of the realisation is a realisation of the chain started at the
profile reached then.

**No counterpart in the paper**, which uses it as "the strong Markov property at `T_N`". -/
theorem pathMeasure_restart (u : Profile N M) (ζ : ℕ → Jump N M) (n : ℕ)
    {E : Set (ℕ → Jump N M)} (hE : MeasurableSet E) :
    biasedPathMeasure γ β u ({ω | ∀ k < n, ω k = ζ k} ∩ shiftPath n ⁻¹' E)
      = biasedPathMeasure γ β u {ω | ∀ k < n, ω k = ζ k}
        * biasedPathMeasure γ β (stateAfter u ζ n) E := by
  classical
  set A : Set (ℕ → Jump N M) := {ω | ∀ k < n, ω k = ζ k} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_cylinderPath ζ n
  set μ₁ : Measure (ℕ → Jump N M) :=
    ((biasedPathMeasure γ β u).restrict A).map (shiftPath n) with hμ₁def
  set μ₂ : Measure (ℕ → Jump N M) :=
    (biasedPathMeasure γ β u A) • biasedPathMeasure γ β (stateAfter u ζ n) with hμ₂def
  have hμ₁apply : ∀ F : Set (ℕ → Jump N M), MeasurableSet F →
      μ₁ F = biasedPathMeasure γ β u (A ∩ shiftPath n ⁻¹' F) := by
    intro F hF
    rw [hμ₁def, Measure.map_apply (measurable_shiftPath n) hF,
      Measure.restrict_apply (measurable_shiftPath n hF), Set.inter_comm]
  have hμ₂apply : ∀ F : Set (ℕ → Jump N M),
      μ₂ F = biasedPathMeasure γ β u A * biasedPathMeasure γ β (stateAfter u ζ n) F := by
    intro F
    rw [hμ₂def, Measure.smul_apply, smul_eq_mul]
  have : IsFiniteMeasure μ₁ := ⟨by
    rw [hμ₁apply Set.univ MeasurableSet.univ, Set.preimage_univ, Set.inter_univ]
    exact measure_lt_top _ _⟩
  have hkey : μ₁ = μ₂ := by
    refine MeasureTheory.ext_of_generate_finite
      {s : Set (ℕ → Jump N M) | ∃ (b : ℕ) (T : Set ((i : Finset.Iic b) → Jump N M)),
        s = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' T} ?_ ?_ ?_ ?_
    · refine le_antisymm (iSup_le fun i => ?_) (MeasurableSpace.generateFrom_le ?_)
      · rintro s ⟨T, -, rfl⟩
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨i, (fun h : (j : Finset.Iic i) → Jump N M =>
            h ⟨i, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' T, rfl⟩
      · rintro s ⟨b, T, rfl⟩
        exact Preorder.measurable_frestrictLe b MeasurableSet.of_discrete
    · rintro s ⟨b, T, rfl⟩ t ⟨b', T', rfl⟩ -
      rcases le_total b b' with hbb | hbb
      · exact ⟨b', (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) hbb ⁻¹' T) ∩ T',
          by rw [Set.preimage_inter, ← Set.preimage_comp]; rfl⟩
      · exact ⟨b, T ∩ (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) hbb ⁻¹' T'),
          by rw [Set.preimage_inter, ← Set.preimage_comp]; rfl⟩
    · rintro s ⟨b, T, rfl⟩
      have hsingle : ∀ h : (i : Finset.Iic b) → Jump N M,
          μ₁ (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h})
            = μ₂ (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h}) := by
        intro h
        rw [cylinder_eq_frestrictLe, hμ₁apply _ (measurableSet_cylinderPath _ _), hμ₂apply,
          hAdef, pathMeasure_cylinder_restart]
      have hmapeq : μ₁.map (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b)
          = μ₂.map (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b) := by
        refine Measure.ext_of_singleton fun h => ?_
        rw [Measure.map_apply (Preorder.measurable_frestrictLe b) (measurableSet_singleton h),
          Measure.map_apply (Preorder.measurable_frestrictLe b) (measurableSet_singleton h)]
        exact hsingle h
      rw [← Measure.map_apply (Preorder.measurable_frestrictLe b)
          (MeasurableSet.of_discrete : MeasurableSet T),
        ← Measure.map_apply (Preorder.measurable_frestrictLe b)
          (MeasurableSet.of_discrete : MeasurableSet T), hmapeq]
    · rw [hμ₁apply Set.univ MeasurableSet.univ, hμ₂apply, Set.preimage_univ, Set.inter_univ,
        measure_univ, mul_one]
  rw [← hμ₁apply E hE, hkey, hμ₂apply]

omit [NeZero N] [NeZero M] in
theorem measurableSet_frestrictLe_preimage (b : ℕ)
    (S : Set ((i : Finset.Iic b) → Jump N M)) :
    MeasurableSet (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' S) :=
  Preorder.measurable_frestrictLe b MeasurableSet.of_discrete

/-- An event decided by the first `b + 1` expressed pairs splits into the histories it
admits. -/
theorem measure_frestrictLe_eq_sum (u : Profile N M) (b : ℕ)
    (S : Finset ((i : Finset.Iic b) → Jump N M)) :
    biasedPathMeasure γ β u
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
      = ∑ h ∈ S, biasedPathMeasure γ β u
          (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h}) := by
  have hdecomp : (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
      = ⋃ h ∈ S, (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h}) := by
    ext ω
    simp
  have hdisj : (S : Set ((i : Finset.Iic b) → Jump N M)).PairwiseDisjoint
      fun h => Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h} := by
    intro h _ h' _ hne
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hω hω'
    rw [← hω, ← hω']
  rw [hdecomp, measure_biUnion_finset hdisj fun h _ => measurableSet_frestrictLe_preimage b _]

/-- **The restart, decomposed.**  The probability that the first `b + 1` expressed pairs form
a history of `S` and that the rest of the realisation lies in `E` is the sum over `S` of the
probability of the history times the probability of `E` from the profile it reaches. -/
theorem measure_inter_shift_eq_sum (u : Profile N M) (b : ℕ)
    (S : Finset ((i : Finset.Iic b) → Jump N M)) {E : Set (ℕ → Jump N M)}
    (hE : MeasurableSet E) :
    biasedPathMeasure γ β u
        ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
          ∩ shiftPath (b + 1) ⁻¹' E)
      = ∑ h ∈ S, biasedPathMeasure γ β u
            (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h})
          * biasedPathMeasure γ β (stateAfterHistory u h (b + 1)) E := by
  have hdecomp : ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
        ∩ shiftPath (b + 1) ⁻¹' E)
      = ⋃ h ∈ S, ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h})
          ∩ shiftPath (b + 1) ⁻¹' E) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Finset.mem_coe, Set.mem_iUnion,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, rfl, h2⟩
    · rintro ⟨h, hh, hrfl, h2⟩
      exact ⟨hrfl ▸ hh, h2⟩
  have hdisj : (S : Set ((i : Finset.Iic b) → Jump N M)).PairwiseDisjoint
      fun h => (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h})
        ∩ shiftPath (b + 1) ⁻¹' E := by
    intro h _ h' _ hne
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    have e1 : Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ω = h := hω.1
    have e2 : Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ω = h' := hω'.1
    rw [← e1, ← e2]
  have hmeas : ∀ h ∈ S, MeasurableSet
      ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' {h})
        ∩ shiftPath (b + 1) ⁻¹' E) :=
    fun h _ => (measurableSet_frestrictLe_preimage b _).inter (measurable_shiftPath (b + 1) hE)
  rw [hdecomp, measure_biUnion_finset hdisj hmeas]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hres := pathMeasure_restart (γ := γ) (β := β) u (ofHistoryPath h) (b + 1) hE
  rwa [← cylinder_eq_frestrictLe b h] at hres

/-- The restart, as the lower bound the argument uses. -/
theorem le_measure_inter_shift (u : Profile N M) (b : ℕ)
    (S : Finset ((i : Finset.Iic b) → Jump N M)) {E : Set (ℕ → Jump N M)}
    (hE : MeasurableSet E) {c : ℝ≥0∞}
    (hc : ∀ h ∈ S, c ≤ biasedPathMeasure γ β (stateAfterHistory u h (b + 1)) E) :
    c * biasedPathMeasure γ β u
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
      ≤ biasedPathMeasure γ β u
        ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
          ∩ shiftPath (b + 1) ⁻¹' E) := by
  rw [measure_frestrictLe_eq_sum, measure_inter_shift_eq_sum u b S hE, Finset.mul_sum]
  refine Finset.sum_le_sum fun h hh => ?_
  rw [mul_comm c]
  gcongr
  exact hc h hh

/-- The restart, as the upper bound the argument uses. -/
theorem measure_inter_shift_le (u : Profile N M) (b : ℕ)
    (S : Finset ((i : Finset.Iic b) → Jump N M)) {E : Set (ℕ → Jump N M)}
    (hE : MeasurableSet E) {q : ℝ≥0∞}
    (hq : ∀ h ∈ S, biasedPathMeasure γ β (stateAfterHistory u h (b + 1)) E ≤ q) :
    biasedPathMeasure γ β u
        ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _))
          ∩ shiftPath (b + 1) ⁻¹' E)
      ≤ q * biasedPathMeasure γ β u
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ⁻¹' (S : Set _)) := by
  rw [measure_frestrictLe_eq_sum, measure_inter_shift_eq_sum u b S hE, Finset.mul_sum]
  refine Finset.sum_le_sum fun h hh => ?_
  rw [mul_comm q]
  gcongr
  exact hq h hh

/-! ### The event that a single actor expresses from some time on -/

/-- `⋂_{m ≥ n} {A_m = A_n}`: from the `n`-th expression on, a single actor expresses. -/
def sameFrom (n : ℕ) : Set (ℕ → Jump N M) := {ω | ∀ m, n ≤ m → (ω m).1 = (ω n).1}

omit [NeZero N] [NeZero M] in
theorem measurableSet_sameFrom (n : ℕ) : MeasurableSet (sameFrom (N := N) (M := M) n) := by
  have h : sameFrom (N := N) (M := M) n
      = ⋂ m : ℕ, ⋂ _ : n ≤ m, {ω : ℕ → Jump N M | (ω m).1 = (ω n).1} := by
    ext ω
    simp [sameFrom]
  rw [h]
  refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_eq_fun
    ((Measurable.of_discrete (f := fun p : Jump N M => p.1)).comp (measurable_pi_apply m))
    ((Measurable.of_discrete (f := fun p : Jump N M => p.1)).comp (measurable_pi_apply n))

omit [NeZero N] [NeZero M] in
theorem sameFrom_eq_preimage (n : ℕ) :
    sameFrom (N := N) (M := M) n = shiftPath n ⁻¹' sameFrom 0 := by
  ext ω
  simp only [sameFrom, Set.mem_ofPred_eq, Set.mem_preimage, shiftPath_apply, Nat.add_zero,
    Nat.zero_le, forall_const]
  constructor
  · intro hω m
    exact hω (n + m) (by omega)
  · intro hω m hm
    have h := hω (m - n)
    rwa [show n + (m - n) = m by omega] at h

end Markov

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
    biasedGreedyEvents γ u m = stepEvents (fun _ => biasedArgmaxFinset γ) u m := by
  ext ω
  simp only [biasedGreedyEvents, stepEvents, Set.mem_ofPred_eq]
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
    nearGreedyEvents γ u m = stepEvents (fun _ => nearArgmaxFinset γ) u m := by
  ext ω
  simp only [nearGreedyEvents, stepEvents, Set.mem_ofPred_eq]
  exact ⟨fun hω k hk => (isNearGreedyAt_iff_mem γ u ω k).1 (hω k hk),
    fun hω k hk => (isNearGreedyAt_iff_mem γ u ω k).2 (hω k hk)⟩

/-- **Proposition 24.**  `P (⋂_{j=1}^{m} ξ̃_j^{α,u}) ≥ (ζ_{α,β})^m`.

**Follows the paper's proof of Proposition 8**, which Appendix C invokes for this statement.
The lattice gap `1/(M-1)` is replaced by the slack `1/(2γ)` that the event `ξ̃` carries — the
substitution Remark 7 is designed for, the entries of the biased model no longer lying on a
lattice. -/
theorem biasedZeta_pow_le (_hM : 2 ≤ M) (_hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β)
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

omit [NeZero N] [NeZero M] in
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

omit [NeZero N] [NeZero M] in
/-- Replaying a realisation is a measurable function of it: the profile after `k` expressions
reads only the first `k + 1` steps, which live in a finite discrete space.

**No counterpart in the paper**, which does not address measurability.  This is
`SocialNetwork.measurable_state_ofStepPath` for the biased model, and it goes through the
same truncation `SocialNetwork.Bias.stateAfter_ofHistoryPath_frestrictLe` as the greedy
events. -/
theorem measurable_stateAfter_ofStepPath (u : Profile N M) (k : ℕ) :
    Measurable fun ω : ℕ → Step N M => stateAfter u (fun n => (ω n).1) k := by
  have h : (fun ω : ℕ → Step N M => stateAfter u (fun n => (ω n).1) k)
      = (fun h : (i : Finset.Iic k) → Jump N M => stateAfterHistory u h k) ∘
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) k) ∘
        fun ω : ℕ → Step N M => fun n => (ω n).1 :=
    funext fun ω =>
      (stateAfter_ofHistoryPath_frestrictLe u (fun n => (ω n).1) (Nat.le_succ k)).symm
  rw [h]
  have hjumps : Measurable fun ω : ℕ → Step N M => fun n => (ω n).1 :=
    measurable_pi_lambda (fun ω : ℕ → Step N M => fun n => (ω n).1) fun n =>
      (measurable_fst (α := Jump N M) (β := ℝ)).comp (measurable_pi_apply n)
  have hhist : Measurable fun h : (i : Finset.Iic k) → Jump N M => stateAfterHistory u h k :=
    Measurable.of_discrete
  exact hhist.comp ((Preorder.measurable_frestrictLe k).comp hjumps)

omit [NeZero N] [NeZero M] in
/-- The biased hitting time is a measurable function of the realisation.

**No counterpart in the paper.**  The biased process has the same jump--hold shape as the
unbiased one, so this is `SocialNetwork.measurable_hittingTimeCts` with
`SocialNetwork.Bias.stateAfter` in place of `SocialNetwork.Trajectory.state`; the countable
reduction `SocialNetwork.sInf_image_eq_hittingCandidates` is shared and knows nothing about
either model. -/
theorem measurable_biasedHittingTimeCts (u : Profile N M) (θ : Set (Profile N M)) :
    Measurable (biasedHittingTimeCts (N := N) (M := M) u θ) := by
  have h : biasedHittingTimeCts (N := N) (M := M) u θ
      = hittingCandidates (fun k ω => stateAfter u (fun n => (ω n).1) k) θ :=
    funext fun ω =>
      sInf_image_eq_hittingCandidates (fun k ω => stateAfter u (fun n => (ω n).1) k) θ ω
  rw [h]
  exact measurable_hittingCandidates (fun k => measurable_stateAfter_ofStepPath u k) θ

omit [NeZero N] [NeZero M] in
/-- Hitting a larger set happens no later. -/
theorem biasedHittingTimeCts_mono (u : Profile N M) {θ₁ θ₂ : Set (Profile N M)} (h : θ₁ ⊆ θ₂)
    (ω : ℕ → Step N M) :
    biasedHittingTimeCts u θ₂ ω ≤ biasedHittingTimeCts u θ₁ ω := by
  refine sInf_le_sInf ?_
  rintro x ⟨t, ⟨ht0, htθ⟩, rfl⟩
  exact ⟨t, ⟨ht0, h htθ⟩, rfl⟩

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
theorem pressure_stateAfter_le_of_biasedGreedy (_hM : 2 ≤ M) (_hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
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
    push Not at hdist
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

/-! #### Proposition 18: the run in which one actor never stops

The paper fixes a starting profile in `B_N^α` whose first row is null — which every `u ∈ S^α`
has, by the first field of `SocialNetwork.Bias.IsBiasedState`, so the paper's "without loss of
generality" is a choice of actor and nothing more — and bounds `P (⋂_{m ≤ n} {A_m = 1})` from
below by decomposing over the word `o₁, …, o_n` that actor expresses, equation (21).  Each
factor of the resulting product is bounded by `(M + λ_m)^{-1}` with the `λ_m` of equation
(22), and the sum over words is the expectation over an i.i.d. uniform word of
`SocialNetwork.uniformSeq`. -/

section Absorption

variable {γ β : ℝ}

/-- The realisation in which the actor `a` expresses the opinions `x 0, x 1, …` and no other
actor ever expresses. -/
def soloPath (a : Actor N) (x : ℕ → Opinion M) : ℕ → Jump N M := fun j => (a, x j)

omit [NeZero N] [NeZero M] in
@[simp]
theorem soloPath_apply (a : Actor N) (x : ℕ → Opinion M) (j : ℕ) :
    soloPath a x j = (a, x j) := rfl

omit [NeZero N] [NeZero M] in
/-- Along `soloPath a x` the expressing actor's memory is reset at every step, so a null row
stays null.  This is the paper's `u (1, o) = 0 for all o`, propagated along the run. -/
theorem heard_stateAfter_soloPath (u : Profile N M) {a : Actor N} (hu : u.heard a = 0)
    (x : ℕ → Opinion M) (m : ℕ) : (stateAfter u (soloPath a x) m).heard a = 0 := by
  cases m with
  | zero => exact hu
  | succ m => rw [stateAfter_succ]; exact Profile.heard_express_self _ _ _

omit [NeZero N] [NeZero M] in
theorem pressure_stateAfter_soloPath_self (u : Profile N M) {a : Actor N} (hu : u.heard a = 0)
    (x : ℕ → Opinion M) (m : ℕ) (p : Opinion M) :
    (stateAfter u (soloPath a x) m).pressure γ a p = 0 :=
  Profile.pressure_eq_zero_of_heard_eq_zero γ (heard_stateAfter_soloPath u hu x m) p

omit [NeZero N] [NeZero M] in
/-- Along `soloPath a x`, every other actor hears exactly the word `x`, so its row is the
initial one shifted by the counts of that word.  This is the profile equation (22) reads. -/
theorem pressure_stateAfter_soloPath_of_ne (u : Profile N M) (a : Actor N)
    (x : ℕ → Opinion M) (m : ℕ) {b : Actor N} (hb : b ≠ a) (p : Opinion M) :
    (stateAfter u (soloPath a x) m).pressure γ b p
      = u.pressure γ b p + ((occCount x p m : ℕ) : ℝ) * (1 + γ) - γ * m := by
  induction m with
  | zero => simp [occCount]
  | succ m ih =>
      rw [stateAfter_succ, soloPath_apply, Profile.pressure_express, if_neg hb, ih,
        occCount_succ]
      by_cases h : p = x m
      · rw [if_pos h, if_pos h.symm]
        push_cast
        ring
      · rw [if_neg h, if_neg fun hh => h hh.symm]
        push_cast
        ring


/-- A lower bound for the probability of a single expressed pair, from a lower bound on its
rate and an upper bound on the total rate. -/
theorem le_biasedJumpPMF_apply (P : Profile N M) (p : Jump N M) {A T : ℝ} (hA : 0 ≤ A)
    (hAle : A ≤ biasedJumpRate γ β P p.1 p.2)
    (hT : (∑ q : Jump N M, biasedJumpRate γ β P q.1 q.2) ≤ T) :
    ENNReal.ofReal (A / T) ≤ biasedJumpPMF γ β P p := by
  have htotpos : (0 : ℝ) < ∑ q : Jump N M, biasedJumpRate γ β P q.1 q.2 :=
    Finset.sum_pos (fun q _ => biasedJumpRate_pos γ β P q.1 q.2) (univ_jump_nonempty N M)
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le htotpos hT
  have hw : (∑' q : Jump N M, biasedJumpWeight γ β P q)
      = ENNReal.ofReal (∑ q : Jump N M, biasedJumpRate γ β P q.1 q.2) := by
    rw [tsum_eq_sum (s := Finset.univ) fun q hq => absurd (Finset.mem_univ q) hq,
      ENNReal.ofReal_sum_of_nonneg fun q _ => (biasedJumpRate_pos γ β P q.1 q.2).le]
    rfl
  rw [biasedJumpPMF_apply, hw, show biasedJumpWeight γ β P p
      = ENNReal.ofReal (biasedJumpRate γ β P p.1 p.2) from rfl,
    ← ENNReal.ofReal_inv_of_pos htotpos,
    ← ENNReal.ofReal_mul (biasedJumpRate_pos γ β P p.1 p.2).le, ← div_eq_mul_inv]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ hTpos htotpos]
  nlinarith [htotpos, (biasedJumpRate_pos γ β P p.1 p.2).le]

/-- **Equation (22)**, `λ_{m+1}`: the rate carried by the actors other than `a`, after `a` has
expressed the first `m` letters of the word `x`, when every entry of the starting profile is
at most `K`. -/
noncomputable def soloOtherRate (N M : ℕ) (γ β K : ℝ) (x : ℕ → Opinion M) (m : ℕ) : ℝ :=
  ((N : ℝ) - 1) * ∑ p : Opinion M,
    Real.exp (β * (K + ((occCount x p m : ℕ) : ℝ) * (1 + γ) - γ * m))

omit [NeZero N] [NeZero M] in
theorem soloOtherRate_nonneg (hN : 1 ≤ N) (γ β K : ℝ) (x : ℕ → Opinion M) (m : ℕ) :
    0 ≤ soloOtherRate N M γ β K x m := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact mul_nonneg (by linarith) (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le)

omit [NeZero N] [NeZero M] in
/-- **The one-step bound behind equation (21).**  When the expressing actor's row is null the
pair it expresses carries rate `1`, and the whole profile carries at most `M + λ`. -/
theorem sum_biasedJumpRate_soloPath_le (hβ : 0 ≤ β) (hN : 1 ≤ N) {u : Profile N M}
    {a : Actor N} (hu : u.heard a = 0) {K : ℝ} (hK : ∀ b p, u.pressure γ b p ≤ K)
    (x : ℕ → Opinion M) (m : ℕ) :
    (∑ q : Jump N M, biasedJumpRate γ β (stateAfter u (soloPath a x) m) q.1 q.2)
      ≤ (M : ℝ) + soloOtherRate N M γ β K x m := by
  have hsplit : (∑ q : Jump N M, biasedJumpRate γ β (stateAfter u (soloPath a x) m) q.1 q.2)
      = ∑ b : Actor N, ∑ p : Opinion M,
          biasedJumpRate γ β (stateAfter u (soloPath a x) m) b p :=
    Fintype.sum_prod_type _
  have hself : (∑ p : Opinion M, biasedJumpRate γ β (stateAfter u (soloPath a x) m) a p)
      = (M : ℝ) := by
    have hone : ∀ p : Opinion M,
        biasedJumpRate γ β (stateAfter u (soloPath a x) m) a p = 1 := fun p => by
      unfold biasedJumpRate
      rw [pressure_stateAfter_soloPath_self u hu x m p, mul_zero, Real.exp_zero]
    rw [Finset.sum_congr rfl fun p _ => hone p]
    simp
  have hother : ∀ b ∈ (Finset.univ : Finset (Actor N)).erase a,
      (∑ p : Opinion M, biasedJumpRate γ β (stateAfter u (soloPath a x) m) b p)
        ≤ ∑ p : Opinion M,
            Real.exp (β * (K + ((occCount x p m : ℕ) : ℝ) * (1 + γ) - γ * m)) := by
    intro b hb
    refine Finset.sum_le_sum fun p _ => ?_
    unfold biasedJumpRate
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hβ)
    rw [pressure_stateAfter_soloPath_of_ne u a x m (Finset.ne_of_mem_erase hb) p]
    have := hK b p
    linarith
  have hfin : (∑ b ∈ (Finset.univ : Finset (Actor N)).erase a,
      ∑ p : Opinion M, biasedJumpRate γ β (stateAfter u (soloPath a x) m) b p)
        ≤ soloOtherRate N M γ β K x m := by
    refine le_trans (Finset.sum_le_sum hother) ?_
    rw [Finset.sum_const, soloOtherRate, nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN, Nat.cast_one]
  rw [hsplit, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hself]
  linarith

theorem inv_le_biasedJumpPMF_soloPath (hβ : 0 ≤ β) (hN : 1 ≤ N) {u : Profile N M}
    {a : Actor N} (hu : u.heard a = 0) {K : ℝ} (hK : ∀ b p, u.pressure γ b p ≤ K)
    (x : ℕ → Opinion M) (m : ℕ) :
    ENNReal.ofReal (((M : ℝ) + soloOtherRate N M γ β K x m)⁻¹)
      ≤ biasedJumpPMF γ β (stateAfter u (soloPath a x) m) (soloPath a x m) := by
  have hA : biasedJumpRate γ β (stateAfter u (soloPath a x) m)
      (soloPath a x m).1 (soloPath a x m).2 = 1 := by
    show Real.exp (β * Profile.pressure γ (stateAfter u (soloPath a x) m) a (x m)) = 1
    rw [pressure_stateAfter_soloPath_self u hu x m (x m), mul_zero, Real.exp_zero]
  have h := le_biasedJumpPMF_apply (γ := γ) (β := β) (stateAfter u (soloPath a x) m)
    (soloPath a x m) zero_le_one hA.ge
    (sum_biasedJumpRate_soloPath_le hβ hN hu hK x m)
  rwa [one_div] at h

/-! ##### The elementary estimates of the proof -/

/-- `M⁻¹ e^{-L} ≤ (M + L)⁻¹`.

**Follows the paper's proof of Proposition 18**: this is its
`ln (1 + x) ≥ x / (1 + x)` at `x = -λ / (M + λ)`, which gives `(M + λ)⁻¹ ≥ M⁻¹ e^{-λ/M}`,
followed by the weakening from `e^{-λ/M}` to `e^{-λ}` that the paper performs on the next
line.  Composed, the two are `M e^L ≥ M + L`. -/
theorem inv_mul_exp_neg_le_inv_add {Mr L : ℝ} (hMr : 1 ≤ Mr) (hL : 0 ≤ L) :
    Mr⁻¹ * Real.exp (-L) ≤ (Mr + L)⁻¹ := by
  have hMpos : (0 : ℝ) < Mr := lt_of_lt_of_le one_pos hMr
  have hsum : (0 : ℝ) < Mr + L := by linarith
  have hexp : Mr + L ≤ Mr * Real.exp L := by
    have h1 : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
    nlinarith
  rw [show Mr⁻¹ * Real.exp (-L) = (Mr * Real.exp L)⁻¹ by rw [mul_inv, Real.exp_neg]]
  exact inv_anti₀ hsum hexp

/-- The product form: `∏_{m < n} (M + λ_m)⁻¹ ≥ M^{-n} e^{-C}` as soon as `∑_{m < n} λ_m ≤ C`.
This is the display following equation (22) in the paper. -/
theorem prod_inv_add_ge {Mr : ℝ} (hMr : 1 ≤ Mr) {l : ℕ → ℝ} (hl : ∀ m, 0 ≤ l m) (n : ℕ)
    {C : ℝ} (hC : ∑ m ∈ Finset.range n, l m ≤ C) :
    Mr⁻¹ ^ n * Real.exp (-C) ≤ ∏ m ∈ Finset.range n, (Mr + l m)⁻¹ := by
  have hMpos : (0 : ℝ) < Mr := lt_of_lt_of_le one_pos hMr
  calc Mr⁻¹ ^ n * Real.exp (-C)
      ≤ Mr⁻¹ ^ n * Real.exp (-∑ m ∈ Finset.range n, l m) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
    _ = ∏ m ∈ Finset.range n, Mr⁻¹ * Real.exp (-(l m)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_sum,
          Finset.sum_neg_distrib]
    _ ≤ ∏ m ∈ Finset.range n, (Mr + l m)⁻¹ :=
        Finset.prod_le_prod (fun m _ => by positivity)
          (fun m _ => inv_mul_exp_neg_le_inv_add hMr (hl m))

/-- A sum whose terms are bounded by a constant below `k` and geometrically above it is
bounded uniformly in the horizon.  This is what makes the right-hand side of the paper's
display (24) finite, and it is where `α < 0` is used: without it the ratio `r` is at least
one. -/
theorem sum_le_of_le_geometric {l : ℕ → ℝ} {D E r : ℝ} (k n : ℕ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hlow : ∀ m, m < n → m < k → l m ≤ D)
    (hhigh : ∀ m, m < n → k ≤ m → l m ≤ E * r ^ m) :
    ∑ m ∈ Finset.range n, l m ≤ (k : ℝ) * D + E * (1 - r)⁻¹ := by
  classical
  have hcard : #(((Finset.range n).filter fun m => m < k)) ≤ k := by
    have hsub : ((Finset.range n).filter fun m => m < k) ⊆ Finset.range k := fun m hm =>
      Finset.mem_range.2 (Finset.mem_filter.1 hm).2
    simpa using Finset.card_le_card hsub
  have h1 : (∑ m ∈ (Finset.range n).filter (fun m => m < k), l m) ≤ (k : ℝ) * D := by
    refine le_trans (Finset.sum_le_sum fun m hm =>
      hlow m (Finset.mem_range.1 (Finset.mem_filter.1 hm).1) (Finset.mem_filter.1 hm).2) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((#(((Finset.range n).filter fun m => m < k)) : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right this hD
  have hgeom : (∑ m ∈ Finset.range n, r ^ m) ≤ (1 - r)⁻¹ := by
    have hsummable : Summable fun m : ℕ => r ^ m := summable_geometric_of_lt_one hr0 hr1
    have hle := hsummable.sum_le_tsum (Finset.range n) (fun m _ => pow_nonneg hr0 m)
    rwa [tsum_geometric_of_lt_one hr0 hr1] at hle
  have h2 : (∑ m ∈ (Finset.range n).filter (fun m => ¬ m < k), l m) ≤ E * (1 - r)⁻¹ := by
    calc (∑ m ∈ (Finset.range n).filter (fun m => ¬ m < k), l m)
        ≤ ∑ m ∈ (Finset.range n).filter (fun m => ¬ m < k), E * r ^ m :=
          Finset.sum_le_sum fun m hm =>
            hhigh m (Finset.mem_range.1 (Finset.mem_filter.1 hm).1)
              (not_lt.1 (Finset.mem_filter.1 hm).2)
      _ ≤ ∑ m ∈ Finset.range n, E * r ^ m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun m _ _ => mul_nonneg hE (pow_nonneg hr0 m))
      _ = E * ∑ m ∈ Finset.range n, r ^ m := by rw [Finset.mul_sum]
      _ ≤ E * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hE
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun m => m < k) l]
  linarith

/-! ##### The events of Proposition 18 -/

omit [NeZero N] [NeZero M] in
theorem measurableSet_forall_lt_fst (a : Actor N) (n : ℕ) :
    MeasurableSet {ω : ℕ → Jump N M | ∀ j < n, (ω j).1 = a} := by
  have h : {ω : ℕ → Jump N M | ∀ j < n, (ω j).1 = a}
      = ⋂ j ∈ Finset.range n, {ω : ℕ → Jump N M | (ω j).1 = a} := by
    ext ω
    simp
  rw [h]
  refine MeasurableSet.biInter (Finset.range n).countable_toSet fun j _ => ?_
  show MeasurableSet ((fun ω : ℕ → Jump N M => (ω j).1) ⁻¹' {a})
  exact ((Measurable.of_discrete (f := fun q : Jump N M => q.1)).comp
    (measurable_pi_apply j)) (measurableSet_singleton a)

end Absorption

/-- **The finite-horizon form of Proposition 18.**  From a profile of `B_N^α` with a null row
`a` — which every profile of `S^α` has — the probability that `a` performs the first `n`
expressions is bounded below uniformly in `n`, in `u` and in `a`.

**Follows the paper's proof of Proposition 18.**  Equation (21) is
`SocialNetwork.Bias.prod_le_pathMeasure_cylinder` summed over the words `f` of length `n`;
each factor is bounded by `(M + λ_m)⁻¹` with the `λ_m` of equation (22)
(`SocialNetwork.Bias.inv_le_biasedJumpPMF_soloPath`); the display after (22) is
`SocialNetwork.Bias.prod_inv_add_ge`; the restriction to `E_ε^k` and the geometric bound
(24) are `SocialNetwork.uniformSeq_freqGood_le` and
`SocialNetwork.Bias.sum_le_of_le_geometric`.

**Supplies a step the paper asserts**: "without loss of generality `u (1, o) = 0` for all
`o`" is the choice of an actor whose row is null, which `IsBiasedState.exists_zero_row`
provides, and the terms of index below `k`, which `E_ε^k` does not control, are bounded by
the crude `λ_m ≤ (N-1) M e^{β (N + k (1+γ))}`. -/
theorem exists_pos_le_pathMeasure_forall_lt_fst (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 1 / ((M : ℝ) - 1) < γ) (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Profile N M, u ∈ biasedBounded N M γ → ∀ a : Actor N,
      u.heard a = 0 → ∀ n : ℕ,
        ENNReal.ofReal c ≤ biasedPathMeasure γ β u {ω | ∀ j < n, (ω j).1 = a} := by
  classical
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hγ0 : (0 : ℝ) < γ := lt_trans (by positivity) hγ
  have h1γ : (0 : ℝ) < 1 + γ := by linarith
  have hgap : (1 : ℝ) < ((M : ℝ) - 1) * γ := by
    rw [div_lt_iff₀ hM1] at hγ
    linarith
  set ε : ℝ := (((M : ℝ) - 1) * γ - 1) / (2 * (M : ℝ) * (1 + γ)) with hεdef
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  set c₀ : ℝ := γ - (((M : ℝ))⁻¹ + ε) * (1 + γ) with hc₀def
  have hc₀eq : c₀ = (((M : ℝ) - 1) * γ - 1) / (2 * (M : ℝ)) := by
    rw [hc₀def, hεdef]
    field_simp
    ring
  have hc₀pos : 0 < c₀ := by
    rw [hc₀eq]
    exact div_pos (by linarith) (by positivity)
  obtain ⟨k, hk⟩ := exists_uniformSeq_freqGood_pos (M := M) hεpos
  set p : ℝ≥0∞ := uniformSeq M (freqGood M ε k) with hpdef
  have hpne : p ≠ ⊤ := measure_ne_top _ _
  have hptoReal : 0 < p.toReal := ENNReal.toReal_pos hk.ne' hpne
  set r : ℝ := Real.exp (-(β * c₀)) with hrdef
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    nlinarith
  set W : ℝ := ((N : ℝ) - 1) * (M : ℝ) with hWdef
  have hW0 : (0 : ℝ) ≤ W := by
    rw [hWdef]
    nlinarith
  set D : ℝ := W * Real.exp (β * ((N : ℝ) + (k : ℝ) * (1 + γ))) with hDdef
  set E : ℝ := W * Real.exp (β * (N : ℝ)) with hEdef
  have hD0 : (0 : ℝ) ≤ D := mul_nonneg hW0 (Real.exp_pos _).le
  have hE0 : (0 : ℝ) ≤ E := mul_nonneg hW0 (Real.exp_pos _).le
  set C : ℝ := (k : ℝ) * D + E * (1 - r)⁻¹ with hCdef
  refine ⟨Real.exp (-C) * p.toReal, by positivity, ?_⟩
  intro u hu a ha n
  have hcyl : ∀ f ∈ freqGoodFinset M ε k n,
      ENNReal.ofReal (((M : ℝ))⁻¹ ^ n * Real.exp (-C))
        ≤ biasedPathMeasure γ β u {ω | ∀ j < n, ω j = soloPath a (extendWord f) j} := by
    intro f hf
    have hlnn : ∀ m : ℕ, 0 ≤ soloOtherRate N M γ β (N : ℝ) (extendWord f) m := fun m =>
      soloOtherRate_nonneg (by omega) _ _ _ _ _
    have hCb : ∑ m ∈ Finset.range n, soloOtherRate N M γ β (N : ℝ) (extendWord f) m ≤ C := by
      refine sum_le_of_le_geometric k n hD0 hE0 hr0 hr1 (fun m _ hmk => ?_)
        (fun m hmn hmk => ?_)
      · have hterm : ∀ q : Opinion M,
            Real.exp (β * ((N : ℝ) + ((occCount (extendWord f) q m : ℕ) : ℝ) * (1 + γ)
                - γ * m))
              ≤ Real.exp (β * ((N : ℝ) + (k : ℝ) * (1 + γ))) := by
          intro q
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hβ.le)
          have h1 : occCount (extendWord f) q m ≤ m := occCount_le _ _ _
          have h3 : ((occCount (extendWord f) q m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
          have h2 : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk.le
          have hoc : ((occCount (extendWord f) q m : ℕ) : ℝ) ≤ (k : ℝ) := by linarith
          have hmul := mul_le_mul_of_nonneg_right hoc h1γ.le
          have hγm : (0 : ℝ) ≤ γ * m := by positivity
          linarith
        calc soloOtherRate N M γ β (N : ℝ) (extendWord f) m
            ≤ ((N : ℝ) - 1) * ∑ _q : Opinion M,
                Real.exp (β * ((N : ℝ) + (k : ℝ) * (1 + γ))) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => hterm q) (by linarith)
          _ = D := by
              rw [hDdef, hWdef, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              ring
      · have hoc : ∀ q : Opinion M,
            ((occCount (extendWord f) q m : ℕ) : ℝ) ≤ (((M : ℝ))⁻¹ + ε) * m :=
          fun q => mem_freqGoodFinset.1 hf m hmn.le hmk q
        have hterm : ∀ q : Opinion M,
            Real.exp (β * ((N : ℝ) + ((occCount (extendWord f) q m : ℕ) : ℝ) * (1 + γ)
                - γ * m))
              ≤ Real.exp (β * (N : ℝ)) * r ^ m := by
          intro q
          have hmul := mul_le_mul_of_nonneg_right (hoc q) h1γ.le
          have hstep : (N : ℝ) + ((occCount (extendWord f) q m : ℕ) : ℝ) * (1 + γ) - γ * m
              ≤ (N : ℝ) + (m : ℝ) * (-c₀) := by
            rw [hc₀def]
            nlinarith [hmul]
          have hexp : β * ((N : ℝ) + ((occCount (extendWord f) q m : ℕ) : ℝ) * (1 + γ)
              - γ * m) ≤ β * (N : ℝ) + (m : ℝ) * (-(β * c₀)) := by
            nlinarith [mul_le_mul_of_nonneg_left hstep hβ.le]
          calc Real.exp (β * ((N : ℝ) + ((occCount (extendWord f) q m : ℕ) : ℝ) * (1 + γ)
                  - γ * m))
              ≤ Real.exp (β * (N : ℝ) + (m : ℝ) * (-(β * c₀))) := Real.exp_le_exp.2 hexp
            _ = Real.exp (β * (N : ℝ)) * r ^ m := by
                rw [Real.exp_add, hrdef, ← Real.exp_nat_mul]
        calc soloOtherRate N M γ β (N : ℝ) (extendWord f) m
            ≤ ((N : ℝ) - 1) * ∑ _q : Opinion M, Real.exp (β * (N : ℝ)) * r ^ m :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => hterm q) (by linarith)
          _ = E * r ^ m := by
              rw [hEdef, hWdef, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              ring
    have hreal : ((M : ℝ))⁻¹ ^ n * Real.exp (-C)
        ≤ ∏ m ∈ Finset.range n,
            ((M : ℝ) + soloOtherRate N M γ β (N : ℝ) (extendWord f) m)⁻¹ :=
      prod_inv_add_ge hMr hlnn n hCb
    refine le_trans ?_ (prod_le_pathMeasure_cylinder (u := u) (soloPath a (extendWord f)) n)
    calc ENNReal.ofReal (((M : ℝ))⁻¹ ^ n * Real.exp (-C))
        ≤ ENNReal.ofReal (∏ m ∈ Finset.range n,
            ((M : ℝ) + soloOtherRate N M γ β (N : ℝ) (extendWord f) m)⁻¹) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∏ m ∈ Finset.range n, ENNReal.ofReal
            (((M : ℝ) + soloOtherRate N M γ β (N : ℝ) (extendWord f) m)⁻¹) :=
          ENNReal.ofReal_prod_of_nonneg fun m _ =>
            inv_nonneg.2 (by have := hlnn m; linarith)
      _ ≤ ∏ m ∈ Finset.range n, biasedJumpPMF γ β
            (stateAfter u (soloPath a (extendWord f)) m) (soloPath a (extendWord f) m) :=
          Finset.prod_le_prod' fun m _ =>
            inv_le_biasedJumpPMF_soloPath hβ.le (by omega) ha hu.2 (extendWord f) m
  have hdisj : (↑(freqGoodFinset M ε k n) : Set (Fin n → Opinion M)).PairwiseDisjoint
      fun f => {ω : ℕ → Jump N M | ∀ j < n, ω j = soloPath a (extendWord f) j} := by
    intro f _ g _ hfg
    refine Set.disjoint_left.2 fun ω hωf hωg => hfg (funext fun i => ?_)
    have h1 : ω (i : ℕ) = (a, extendWord f (i : ℕ)) := hωf (i : ℕ) i.isLt
    have h2 : ω (i : ℕ) = (a, extendWord g (i : ℕ)) := hωg (i : ℕ) i.isLt
    have he : extendWord f (i : ℕ) = extendWord g (i : ℕ) :=
      congrArg Prod.snd (h1.symm.trans h2)
    rwa [extendWord_apply f i.isLt, extendWord_apply g i.isLt] at he
  have hsub : (⋃ f ∈ freqGoodFinset M ε k n,
      {ω : ℕ → Jump N M | ∀ j < n, ω j = soloPath a (extendWord f) j})
      ⊆ {ω : ℕ → Jump N M | ∀ j < n, (ω j).1 = a} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hω
    obtain ⟨f, -, hf⟩ := hω
    exact fun j hj => congrArg Prod.fst (hf j hj)
  calc ENNReal.ofReal (Real.exp (-C) * p.toReal)
      = ENNReal.ofReal (Real.exp (-C)) * p := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hpne]
    _ ≤ ENNReal.ofReal (Real.exp (-C)) *
          ∑ _f ∈ freqGoodFinset M ε k n, ((M : ℝ≥0∞))⁻¹ ^ n := by
        gcongr
        exact uniformSeq_freqGood_le ε k n
    _ = ∑ _f ∈ freqGoodFinset M ε k n,
          ENNReal.ofReal (((M : ℝ))⁻¹ ^ n * Real.exp (-C)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_inv_of_pos hMpos, ENNReal.ofReal_natCast]
        ring
    _ ≤ ∑ f ∈ freqGoodFinset M ε k n, biasedPathMeasure γ β u
          {ω | ∀ j < n, ω j = soloPath a (extendWord f) j} := Finset.sum_le_sum hcyl
    _ = biasedPathMeasure γ β u (⋃ f ∈ freqGoodFinset M ε k n,
          {ω | ∀ j < n, ω j = soloPath a (extendWord f) j}) :=
        (measure_biUnion_finset hdisj fun f _ =>
          measurableSet_cylinderPath (soloPath a (extendWord f)) n).symm
    _ ≤ biasedPathMeasure γ β u {ω | ∀ j < n, (ω j).1 = a} := measure_mono hsub

/-- **Proposition 18.**  For `α < 0`, from any profile in `B_N^α` there is a uniformly positive
chance that a single actor expresses forever after.

**Follows the paper's proof of Proposition 18**: the finite-horizon bound is
`SocialNetwork.Bias.exists_pos_le_pathMeasure_forall_lt_fst`, and the passage to
`⋂_{j ≥ 1} {A_j = A_1}` is continuity from above along the decreasing events. -/
theorem inf_measure_forall_eq_first_pos (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 1 / ((M : ℝ) - 1) < γ) (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Profile N M, u ∈ biasedBounded N M γ →
      ENNReal.ofReal c
        ≤ biasedPathMeasure γ β u {ω | ∀ j, (ω j).1 = (ω 0).1} := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_pathMeasure_forall_lt_fst hM hN hγ hβ
  refine ⟨c, hc, fun u hu => ?_⟩
  obtain ⟨a, ha⟩ := hu.1.exists_zero_row
  have hanti : Antitone fun n : ℕ => {ω : ℕ → Jump N M | ∀ j < n, (ω j).1 = a} := by
    intro m n hmn ω hω j hj
    exact hω j (lt_of_lt_of_le hj hmn)
  have hinter : (⋂ n : ℕ, {ω : ℕ → Jump N M | ∀ j < n, (ω j).1 = a})
      = {ω : ℕ → Jump N M | ∀ j, (ω j).1 = a} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h j => h (j + 1) j (by omega), fun h n j _ => h j⟩
  have hle : ENNReal.ofReal c
      ≤ biasedPathMeasure γ β u {ω : ℕ → Jump N M | ∀ j, (ω j).1 = a} := by
    rw [← hinter,
      hanti.measure_iInter (fun n => (measurableSet_forall_lt_fst a n).nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun n => hbound u hu a ha n
  refine le_trans hle (measure_mono fun ω hω j => ?_)
  rw [hω j, hω 0]

/-- **The uniform bound of Theorem 4 part 1.**  From any profile of `S^α`, a single actor
performs every expression from the `N`-th on, with probability at least `c` uniformly in the
profile.

**Follows the paper's proof of Theorem 4 part 1**, first display: Proposition 17 puts the
profile after `N` expressions in `B_N^α` with probability at least `(NM)^{-N}`, and
Proposition 18 takes over from there.  The paper calls the passage "the strong Markov property
at `T_N`"; for the skeleton `T_N` is the deterministic index `N`, so it is
`SocialNetwork.Bias.le_measure_inter_shift`. -/
theorem exists_pos_le_measure_sameFrom (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ}
    (hγ : 1 / ((M : ℝ) - 1) < γ) (hβ : 0 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : Profile N M, IsBiasedState u →
      ENNReal.ofReal c ≤ biasedPathMeasure γ β u (sameFrom N) := by
  classical
  obtain ⟨c₁, hc₁, hbound⟩ := inf_measure_forall_eq_first_pos hM hN hγ hβ
  have hNM : (0 : ℝ) < ((N * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < N) (by omega : 0 < M)
  refine ⟨c₁ * ((N * M : ℕ) : ℝ) ^ (-(N : ℤ)), mul_pos hc₁ (zpow_pos hNM _), ?_⟩
  intro u hu
  obtain ⟨b, rfl⟩ : ∃ b, N = b + 1 := ⟨N - 1, by omega⟩
  set S : Finset ((i : Finset.Iic b) → Jump (b + 1) M) :=
    Finset.univ.filter fun h =>
      stateAfterHistory u h (b + 1) ∈ biasedBounded (b + 1) M γ with hSdef
  have hst : ∀ ω : ℕ → Jump (b + 1) M,
      stateAfterHistory u (Preorder.frestrictLe (π := fun _ : ℕ => Jump (b + 1) M) b ω) (b + 1)
        = stateAfter u ω (b + 1) :=
    fun ω => stateAfter_ofHistoryPath_frestrictLe u ω (le_refl (b + 1))
  have hA : {ω : ℕ → Jump (b + 1) M | stateAfter u ω (b + 1) ∈ biasedBounded (b + 1) M γ}
      = Preorder.frestrictLe (π := fun _ : ℕ => Jump (b + 1) M) b ⁻¹' (S : Set _) := by
    ext ω
    show stateAfter u ω (b + 1) ∈ biasedBounded (b + 1) M γ ↔ _
    rw [Set.mem_preimage, Finset.mem_coe, hSdef, Finset.mem_filter]
    simp [hst ω]
  have hzero : sameFrom (N := b + 1) (M := M) 0
      = {ω : ℕ → Jump (b + 1) M | ∀ j, (ω j).1 = (ω 0).1} := by
    ext ω
    simp [sameFrom]
  have hc : ∀ h ∈ S, ENNReal.ofReal c₁
      ≤ biasedPathMeasure γ β (stateAfterHistory u h (b + 1)) (sameFrom 0) := by
    intro h hh
    have hmem : stateAfterHistory u h (b + 1) ∈ biasedBounded (b + 1) M γ := by
      rw [hSdef, Finset.mem_filter] at hh
      exact hh.2
    rw [hzero]
    exact hbound _ hmem
  calc ENNReal.ofReal (c₁ * (((b + 1) * M : ℕ) : ℝ) ^ (-((b + 1 : ℕ) : ℤ)))
      = ENNReal.ofReal c₁ * ENNReal.ofReal ((((b + 1) * M : ℕ) : ℝ) ^ (-((b + 1 : ℕ) : ℤ))) :=
        ENNReal.ofReal_mul hc₁.le
    _ ≤ ENNReal.ofReal c₁ * biasedPathMeasure γ β u
          (Preorder.frestrictLe (π := fun _ : ℕ => Jump (b + 1) M) b ⁻¹' (S : Set _)) := by
        gcongr
        rw [← hA]
        exact measure_biasedBounded_ge hM hN hγ hβ.le hu
    _ ≤ biasedPathMeasure γ β u
          ((Preorder.frestrictLe (π := fun _ : ℕ => Jump (b + 1) M) b ⁻¹' (S : Set _))
            ∩ shiftPath (b + 1) ⁻¹' sameFrom 0) :=
        le_measure_inter_shift u b S (measurableSet_sameFrom 0) hc
    _ ≤ biasedPathMeasure γ β u (sameFrom (b + 1)) := by
        refine measure_mono ?_
        rw [sameFrom_eq_preimage (b + 1)]
        exact Set.inter_subset_right

open Classical in
/-- The histories of length `p + 1` on which the first expression after the `N`-th performed by
a different actor happens exactly at `p`.  These are the paper's failure times, read as events
rather than as a random time. -/
noncomputable def breakHistory (N M : ℕ) (p : ℕ) : Finset ((i : Finset.Iic p) → Jump N M) :=
  Finset.univ.filter fun h => N ≤ p ∧ (ofHistoryPath h p).1 ≠ (ofHistoryPath h N).1 ∧
    ∀ m < p, N ≤ m → (ofHistoryPath h m).1 = (ofHistoryPath h N).1

omit [NeZero N] [NeZero M] in
theorem mem_breakEvent (ω : ℕ → Jump N M) (p : ℕ) :
    ω ∈ Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
        (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M))
      ↔ N ≤ p ∧ (ω p).1 ≠ (ω N).1 ∧ ∀ m < p, N ≤ m → (ω m).1 = (ω N).1 := by
  classical
  have hof : ∀ j ≤ p, ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ω) j
      = ω j := fun j hj => by rw [ofHistoryPath_apply _ hj, Preorder.frestrictLe_apply]
  rw [Set.mem_preimage, Finset.mem_coe, breakHistory, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun m hm hNm => ?_⟩
    · rwa [hof p le_rfl, hof N h1] at h2
    · have := h3 m hm hNm
      rwa [hof m hm.le, hof N h1] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, fun m hm hNm => ?_⟩
    · rwa [hof p le_rfl, hof N h1]
    · rw [hof m hm.le, hof N h1]
      exact h3 m hm hNm

/-- **Theorem 4.1.**  For `α < 0`, almost surely all but one actor eventually stop expressing:

```
P (⋃_{n ≥ 1} ⋂_{m ≥ n} {A_n^α = A_m^α}) = 1.
```

**Follows the paper's proof of Theorem 4 part 1, with its recursion run as a single
fixed-point step.**  The paper defines the successive failure times `η_n`, applies the strong
Markov property at each and gets `P (η_{n+1} < ∞) ≤ (1-c) P (η_n < ∞)`, whence
`lim_n P (η_n < ∞) = 0`.  That limit is exactly
`q = sup_{v ∈ S^α} P_v (no actor is eventually alone)`, and the single inequality the
induction uses — the restart at the first failure — gives `q ≤ (1-c) q` in one step, which
forces `q = 0` since `c > 0`.  The estimate, the time it is applied at and the constant are
the paper's; only the bookkeeping of the recursion is replaced by the fixed point it
converges to.

**Supplies a step the paper asserts**: that `{η_n < ∞}` is measurable with respect to the past
at `η_n`, which here is the statement that the failure events are decided by the expressions
that precede them, and is what `SocialNetwork.Bias.mem_breakEvent` records. -/
theorem biasedAbsorption (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 1 / ((M : ℝ) - 1) < γ)
    (hβ : 0 < β) {u : Profile N M} (hu : IsBiasedState u) :
    biasedPathMeasure γ β u {ω | ∃ n, ∀ m, n ≤ m → (ω m).1 = (ω n).1} = 1 := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_measure_sameFrom hM hN hγ hβ
  set absorbed : Set (ℕ → Jump N M) := ⋃ n : ℕ, sameFrom n with habs
  have hmeasAbs : MeasurableSet absorbed :=
    MeasurableSet.iUnion fun n => measurableSet_sameFrom n
  set q : ℝ≥0∞ := ⨆ v ∈ biasedStateSet N M, biasedPathMeasure γ β v absorbedᶜ with hqdef
  have hqle : ∀ v : Profile N M, IsBiasedState v →
      biasedPathMeasure γ β v absorbedᶜ ≤ q := fun v hv =>
    le_iSup₂ (f := fun v (_ : v ∈ biasedStateSet N M) =>
      biasedPathMeasure γ β v absorbedᶜ) v hv
  have hshift : ∀ (j : ℕ) (ω : ℕ → Jump N M), ω ∈ absorbedᶜ → shiftPath j ω ∈ absorbedᶜ := by
    intro j ω hω hmem
    rw [habs, Set.mem_iUnion] at hmem
    obtain ⟨n, hn⟩ := hmem
    refine hω ?_
    rw [habs, Set.mem_iUnion]
    refine ⟨j + n, fun m hm => ?_⟩
    have h1 := hn (m - j) (by omega)
    rw [shiftPath_apply, shiftPath_apply, show j + (m - j) = m by omega] at h1
    exact h1
  have hdisjBreak : Pairwise (Function.onFun Disjoint fun p : ℕ =>
      Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
        (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M))) := by
    have key : ∀ p p' : ℕ, p < p' →
        Disjoint (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
            (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M)))
          (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p' ⁻¹'
            (breakHistory N M p' : Set ((i : Finset.Iic p') → Jump N M))) := by
      intro p p' hlt
      refine Set.disjoint_left.2 fun ω hω hω' => ?_
      obtain ⟨h1, h2, -⟩ := (mem_breakEvent ω p).1 hω
      obtain ⟨-, -, h3⟩ := (mem_breakEvent ω p').1 hω'
      exact h2 (h3 p hlt h1)
    intro p p' hpp
    rcases lt_or_gt_of_ne hpp with h | h
    · exact key p p' h
    · exact (key p' p h).symm
  have hstep : ∀ v : Profile N M, IsBiasedState v →
      biasedPathMeasure γ β v absorbedᶜ ≤ q * (1 - ENNReal.ofReal c) := by
    intro v hv
    have hcover : absorbedᶜ ⊆ ⋃ p : ℕ,
        ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
            (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M)))
          ∩ shiftPath (p + 1) ⁻¹' absorbedᶜ) := by
      intro ω hω
      have hnot : ω ∉ sameFrom (N := N) (M := M) N := fun hmem =>
        hω (by rw [habs]; exact Set.mem_iUnion.2 ⟨N, hmem⟩)
      have hex : ∃ m, N ≤ m ∧ (ω m).1 ≠ (ω N).1 := by
        by_contra hcon
        push Not at hcon
        exact hnot fun m hm => hcon m hm
      have hp := Nat.find_spec hex
      refine Set.mem_iUnion.2 ⟨Nat.find hex, ?_, hshift (Nat.find hex + 1) ω hω⟩
      refine (mem_breakEvent ω (Nat.find hex)).2 ⟨hp.1, hp.2, fun m hm hNm => ?_⟩
      by_contra hne
      have hle : Nat.find hex ≤ m := Nat.find_le ⟨hNm, hne⟩
      omega
    calc biasedPathMeasure γ β v absorbedᶜ
        ≤ ∑' p : ℕ, biasedPathMeasure γ β v
            ((Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
                (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M)))
              ∩ shiftPath (p + 1) ⁻¹' absorbedᶜ) :=
          le_trans (measure_mono hcover) (measure_iUnion_le _)
      _ ≤ ∑' p : ℕ, q * biasedPathMeasure γ β v
            (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
              (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M))) := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          exact measure_inter_shift_le v p (breakHistory N M p) hmeasAbs.compl
            fun h _ => hqle _ (isBiasedState_stateAfter hv (ofHistoryPath h) (p + 1))
      _ = q * ∑' p : ℕ, biasedPathMeasure γ β v
            (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
              (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M))) :=
          ENNReal.tsum_mul_left
      _ = q * biasedPathMeasure γ β v (⋃ p : ℕ,
            Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) p ⁻¹'
              (breakHistory N M p : Set ((i : Finset.Iic p) → Jump N M))) := by
          rw [measure_iUnion hdisjBreak fun p => measurableSet_frestrictLe_preimage p _]
      _ ≤ q * biasedPathMeasure γ β v (sameFrom (N := N) (M := M) N)ᶜ := by
          gcongr
          intro ω hω
          rw [Set.mem_iUnion] at hω
          obtain ⟨p, hp⟩ := hω
          obtain ⟨h1, h2, -⟩ := (mem_breakEvent ω p).1 hp
          exact fun hmem => h2 (hmem p h1)
      _ ≤ q * (1 - ENNReal.ofReal c) := by
          gcongr
          rw [measure_compl (measurableSet_sameFrom N) (measure_ne_top _ _), measure_univ]
          exact tsub_le_tsub_left (hbound v hv) 1
  have hqineq : q ≤ q * (1 - ENNReal.ofReal c) := iSup₂_le fun v hv => hstep v hv
  have hqtop : q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup₂_le fun v _ => prob_le_one)
  have hq0 : q = 0 := by
    by_contra hne
    have hlt : (1 : ℝ≥0∞) - ENNReal.ofReal c < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (by simpa using hc)
    have hmul := ENNReal.mul_lt_mul_left hne hqtop hlt
    rw [one_mul] at hmul
    rw [mul_comm] at hqineq
    exact absurd hqineq (not_le.2 hmul)
  have hzero : biasedPathMeasure γ β u absorbedᶜ = 0 :=
    le_antisymm (hq0 ▸ hqle u hu) zero_le
  have habsorbed : biasedPathMeasure γ β u absorbed = 1 :=
    (prob_compl_eq_zero_iff hmeasAbs).1 hzero
  rw [← habsorbed, habs]
  congr 1
  ext ω
  simp [sameFrom]

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

/-- **Lemma 28.**  `P (R^{α,β,u} (L_α) > 2β) ≤ C e^{-β/(2γ)}`, with `C` depending only on
`α`, `M` and `N`.

**Restated.**  The earlier Lean statement of this lemma was about the skeleton path measure
and the discrete steps `k ≤ ⌈2β⌉` rather than about the continuous-time hitting time
`R^{α,β,u}`, and it bound `C` *after* `β` and `u`, so the constant was free to depend on both.
Neither matches the paper's display, and neither can serve as assumption (16) of the biased
Proposition 12, which is what Lemma 28 exists for.  This is the shape of the unbiased
Lemma 13, `SocialNetwork.probHittingGT_ladderSet_le`, with `1/((M+1)N)` replaced by `1/(2γ)`;
see `FOR-THE-AUTHORS.md`. -/
theorem biasedProbHitting_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ u : Profile N M, IsBiasedState u →
      biasedProbHittingGT γ β u (biasedLadderSet N M γ) (ENNReal.ofReal (2 * β))
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
  obtain ⟨hcpos, hchar⟩ := hc
  have hKpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast Nat.mul_pos (Nat.pow_pos hN0) (Nat.pow_pos (Nat.succ_pos M))
  have h29 := le_biasedProbHittingGT hM hN hγ hγ' hβ
    (isBiasedLadder_biasedLadderOf (N := N) γ o) hcpos
  rw [hchar _ (isBiasedLadder_biasedLadderOf (N := N) γ o)] at h29
  have h' := Real.exp_le_exp.mp
    ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h29)
  rw [neg_div, Real.exp_neg] at h'
  have hFpos : (0 : ℝ) < Real.exp (β / (2 * γ)) := Real.exp_pos _
  have key : (1 : ℝ) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) *
      (Real.exp (β / (2 * γ)))⁻¹ := by linarith
  have hFle : Real.exp (β / (2 * γ)) ≤ 2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right key hFpos.le
    rwa [one_mul, inv_mul_cancel_right₀ hFpos.ne'] at this
  have hKne : ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) ≠ 0 := hKpos.ne'
  have hstep := mul_le_mul_of_nonneg_left hFle
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹)
  rwa [show (1 / 2 : ℝ) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)⁻¹ *
    (2 * c * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) = c by field_simp] at hstep

/-! ### The four assumptions of the biased Proposition 12

Appendix C says only that "the proof of Theorem 31 follows exactly as the proof of Theorem 3",
and does not name the constants.  They are the ones Section 5.3 produces once `1/(M-1)` is
replaced by `1/(2γ)`: the exponent `1/(2γ)` of Lemmas 28 and 29 is halved to `1/(4γ)` to absorb
the factor `β` of step (20), so `δ = θ = 1/(4γ)` here, where the unbiased proof had two
different values.
-/

/-- Assumption **(16)** of the biased Proposition 12, with `s₂ = 2β`.

As in the unbiased model, Lemma 28 is about `L_α` and the assumption is about
`L_α^o ∪ C_α^{-o}`; the two are related by `L_α ⊆ L_α^o ∪ C_α^{-o}`, a biased ladder for
`p ≠ o` being a biased consensus state for `p`. -/
theorem biasedProbHittingGT_ladderOther_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (o : Opinion M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ u : Profile N M, IsBiasedState u →
      biasedProbHittingGT γ β u
          ({v | IsBiasedLadder γ o v} ∪ biasedConsensusSetOther N γ o)
          (ENNReal.ofReal (2 * β))
        ≤ ENNReal.ofReal (C * Real.exp (-β / (2 * γ))) := by
  obtain ⟨C, hC, h28⟩ := biasedProbHitting_le hM hN hγ hγ'
  refine ⟨C, hC, fun β hβ u hu => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_) (h28 β hβ u hu)
  have hsub : biasedLadderSet N M γ
      ⊆ {v | IsBiasedLadder γ o v} ∪ biasedConsensusSetOther N γ o := by
    rintro v ⟨p, hp⟩
    by_cases hpo : p = o
    · exact Or.inl (hpo ▸ hp)
    · exact Or.inr ⟨p, hpo, hp.isBiasedConsensus hγ (by omega)⟩
  exact lt_of_lt_of_le hω (biasedHittingTimeCts_mono u hsub ω)

/-- Assumption **(15)** of the biased Proposition 12, with `s₁ = 1` and
`ε₁ = 2N³(M+1)³e^{-β/(2γ)}`.

Part 1 of Lemma 29 at `t = 1`, read on the complementary event, with `1 - e^{-x} ≤ x`. -/
theorem biasedMeasure_hittingTime_le_one (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β)
    {o : Opinion M} {l : Profile N M} (hl : IsBiasedLadder γ o l) :
    biasedCtsPathMeasure γ β l
        {ω | biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal 1}
      ≤ ENNReal.ofReal (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / (2 * γ))) := by
  set E : ℝ := Real.exp (-β / (2 * γ)) with hE
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hE0 : 0 < E := Real.exp_pos _
  have hmeas : MeasurableSet {ω : ℕ → Step N M |
      ENNReal.ofReal 1 < biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω} :=
    measurableSet_lt measurable_const (measurable_biasedHittingTimeCts l _)
  have hcompl : {ω : ℕ → Step N M |
      biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω ≤ ENNReal.ofReal 1}
      = {ω : ℕ → Step N M |
        ENNReal.ofReal 1 < biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω}ᶜ := by
    ext ω; simp [not_lt]
  have h29 := le_biasedProbHittingGT hM hN hγ hγ' hβ hl (t := 1) one_pos
  rw [show (-2 * (1 : ℝ) * Kc * E) = -(2 * Kc * E) by ring] at h29
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  refine le_trans (tsub_le_tsub_left h29 1) ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.add_one_le_exp (-(2 * Kc * E))
  linarith

/-- Assumption **(18)** of the biased Proposition 12, with `s₂ = 2β`, `θ = 1/(4γ)` and
`K = N²M + 16γe⁻¹N³(M+1)³`.

Part 2 of Lemma 29 at `t = 2β` gives `(N²M + 4βN³(M+1)³) e^{-β/(2γ)}`; splitting the exponent
in half and absorbing `β e^{-β/(4γ)} ≤ 4γ e^{-1}` is step (20) of Section 5.3. -/
theorem biasedMeasure_hittingTime_le_two_mul (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 < β)
    {o : Opinion M} {u : Profile N M} (hu : IsBiasedConsensus γ o u) :
    biasedCtsPathMeasure γ β u
        {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω
          ≤ ENNReal.ofReal (2 * β)}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ)
            + 16 * γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ))
          * Real.exp (-(1 / (4 * γ)) * β)) := by
  refine le_trans
    (biasedProbHittingLE_le hM hN hγ hγ' hβ.le hu (by linarith : (0 : ℝ) < 2 * β))
    (ENNReal.ofReal_le_ofReal ?_)
  have ha : (0 : ℝ) < 4 * γ := by linarith
  have hγ0 : (γ : ℝ) ≠ 0 := hγ.ne'
  set E : ℝ := Real.exp (-β / (4 * γ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  have hexpeq : -β / (4 * γ) + -β / (4 * γ) = -β / (2 * γ) := by field_simp; ring
  have hhalf : Real.exp (-β / (2 * γ)) = E * E := by rw [hE, ← Real.exp_add, hexpeq]
  have hgoal : Real.exp (-(1 / (4 * γ)) * β) = E := by
    rw [hE, show -(1 / (4 * γ)) * β = -β / (4 * γ) by ring]
  rw [hhalf, hgoal]
  have hβE : β * E ≤ (4 * γ) * Real.exp (-1) := mul_exp_neg_div_le ha β
  have hKc : (0 : ℝ) ≤ ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hNM : (0 : ℝ) ≤ ((N ^ 2 * M : ℕ) : ℝ) := by positivity
  have hstep : (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E
      ≤ ((N ^ 2 * M : ℕ) : ℝ)
        + 16 * γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    have hexp : 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * (β * E)
        ≤ 4 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * ((4 * γ) * Real.exp (-1)) :=
      mul_le_mul_of_nonneg_left hβE (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hE1 hNM]
  calc (((N ^ 2 * M : ℕ) : ℝ) + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * (E * E)
      = ((((N ^ 2 * M : ℕ) : ℝ)
          + 2 * (2 * β) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E) * E := by ring
    _ ≤ (((N ^ 2 * M : ℕ) : ℝ)
        + 16 * γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) * E :=
        mul_le_mul_of_nonneg_right hstep hE0.le

/-- Assumption **(17)** of the biased Proposition 12, with `s₂ = 2β`, `δ = 1/(4γ)` and
`C = 16γe⁻¹N³(M+1)³ + C₂₈`.

This is where Corollary 30 enters: it turns `s₂ / c_{α,β}` into `4βN³(M+1)³e^{-β/(2γ)}`, and
half of the exponent absorbs the factor `β`. -/
theorem biasedMax_le_of_isCharacteristicTime (hM : 2 ≤ M) (hN : 3 ≤ N) {γ β : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (hβ : 0 ≤ β) {o : Opinion M} {c : ℝ}
    (hc : IsBiasedCharacteristicTime (N := N) γ β o c) {C : ℝ} (hC : 0 ≤ C) :
    max (2 * β / c) (C * Real.exp (-β / (2 * γ)))
      ≤ (16 * γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + C)
          * Real.exp (-(1 / (4 * γ)) * β) := by
  have ha : (0 : ℝ) < 4 * γ := by linarith
  have hγ0 : (γ : ℝ) ≠ 0 := hγ.ne'
  set Kc : ℝ := ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  set E : ℝ := Real.exp (-β / (4 * γ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE, Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg <;> linarith
  have hexpeq : -β / (4 * γ) + -β / (4 * γ) = -β / (2 * γ) := by field_simp; ring
  have hhalf : Real.exp (-β / (2 * γ)) = E * E := by rw [hE, ← Real.exp_add, hexpeq]
  have hgoal : Real.exp (-(1 / (4 * γ)) * β) = E := by
    rw [hE, show -(1 / (4 * γ)) * β = -β / (4 * γ) by ring]
  have hbig : (0 : ℝ) ≤ 16 * γ * Real.exp (-1) * Kc := by positivity
  rw [hgoal]
  refine max_le ?_ ?_
  · have hcpos : 0 < c := hc.1
    have h30 := le_biasedCharacteristicTime hM hN hγ hγ' hβ hc
    set F : ℝ := Real.exp (β / (2 * γ)) with hF
    have hFpos : 0 < F := Real.exp_pos _
    have hbpos : (0 : ℝ) < 1 / 2 * Kc⁻¹ * F := by positivity
    have hdiv : 2 * β / c ≤ 2 * β / (1 / 2 * Kc⁻¹ * F) :=
      div_le_div_of_nonneg_left (by linarith) hbpos h30
    have hfe : 2 * β / (1 / 2 * Kc⁻¹ * F) = 4 * Kc * (β * E) * E := by
      rw [show 4 * Kc * (β * E) * E = 4 * Kc * β * (E * E) by ring, ← hhalf,
        show -β / (2 * γ) = -(β / (2 * γ)) by ring, Real.exp_neg, ← hF]
      field_simp
      ring
    calc 2 * β / c ≤ 4 * Kc * (β * E) * E := hdiv.trans_eq hfe
      _ ≤ 4 * Kc * ((4 * γ) * Real.exp (-1)) * E :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_exp_neg_div_le ha β) (by positivity)) hE0.le
      _ = 16 * γ * Real.exp (-1) * Kc * E := by ring
      _ ≤ (16 * γ * Real.exp (-1) * Kc + C) * E := by nlinarith
  · calc C * Real.exp (-β / (2 * γ)) = C * E * E := by rw [hhalf]; ring
      _ ≤ C * E := by
          have h := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hC hE0.le)
          linarith
      _ ≤ (16 * γ * Real.exp (-1) * Kc + C) * E := by nlinarith

/-- **Proposition 12 for the biased process**, the consequence for this model of Theorem 5.3
of [LM22].

**This is an axiom, not a theorem, and it is the second one this repository asks you to
trust.**  It is the exact twin of `SocialNetwork.exitTime_approx_exponential`, over
`Profile N M` instead of `Pressure N M`.  Appendix C never states it: it says only that "the
proof of Theorem 31 follows exactly as the proof of Theorem 3", and the proof of Theorem 3
runs through Proposition 12, which is stated for the unbiased process alone.

**One axiom cannot serve both models.**  Stated abstractly — over an arbitrary family of
measures and an arbitrary hitting time — the statement is *inconsistent*: the zero measure
with an empty ladder set satisfies the four assumptions vacuously and falsifies the conclusion
at `t = 0`.  What rules that out is the strong Markov property, which is the content of [LM22]
and is not expressible here, so the statement has to be attached to a concrete process.  The
unbiased axiom is attached to the unbiased one, and this is the price: a second thing to
trust.  See `FOR-THE-AUTHORS.md` §3.

The hypotheses are named after the equations of the paper, and `ε₁ ε₂ s₁ s₂` are functions of
`β` for the reason recorded at the unbiased axiom. -/
axiom biasedExitTime_approx_exponential (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) (o : Opinion M)
    (ε₁ ε₂ s₁ s₂ : ℝ → ℝ) {C δ K θ β₁ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hK : 0 < K) (hθ : 0 < θ)
    (hpos : ∀ β : ℝ, β₁ ≤ β → 0 < ε₁ β ∧ 0 < ε₂ β ∧ 0 < s₁ β ∧ 0 < s₂ β)
    (hsum : ∀ β : ℝ, β₁ ≤ β → ε₁ β + ε₂ β ≤ 1 / 2)
    (h15 : ∀ β : ℝ, β₁ ≤ β → ∀ l : Profile N M, IsBiasedLadder γ o l →
      biasedCtsPathMeasure γ β l
          {ω | biasedHittingTimeCts l (biasedConsensusSetOther N γ o) ω
            ≤ ENNReal.ofReal (s₁ β)}
        ≤ ENNReal.ofReal (ε₁ β))
    (h16 : ∀ β : ℝ, β₁ ≤ β → ∀ u : Profile N M, IsBiasedState u →
      biasedProbHittingGT γ β u
          ({v | IsBiasedLadder γ o v} ∪ biasedConsensusSetOther N γ o)
          (ENNReal.ofReal (s₂ β))
        ≤ ENNReal.ofReal (ε₂ β))
    (h17 : ∀ β : ℝ, β₁ ≤ β → ∀ c : ℝ, IsBiasedCharacteristicTime (N := N) γ β o c →
      max (s₂ β / c) (ε₂ β) ≤ C * Real.exp (-δ * β))
    (h18 : ∀ β : ℝ, β₁ ≤ β → ∀ u : Profile N M, IsBiasedConsensus γ o u →
      biasedCtsPathMeasure γ β u
          {ω | biasedHittingTimeCts u (biasedConsensusSetOther N γ o) ω
            ≤ ENNReal.ofReal (s₂ β)}
        ≤ ENNReal.ofReal (K * Real.exp (-θ * β))) :
    ∃ β₀ K' : ℝ, β₁ ≤ β₀ ∧ 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Profile N M, IsBiasedConsensus γ o u →
      (∀ t : ℝ, 0 ≤ t →
        |(biasedProbHittingGT γ β u (biasedConsensusSetOther N γ o)
            (ENNReal.ofReal t *
              biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)) ∧
      ∀ v : Profile N M, IsBiasedConsensus γ o v →
        |(biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o)).toReal /
            (biasedExpHittingTimeCts γ β v (biasedConsensusSetOther N γ o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min (δ / 3) (1 / 2)) θ * β)

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
  have hKcpos : (0 : ℝ) < ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (Nat.pow_pos (Nat.succ_pos M))
  have hNMpos : (0 : ℝ) < ((N ^ 2 * M : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pow_pos (by omega : 0 < N)) (by omega : 0 < M)
  have hδpos : (0 : ℝ) < 1 / (4 * γ) := by positivity
  have hepos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  -- Proposition 12 for the biased process, opinion by opinion
  have key : ∀ o : Opinion M, ∃ β₀ K' : ℝ, 0 < β₀ ∧ 0 < K' ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ u : Profile N M, IsBiasedConsensus γ o u →
      (∀ t : ℝ, 0 ≤ t →
        |(biasedProbHittingGT γ β u (biasedConsensusSetOther N γ o)
            (ENNReal.ofReal t *
              biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o))).toReal
          - Real.exp (-t)|
        ≤ K' * β ^ 3 * Real.exp (-min (min ((1 / (4 * γ)) / 3) (1 / 2)) (1 / (4 * γ)) * β)) ∧
      ∀ v : Profile N M, IsBiasedConsensus γ o v →
        |(biasedExpHittingTimeCts γ β u (biasedConsensusSetOther N γ o)).toReal /
            (biasedExpHittingTimeCts γ β v (biasedConsensusSetOther N γ o)).toReal - 1|
          ≤ K' * β ^ 3 * Real.exp (-min (min ((1 / (4 * γ)) / 3) (1 / 2)) (1 / (4 * γ)) * β) := by
    intro o
    -- Lemma 28, in the form assumption (16) needs
    obtain ⟨Cl, hCl, h16⟩ := biasedProbHittingGT_ladderOther_le hM hN hγ hγ' o
    -- the threshold above which `ε₁ + ε₂ ≤ 1/2`
    set β₁ : ℝ := max 1 (4 * γ * (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl)) with hβ₁def
    have hβ₁one : (1 : ℝ) ≤ β₁ := le_max_left _ _
    have hpos' : ∀ β : ℝ, β₁ ≤ β → (0 : ℝ) < β := fun β hβ =>
      lt_of_lt_of_le zero_lt_one (le_trans hβ₁one hβ)
    have hsum : ∀ β : ℝ, β₁ ≤ β →
        2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / (2 * γ))
          + Cl * Real.exp (-β / (2 * γ)) ≤ 1 / 2 := by
      intro β hβ
      have hβpos := hpos' β hβ
      have hb : 4 * γ * (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) ≤ β :=
        le_trans (le_max_right _ _) hβ
      have hexp : Real.exp (-β / (2 * γ)) ≤ (2 * γ) / β :=
        exp_neg_div_le (by linarith) hβpos
      have hmul : (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * Real.exp (-β / (2 * γ))
          ≤ (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * ((2 * γ) / β) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
      have hfin : (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * ((2 * γ) / β) ≤ 1 / 2 := by
        rw [show (2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * ((2 * γ) / β)
            = ((2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl) * (2 * γ)) / β by ring,
          div_le_iff₀ hβpos]
        linarith
      linarith
    have hCpos : (0 : ℝ)
        < 16 * γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) + Cl := by positivity
    have hKpos : (0 : ℝ) < ((N ^ 2 * M : ℕ) : ℝ)
        + 16 * γ * Real.exp (-1) * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by positivity
    obtain ⟨b, K', -, hbpos, hK'pos, hmain⟩ :=
      biasedExitTime_approx_exponential hM hN hγ hγ' o
        (fun β => 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / (2 * γ)))
        (fun β => Cl * Real.exp (-β / (2 * γ)))
        (fun _ => 1) (fun β => 2 * β)
        hCpos hδpos hKpos hδpos
        (fun β hβ => ⟨mul_pos (by linarith) (Real.exp_pos _), mul_pos hCl (Real.exp_pos _),
          one_pos, by linarith [hpos' β hβ]⟩)
        hsum
        (fun β hβ l hl =>
          biasedMeasure_hittingTime_le_one hM hN hγ hγ' (hpos' β hβ).le hl)
        (fun β hβ u hu => h16 β (hpos' β hβ).le u hu)
        (fun β hβ c hc =>
          biasedMax_le_of_isCharacteristicTime hM hN hγ hγ' (hpos' β hβ).le hc hCl.le)
        (fun β hβ u hu =>
          biasedMeasure_hittingTime_le_two_mul hM hN hγ hγ' (hpos' β hβ) hu)
    exact ⟨b, K', hbpos, hK'pos, hmain⟩
  -- the constants are uniform over the finitely many opinions
  choose b k hbpos hkpos hmain using key
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ o : Opinion M, b o ≤ B := Finite.exists_le b
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, ∀ o : Opinion M, k o ≤ Kb := Finite.exists_le k
  refine ⟨max B 1, max Kb 1, min (min ((1 / (4 * γ)) / 3) (1 / 2)) (1 / (4 * γ)),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_min (lt_min (by positivity) (by norm_num)) hδpos, ?_⟩
  intro β hβ o u hu
  have hbβ : b o ≤ β := le_trans (hB o) (le_trans (le_max_left _ _) hβ)
  obtain ⟨h1, h2⟩ := hmain o β hbβ u hu
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le (hbpos o) hbβ
  have hfac : (0 : ℝ) ≤ β ^ 3 *
      Real.exp (-min (min ((1 / (4 * γ)) / 3) (1 / 2)) (1 / (4 * γ)) * β) := by positivity
  have hup : k o * β ^ 3 *
        Real.exp (-min (min ((1 / (4 * γ)) / 3) (1 / 2)) (1 / (4 * γ)) * β)
      ≤ max Kb 1 * β ^ 3 *
        Real.exp (-min (min ((1 / (4 * γ)) / 3) (1 / 2)) (1 / (4 * γ)) * β) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_trans (hKb o) (le_max_left _ _)) hfac
  exact ⟨fun t ht => le_trans (h1 t ht) hup, fun v hv => le_trans (h2 v hv) hup⟩

end PositiveBias

end Bias

end SocialNetwork
