/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BandCollapse

/-!
# Theorem 1.1, along [GL24]'s construction

`SocialNetwork.Band` and `SocialNetwork.BandCollapse` build [GL24]'s band and identify the
realisation it carries with the process it drives, for an arbitrary band.  This file
instantiates them for the model of equation (3) and reads off Theorem 1.1.

Two things are needed of the model.

* The band's data: the rates of equation (3), the operators `π^{a,o}`, the pairs whose actor
  carries pressure below `N`, and the bound `λ = NMe^{βN}` on the rate they carry
  (`SocialNetwork.pressureBand`).
* **Lemma 10 of [GL24]**, read on the marks: at least one mark in every `N` lands in the strip
  of height `λ` (`SocialNetwork.exists_isLambdaAt_block`).  A discarded mark does, and if all
  `N` of a block express then Proposition 5 exhibits one whose actor carries pressure
  below `N`.

`SocialNetwork.nonExplosion` is then [GL24]'s conclusion.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### The band of the model of equation (3) -/

/-- [GL24]'s band for the model of equation (3): the rates of the generator, the operators
`π^{a,o}`, the pairs whose actor carries pressure below `N`, and the bound `λ = NMe^{βN}` of
equation (11) on the rate they carry. -/
noncomputable def pressureBand (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) :
    Band N M (Pressure N M) where
  rate v p := jumpRate β v p.1 p.2
  rate_pos v p := jumpRate_pos β v p.1 p.2
  next v p := express p.1 p.2 v
  low := lowFinset
  lam := clockBound N M β
  lam_pos := clockBound_pos N M β
  low_le_lam v := lowRate_le_clockBound hM hβ v

@[simp]
theorem pressureBand_totRate (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    (pressureBand hM hβ).totRate v = totalRate β v := rfl

@[simp]
theorem pressureBand_stepLaw (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    (pressureBand hM hβ).stepLaw v = stepLaw β v := rfl

/-- The band of the model of equation (3) carries the process of equation (3).  Both sides are
the Ionescu-Tulcea measure of the same kernels; this is a matter of unfolding. -/
theorem pressureBand_ctsPath (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M) :
    (pressureBand hM hβ).ctsPath u = ctsPathMeasure β u := by
  have hstate : ∀ (j : ℕ → Jump N M) (n : ℕ),
      stateAfterJumps (pressureBand hM hβ).next u j n = (Trajectory.ofPath j).state u n := by
    intro j n
    induction n with
    | zero => rfl
    | succ n ih => rw [stateAfterJumps_succ, ih, Trajectory.state_succ]; rfl
  have hker : drivenKernel (pressureBand hM hβ).next (pressureBand hM hβ).stepLaw u
      = ctsDrivingKernel β u := by
    funext n
    ext h : 1
    rw [drivenKernel_apply, ctsDrivingKernel_apply, pressureBand_stepLaw]
    exact congrArg _ (hstate _ (n + 1))
  rw [Band.ctsPath, drivenMeasure, jumpHoldMeasure, ctsPathMeasure]
  simp only [hker, pressureBand_stepLaw]
  rfl

/-! ### Lemma 10 of [GL24], read on the marks -/

/-- `S` is preserved along the mark chain: a discarded mark changes nothing, and an expression
is `π^{a,o}`. -/
theorem isState_markState (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M} (hu : IsState u)
    (j : ℕ → MarkJump N M) (n : ℕ) : IsState (markState (pressureBand hM hβ) u j n) := by
  induction n with
  | zero => exact hu
  | succ n ih =>
      rw [markState_succ]
      cases hj : j n with
      | discard => exact ih
      | jump p => exact ih.express p.1 p.2

/-- A run of marks that all express follows the trajectory they spell out. -/
theorem markState_add_of_jumps (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    {j : ℕ → MarkJump N M} {m n : ℕ} {T : Trajectory N M}
    (h : ∀ i < n, j (m + i) = .jump (T.actor i, T.opinion i)) :
    ∀ k ≤ n, markState (pressureBand hM hβ) u j (m + k)
      = T.state (markState (pressureBand hM hβ) u j m) k := by
  intro k
  induction k with
  | zero => intro _; rw [Nat.add_zero, Trajectory.state_zero]
  | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, markState_succ_jump _ u j (h k (by omega)), ih (by omega),
        T.state_succ]
      rfl

/-- **Lemma 10 of [GL24], transported to the marks.**  Among any `N` consecutive marks at least
one lands in the strip of height `λ`: a discarded mark does, and if all `N` express then
Proposition 5 exhibits one whose actor carries pressure below `N`. -/
theorem exists_isLambdaAt_block (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) (j : ℕ → MarkJump N M) (m : ℕ) :
    ∃ k, m * N ≤ k ∧ k < m * N + N ∧ IsLambdaAt (pressureBand hM hβ) u k j := by
  by_cases hdis : ∃ i < N, j (m * N + i) = .discard
  · obtain ⟨i, hiN, hi⟩ := hdis
    exact ⟨m * N + i, by omega, by omega, by
      rw [IsLambdaAt, hi]; exact Finset.mem_insert_self _ _⟩
  · push Not at hdis
    -- every mark of the block expresses; read off the trajectory it spells
    have hjump : ∀ i, i < N → ∃ p : Jump N M, j (m * N + i) = .jump p := by
      intro i hi
      cases hji : j (m * N + i) with
      | discard => exact absurd hji (hdis i hi)
      | jump p => exact ⟨p, rfl⟩
    choose p hp using hjump
    set a₀ : Actor N := ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ with ha₀
    set o₀ : Opinion M := ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩ with ho₀
    set T : Trajectory N M :=
      { actor := fun i => if hi : i < N then (p i hi).1 else a₀
        opinion := fun i => if hi : i < N then (p i hi).2 else o₀ } with hT
    have hstep : ∀ i < N, j (m * N + i) = .jump (T.actor i, T.opinion i) := by
      intro i hi
      rw [hT]
      show j (m * N + i) = .jump ((if h : i < N then (p i h).1 else a₀),
        (if h : i < N then (p i h).2 else o₀))
      rw [dif_pos hi, dif_pos hi, hp i hi]
    obtain ⟨k, hkN, hk⟩ :=
      exists_rowSup_actor_lt T hM (isState_markState hM hβ hu j (m * N))
    refine ⟨m * N + k, by omega, by omega, ?_⟩
    rw [IsLambdaAt, hstep k hkN, mem_lambdaFinset]
    refine Or.inr ⟨(T.actor k, T.opinion k), ?_, rfl⟩
    show _ ∈ lowFinset _
    rw [mem_lowFinset, markState_add_of_jumps hM hβ hstep k hkN.le]
    exact hk

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1.**  For any `β ≥ 0` and any starting matrix `u ∈ S`, the jump times satisfy
`P (sup {Tₘ : m ≥ 1} = ∞) = 1`: the process does not explode.

**Follows the written proof**, which is [GL24] pp. 12–14.  Its Lemma 10 puts at least one mark
in every `N` in the strip of height `λ`, and `λ = NMe^{βN}` bounds the rate the strip carries
whatever the matrix is; so the marks of the band do not accumulate.  The realisation the band
carries is the process (`SocialNetwork.map_markPathMeasure_collapse_eq`), and its jump times
are a sub-sequence of the band's marks, so they are unbounded with them. -/
theorem nonExplosion (hM : 2 ≤ M) (_hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) :
    ctsPathMeasure β u {ω | explosionTime ω = ⊤} = 1 := by
  have h := measure_ctsPath_blowUp (pressureBand hM hβ) (b := N)
    (exists_isLambdaAt_block hM hβ hu)
  rwa [pressureBand_ctsPath] at h

end SocialNetwork
