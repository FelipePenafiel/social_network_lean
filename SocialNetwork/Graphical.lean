/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.NonExplosion

/-!
# The graphical construction of [GL24]

Placeholder header, rewritten at the end.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ}

/-! ### The band of Figure 2 -/

/-- The rate carried by the pairs whose actor is under pressure `≥ N`: the blue region of
[GL24]'s Figure 2, of height `q^>(v)`. -/
noncomputable def highRate (β : ℝ) (v : Pressure N M) : ℝ := totalRate β v - lowRate β v

theorem highRate_nonneg (β : ℝ) (v : Pressure N M) : 0 ≤ highRate β v :=
  sub_nonneg.2 (lowRate_le_totalRate β v)

/-- The height of the band the marks are read in: `λ + q^>(v)`.  Below `λ` sits the strip that
carries the low-pressure pairs and the discarded region; above it, the high-pressure pairs. -/
noncomputable def bandRate (β : ℝ) (v : Pressure N M) : ℝ :=
  clockBound N M β + highRate β v

theorem clockBound_le_bandRate (β : ℝ) (v : Pressure N M) :
    clockBound N M β ≤ bandRate β v := by
  rw [bandRate]
  linarith [highRate_nonneg β v]

theorem bandRate_pos [NeZero N] [NeZero M] (β : ℝ) (v : Pressure N M) : 0 < bandRate β v :=
  lt_of_lt_of_le (clockBound_pos N M β) (clockBound_le_bandRate β v)

/-- A mark of the band, read through the stacking functions of [GL24]: either the pair whose
interval it lands in, or `discard` when it lands in the region `[q^<(v), λ)`, which the
construction skips. -/
inductive MarkJump (N M : ℕ) where
  /-- The mark landed in the discarded region `[q^<(v), λ)`: no expression follows. -/
  | discard : MarkJump N M
  /-- The mark landed in the interval of the pair `p`, which then expresses. -/
  | jump (p : Jump N M) : MarkJump N M
  deriving DecidableEq

instance : Fintype (MarkJump N M) where
  elems := insert MarkJump.discard (Finset.univ.image MarkJump.jump)
  complete := by rintro (_ | p) <;> simp

instance : MeasurableSpace (MarkJump N M) := ⊤

instance : DiscreteMeasurableSpace (MarkJump N M) := ⟨fun _ => trivial⟩

/-- The width of the interval a mark of the band decodes to: the rate of the pair, or the
height `λ - q^<(v)` of the discarded region. -/
noncomputable def markWeight (β : ℝ) (v : Pressure N M) : MarkJump N M → ℝ≥0∞
  | .discard => ENNReal.ofReal (clockBound N M β - lowRate β v)
  | .jump p => ENNReal.ofReal (jumpRate β v p.1 p.2)

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
theorem markWeight_ne_top {β : ℝ} (v : Pressure N M) (m : MarkJump N M) :
    markWeight β v m ≠ ∞ := by
  cases m <;> exact ENNReal.ofReal_ne_top

theorem sum_markWeight (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    ∑' m : MarkJump N M, markWeight β v m = ENNReal.ofReal (bandRate β v) := by
  have hlow : lowRate β v ≤ clockBound N M β := lowRate_le_clockBound hM hβ v
  rw [tsum_fintype, Fintype.sum_eq_add_sum_compl MarkJump.discard,
    show ({MarkJump.discard} : Finset (MarkJump N M))ᶜ
      = Finset.univ.image MarkJump.jump by
      ext m; cases m <;> simp]
  rw [Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p : Jump N M, markWeight β v (MarkJump.jump p)
      = ENNReal.ofReal (totalRate β v) := by
    show ∑ p : Jump N M, ENNReal.ofReal (jumpRate β v p.1 p.2) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le]
    rfl
  rw [hjump]
  show ENNReal.ofReal (clockBound N M β - lowRate β v) + ENNReal.ofReal (totalRate β v) = _
  rw [← ENNReal.ofReal_add (by linarith) (totalRate_pos β v).le]
  congr 1
  rw [bandRate, highRate]
  ring

theorem sum_markWeight_ne_zero (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    (∑' m : MarkJump N M, markWeight β v m) ≠ 0 := by
  rw [sum_markWeight hM hβ v]
  exact (ENNReal.ofReal_pos.2 (bandRate_pos β v)).ne'

theorem sum_markWeight_ne_top (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    (∑' m : MarkJump N M, markWeight β v m) ≠ ∞ := by
  rw [sum_markWeight hM hβ v]
  exact ENNReal.ofReal_ne_top

/-- **The law of one mark of the band**: a uniform point of `[0, λ + q^>(v))` decodes to the
pair whose interval it lands in, or to `none` when it lands in the discarded region.  The
stacking functions of [GL24] make the decoding explicit; what the argument uses of them is
that each interval has the width of its rate, which is this law. -/
noncomputable def markPMF (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    PMF (MarkJump N M) :=
  PMF.normalize (markWeight β v) (sum_markWeight_ne_zero hM hβ v) (sum_markWeight_ne_top hM hβ v)

theorem markPMF_apply (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) (m : MarkJump N M) :
    markPMF hM hβ v m = markWeight β v m * (∑' q : MarkJump N M, markWeight β v q)⁻¹ := rfl

/-- The law of one step of the mark chain: the decoded mark, and the time until the next mark
of the band, which is exponential of the band's height. -/
noncomputable def markLaw (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    Measure (Hold (MarkJump N M)) :=
  (markPMF hM hβ v).toMeasure.prod (expMeasure (bandRate β v))

instance isProbabilityMeasure_markLaw (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    IsProbabilityMeasure (markLaw hM hβ v) := by
  have : IsProbabilityMeasure (expMeasure (bandRate β v)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos β v)
  exact Measure.prod.instIsProbabilityMeasure _ _

/-! ### The chain the marks drive -/

/-- The rule moving the matrix along a mark: a discarded mark leaves it alone, the others
express. -/
def markNext (v : Pressure N M) : MarkJump N M → Pressure N M
  | .discard => v
  | .jump p => express p.1 p.2 v

/-- The matrix after `n` marks. -/
def markState (u : Pressure N M) (j : ℕ → MarkJump N M) (n : ℕ) : Pressure N M :=
  stateAfterJumps markNext u j n

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_zero (u : Pressure N M) (j : ℕ → MarkJump N M) : markState u j 0 = u := rfl

omit [NeZero N] [NeZero M] in
theorem markState_succ (u : Pressure N M) (j : ℕ → MarkJump N M) (n : ℕ) :
    markState u j (n + 1) = markNext (markState u j n) (j n) := rfl

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_succ_discard (u : Pressure N M) (j : ℕ → MarkJump N M) {n : ℕ}
    (h : j n = .discard) : markState u j (n + 1) = markState u j n := by
  rw [markState_succ, h]
  rfl

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_succ_jump (u : Pressure N M) (j : ℕ → MarkJump N M) {n : ℕ} {p : Jump N M}
    (h : j n = .jump p) :
    markState u j (n + 1) = express p.1 p.2 (markState u j n) := by
  rw [markState_succ, h]
  rfl

omit [NeZero N] [NeZero M] in
/-- The matrix after `n` marks depends only on the first `n` of them. -/
theorem markState_congr (u : Pressure N M) {j j' : ℕ → MarkJump N M} (n : ℕ)
    (h : ∀ k < n, j k = j' k) : markState u j n = markState u j' n :=
  stateAfterJumps_congr markNext u n h

omit [NeZero N] [NeZero M] in
/-- `S` is preserved along the mark chain: a discarded mark changes nothing, and an expression
is `π^{a,o}`. -/
theorem isState_markState {u : Pressure N M} (hu : IsState u) (j : ℕ → MarkJump N M) (n : ℕ) :
    IsState (markState u j n) := by
  induction n with
  | zero => exact hu
  | succ n ih =>
      rw [markState_succ]
      cases hj : j n with
      | discard => exact ih
      | jump p => exact ih.express p.1 p.2

omit [NeZero N] [NeZero M] in
/-- The kernel driving the mark chain: replay the marks so far, and read the band at the
matrix they reach. -/
noncomputable abbrev markDrivingKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M) :
    (n : ℕ) → Kernel ((i : Finset.Iic n) → Hold (MarkJump N M)) (Hold (MarkJump N M)) :=
  drivenKernel markNext (markLaw hM hβ) u

theorem markDrivingKernel_apply (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Hold (MarkJump N M)) :
    markDrivingKernel hM hβ u n h
      = markLaw hM hβ (markState u (jumpExtend fun i => (h i).1) (n + 1)) := rfl

/-- **The construction of [GL24]**: the sequence of marks of the band, read from the matrix
they drive. -/
noncomputable def markPathMeasure (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M) :
    Measure (ℕ → Hold (MarkJump N M)) :=
  drivenMeasure markNext (markLaw hM hβ) u

instance isProbabilityMeasure_markPathMeasure (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    (u : Pressure N M) : IsProbabilityMeasure (markPathMeasure hM hβ u) := by
  rw [markPathMeasure]; infer_instance

/-! ### The strip of height `λ` -/

/-- The marks of the strip `[0, λ)`: the discarded ones, and the expressions by an actor under
pressure below `N`.  [GL24] writes their times `T^λ`, and the whole point of the construction is
that they arrive at rate `λ` whatever the matrix does. -/
def lambdaFinset (v : Pressure N M) : Finset (MarkJump N M) :=
  insert MarkJump.discard ((lowFinset v).image MarkJump.jump)

omit [NeZero N] [NeZero M] in
theorem mem_lambdaFinset {v : Pressure N M} {m : MarkJump N M} :
    m ∈ lambdaFinset v ↔ m = .discard ∨ ∃ p ∈ lowFinset v, m = .jump p := by
  simp [lambdaFinset, eq_comm]

/-- The strip has height exactly `λ`: the discarded region and the low-pressure intervals fill
`[0, λ)`. -/
theorem sum_markWeight_lambdaFinset (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    ∑ m ∈ lambdaFinset v, markWeight β v m = ENNReal.ofReal (clockBound N M β) := by
  have hlow : lowRate β v ≤ clockBound N M β := lowRate_le_clockBound hM hβ v
  have hnot : MarkJump.discard ∉ (lowFinset v).image MarkJump.jump := by simp
  rw [lambdaFinset, Finset.sum_insert hnot,
    Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p ∈ lowFinset v, markWeight β v (MarkJump.jump p)
      = ENNReal.ofReal (lowRate β v) := by
    show ∑ p ∈ lowFinset v, ENNReal.ofReal (jumpRate β v p.1 p.2) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le]
    rfl
  rw [hjump]
  show ENNReal.ofReal (clockBound N M β - lowRate β v) + ENNReal.ofReal (lowRate β v) = _
  rw [← ENNReal.ofReal_add (by linarith) (lowRate_nonneg β v)]
  congr 1
  ring

/-! ### Lemma 10 of [GL24], read on the marks -/

/-- Mark `k` lands in the strip of height `λ`. -/
def IsLambdaAt (u : Pressure N M) (k : ℕ) (j : ℕ → MarkJump N M) : Prop :=
  j k ∈ lambdaFinset (markState u j k)

instance decidableIsLambdaAt (u : Pressure N M) (k : ℕ) (j : ℕ → MarkJump N M) :
    Decidable (IsLambdaAt u k j) := inferInstanceAs (Decidable (_ ∈ _))

omit [NeZero N] [NeZero M] in
/-- Whether mark `k` lands in the strip is read off the first `k + 1` marks. -/
theorem isLambdaAt_congr (u : Pressure N M) (k : ℕ) (j j' : ℕ → MarkJump N M)
    (h : ∀ i ≤ k, j i = j' i) : IsLambdaAt u k j ↔ IsLambdaAt u k j' := by
  rw [IsLambdaAt, IsLambdaAt, markState_congr u k fun i hi => h i hi.le, h k le_rfl]

omit [NeZero N] [NeZero M] in
/-- A run of marks that all express follows the trajectory they spell out. -/
theorem markState_add_of_jumps {u : Pressure N M} {j : ℕ → MarkJump N M} {m n : ℕ}
    {T : Trajectory N M}
    (h : ∀ i < n, j (m + i) = .jump (T.actor i, T.opinion i)) :
    ∀ k ≤ n, markState u j (m + k) = T.state (markState u j m) k := by
  intro k
  induction k with
  | zero => intro _; rw [Nat.add_zero, Trajectory.state_zero]
  | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, markState_succ_jump u j (h k (by omega)), ih (by omega),
        T.state_succ]

/-- **Lemma 10 of [GL24], transported to the marks.**  Among any `N` consecutive marks at least
one lands in the strip of height `λ`: a discarded mark does, and if all `N` express then
Proposition 5 exhibits one whose actor carries pressure below `N`. -/
theorem exists_isLambdaAt_block (hM : 2 ≤ M) {u : Pressure N M} (hu : IsState u)
    (j : ℕ → MarkJump N M) (m : ℕ) :
    ∃ k, m * N ≤ k ∧ k < m * N + N ∧ IsLambdaAt u k j := by
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
      exists_rowSup_actor_lt T hM (isState_markState hu j (m * N))
    refine ⟨m * N + k, by omega, by omega, ?_⟩
    rw [IsLambdaAt, hstep k hkN, mem_lambdaFinset]
    refine Or.inr ⟨(T.actor k, T.opinion k), ?_, rfl⟩
    rw [mem_lowFinset, markState_add_of_jumps hstep k hkN.le]
    exact hk

/-- At least one mark in every `N` lands in the strip, so after `m` blocks at least `m` do. -/
theorem le_lowCountOf_lambda (hM : 2 ≤ M) {u : Pressure N M} (hu : IsState u)
    (j : ℕ → MarkJump N M) (m : ℕ) : m ≤ lowCountOf (IsLambdaAt u) (m * N) j := by
  induction m with
  | zero => simp [lowCountOf]
  | succ m ih =>
      obtain ⟨k, hk1, hk2, hk3⟩ := exists_isLambdaAt_block hM hu j m
      have hsub : {i ∈ Finset.range (m * N) | IsLambdaAt u i j}
          ⊆ {i ∈ Finset.range ((m + 1) * N) | IsLambdaAt u i j} := by
        have hrange : Finset.range (m * N) ⊆ Finset.range ((m + 1) * N) := by
          have hsucc : (m + 1) * N = m * N + N := by ring
          rw [hsucc]
          exact Finset.range_subset.2 fun x hx => Finset.mem_range.2 (by omega)
        exact Finset.filter_subset_filter _ hrange
      have hmem : k ∈ {i ∈ Finset.range ((m + 1) * N) | IsLambdaAt u i j} := by
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hk3⟩
        have hsucc : (m + 1) * N = m * N + N := by ring
        rw [hsucc]
        omega
      have hnot : k ∉ {i ∈ Finset.range (m * N) | IsLambdaAt u i j} := by
        intro hcon
        exact absurd (Finset.mem_range.1 (Finset.mem_filter.1 hcon).1) (by omega)
      have hlt : lowCountOf (IsLambdaAt u) (m * N) j
          < lowCountOf (IsLambdaAt u) ((m + 1) * N) j :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨k, hmem, hnot⟩)
      omega

/-! ### The marks of the band do not accumulate -/

theorem markPMF_toMeasure_finset (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (s : Finset (MarkJump N M)) :
    (markPMF hM hβ v).toMeasure ↑s
      = (∑ m ∈ s, markWeight β v m) * (ENNReal.ofReal (bandRate β v))⁻¹ := by
  rw [PMF.toMeasure_apply_finset]
  simp only [markPMF_apply, sum_markWeight hM hβ v]
  rw [← Finset.sum_mul]

omit [NeZero N] [NeZero M] in
theorem compl_lambdaFinset (v : Pressure N M) :
    (lambdaFinset v)ᶜ = ((lowFinset v)ᶜ).image MarkJump.jump := by
  ext m
  cases m with
  | discard => simp [lambdaFinset]
  | jump p => simp [lambdaFinset]

omit [NeZero N] [NeZero M] in
theorem sum_markWeight_compl_lambdaFinset {β : ℝ} (v : Pressure N M) :
    ∑ m ∈ (lambdaFinset v)ᶜ, markWeight β v m = ENNReal.ofReal (highRate β v) := by
  rw [compl_lambdaFinset, Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p ∈ (lowFinset v)ᶜ, markWeight β v (MarkJump.jump p)
      = ENNReal.ofReal (∑ p ∈ (lowFinset v)ᶜ, jumpRate β v p.1 p.2) := by
    show ∑ p ∈ (lowFinset v)ᶜ, ENNReal.ofReal (jumpRate β v p.1 p.2) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le]
  rw [hjump]
  congr 1
  have hsplit := Finset.sum_compl_add_sum (lowFinset v) fun p : Jump N M => jumpRate β v p.1 p.2
  rw [highRate, lowRate, totalRate]
  linarith [hsplit]

/-- **One mark of the band, discounted.**  The strip of height `λ` carries exactly the rate
`λ` out of the band's `λ + q^>(v)`, so discounting the marks that land in it by
`(λ + θ)/λ` costs nothing.  This is where the construction pays: the height of the strip does
not depend on the matrix. -/
theorem lintegral_markLaw_stepWeight_le_one (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {θ : ℝ}
    (hθ : 0 < θ) (v : Pressure N M) :
    ∫⁻ z, stepWeight (ENNReal.ofReal ((clockBound N M β + θ) / clockBound N M β)) θ
      (lambdaFinset v) z ∂(markLaw hM hβ v) ≤ 1 := by
  have hband : 0 < bandRate β v := bandRate_pos β v
  have hmass : (markPMF hM hβ v).toMeasure ↑(lambdaFinset v)
      = ENNReal.ofReal (clockBound N M β / bandRate β v) := by
    rw [markPMF_toMeasure_finset hM hβ v, sum_markWeight_lambdaFinset hM hβ v,
      ← ENNReal.ofReal_inv_of_pos hband,
      ← ENNReal.ofReal_mul (clockBound_pos N M β).le, ← div_eq_mul_inv]
  have hmassc : (markPMF hM hβ v).toMeasure ((↑(lambdaFinset v) : Set (MarkJump N M))ᶜ)
      = ENNReal.ofReal ((bandRate β v - clockBound N M β) / bandRate β v) := by
    rw [← Finset.coe_compl, markPMF_toMeasure_finset hM hβ v,
      sum_markWeight_compl_lambdaFinset v, ← ENNReal.ofReal_inv_of_pos hband,
      ← ENNReal.ofReal_mul (highRate_nonneg β v), ← div_eq_mul_inv]
    congr 2
    rw [bandRate]
    ring
  exact lintegral_stepWeight_le_one hband (clockBound_pos N M β) hθ
    (clockBound_pos N M β).le (clockBound_le_bandRate β v) le_rfl hmass hmassc

/-- **[GL24], steps 4 and 5.**  The marks of the band do not accumulate: the strip of height
`λ` carries at least one mark in every `N`, by Lemma 10, and its marks arrive at rate `λ`
whatever the matrix does. -/
theorem measure_markPathMeasure_blowUp (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) :
    markPathMeasure hM hβ u {ω | holdBlowUp ω = ⊤} = 1 := by
  rw [markPathMeasure, drivenMeasure]
  refine measure_holdBlowUp_eq_one (low := IsLambdaAt u) (D := ENNReal.ofReal
      ((clockBound N M β + 1) / clockBound N M β)) (θ := 1) _ _ (isLambdaAt_congr u)
    (fun n h => lambdaFinset (markState u (jumpExtend fun i => (h i).1) (n + 1)))
    (lambdaFinset u) ?_ ?_ ?_ ?_ one_pos (one_lt_discountRatio one_pos) (b := N) ?_
  · intro z
    rw [IsLambdaAt, markState_zero]
  · intro n h x hx
    have hstate : markState u (jumpExtend fun i => (x i).1) (n + 1)
        = markState u (jumpExtend fun i => (h i).1) (n + 1) := by
      refine markState_congr u (n + 1) fun i hi => ?_
      rw [jumpExtend_apply _ (show i ≤ n + 1 by omega),
        jumpExtend_apply _ (show i ≤ n by omega), ← hx]
      rfl
    rw [IsLambdaAt, jumps_stepExtend, hstate, stepExtend_apply _ (le_refl (n + 1))]
  · exact lintegral_markLaw_stepWeight_le_one hM hβ one_pos u
  · intro n h
    rw [markDrivingKernel_apply]
    exact lintegral_markLaw_stepWeight_le_one hM hβ one_pos _
  · exact fun j q => le_lowCountOf_lambda hM hu j q

/-! ### The law of the first expression

The marks that land in the discarded region leave the matrix alone, so the chain waits there
until a mark lands in an interval of a pair.  That wait is a geometric number of exponential
times of rate `λ + q^>(v)`, each accepted with probability `q(v)/(λ + q^>(v))`; the law it adds
up to is the exponential of rate `q(v)`, and the pair it stops at follows the Gibbs law of
equation (3).  That is the step of `SocialNetwork.stepLaw`, and proving it is what identifies
[GL24]'s construction with the jump-hold one. -/

/-- Some mark among the first `n` expresses; the first that does carries a pair in `B`, and it
happens by time `t`. -/
def acceptedWithin (B : Finset (Jump N M)) (n : ℕ) (t : ℝ) :
    Set (ℕ → Hold (MarkJump N M)) :=
  {ω | ∃ k < n, (∀ i < k, (ω i).1 = MarkJump.discard) ∧ (∃ p ∈ B, (ω k).1 = MarkJump.jump p)
        ∧ holdSum (k + 1) ω ≤ t}

omit [NeZero N] [NeZero M] in
theorem measurableSet_acceptedWithin (B : Finset (Jump N M)) (n : ℕ) (t : ℝ) :
    MeasurableSet (acceptedWithin B n t) := by
  have hcoord : ∀ (i : ℕ) (s : Set (MarkJump N M)),
      MeasurableSet {ω : ℕ → Hold (MarkJump N M) | (ω i).1 ∈ s} :=
    fun i s => (measurable_fst.comp (measurable_pi_apply i)) MeasurableSet.of_discrete
  have hset : acceptedWithin B n t
      = ⋃ k ∈ Finset.range n,
          ((⋂ i ∈ Finset.range k, {ω : ℕ → Hold (MarkJump N M) |
              (ω i).1 ∈ ({MarkJump.discard} : Set (MarkJump N M))})
            ∩ {ω : ℕ → Hold (MarkJump N M) |
                (ω k).1 ∈ {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}}
            ∩ {ω : ℕ → Hold (MarkJump N M) | holdSum (k + 1) ω ≤ t}) := by
    ext ω
    simp only [acceptedWithin, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨k, hk, hdis, hjump, htime⟩
      exact ⟨k, hk, ⟨⟨fun i hi => hdis i hi, hjump⟩, htime⟩⟩
    · rintro ⟨k, hk, ⟨hdis, hjump⟩, htime⟩
      exact ⟨k, hk, fun i hi => hdis i hi, hjump, htime⟩
  rw [hset]
  refine MeasurableSet.biUnion (Finset.range n).countable_toSet fun k _ => ?_
  refine ((MeasurableSet.biInter (Finset.range k).countable_toSet fun i _ => hcoord i _).inter
    (hcoord k _)).inter ?_
  exact measurableSet_le (measurable_holdSum (k + 1)) measurable_const

omit [NeZero N] [NeZero M] in
/-- The first expression is either the first mark, or comes after a discarded one. -/
theorem acceptedWithin_succ (B : Finset (Jump N M)) (n : ℕ) (t : ℝ) :
    acceptedWithin B (n + 1) t
      = {ω | (∃ p ∈ B, (ω 0).1 = MarkJump.jump p) ∧ (ω 0).2 ≤ t}
        ∪ {ω | (ω 0).1 = MarkJump.discard
            ∧ shiftHold ω ∈ acceptedWithin B n (t - (ω 0).2)} := by
  ext ω
  constructor
  · rintro ⟨k, hk, hdis, hjump, htime⟩
    cases k with
    | zero =>
        refine Or.inl ⟨hjump, ?_⟩
        have : holdSum 1 ω = (ω 0).2 := by
          rw [holdSum, Finset.sum_range_one]
          rfl
        rwa [this] at htime
    | succ k =>
        refine Or.inr ⟨hdis 0 (by omega), ⟨k, by omega, ?_, ?_, ?_⟩⟩
        · intro i hi
          show (ω (1 + i)).1 = MarkJump.discard
          exact hdis (1 + i) (by omega)
        · show ∃ p ∈ B, (ω (1 + k)).1 = MarkJump.jump p
          rw [show 1 + k = k + 1 by omega]
          exact hjump
        · have hsplit : holdSum (k + 1 + 1) ω = (ω 0).2 + holdSum (k + 1) (shiftHold ω) := by
            have h1 : holdSum (k + 1 + 1) ω
                = (∑ i ∈ Finset.range (k + 1), holdTime (i + 1) ω) + holdTime 0 ω :=
              Finset.sum_range_succ' _ (k + 1)
            have h2 : holdSum (k + 1) (shiftHold ω)
                = ∑ i ∈ Finset.range (k + 1), holdTime (i + 1) ω :=
              Finset.sum_congr rfl fun i _ => by
                show (ω (1 + i)).2 = (ω (i + 1)).2
                rw [Nat.add_comm]
            rw [h1, h2, add_comm]
            rfl
          rw [hsplit] at htime
          linarith
  · rintro (⟨hjump, htime⟩ | ⟨hdis, k, hk, hdis', hjump, htime⟩)
    · refine ⟨0, by omega, fun i hi => absurd hi (by omega), hjump, ?_⟩
      have : holdSum 1 ω = (ω 0).2 := by
        rw [holdSum, Finset.sum_range_one]
        rfl
      rwa [this]
    · refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hdis
        | succ i =>
            have := hdis' i (by omega)
            show (ω (i + 1)).1 = MarkJump.discard
            rw [show i + 1 = 1 + i by omega]
            exact this
      · obtain ⟨p, hpB, hp⟩ := hjump
        refine ⟨p, hpB, ?_⟩
        show (ω (k + 1)).1 = MarkJump.jump p
        rw [show k + 1 = 1 + k by omega]
        exact hp
      · have hsplit : holdSum (k + 1 + 1) ω = (ω 0).2 + holdSum (k + 1) (shiftHold ω) := by
          have h1 : holdSum (k + 1 + 1) ω
              = (∑ i ∈ Finset.range (k + 1), holdTime (i + 1) ω) + holdTime 0 ω :=
            Finset.sum_range_succ' _ (k + 1)
          have h2 : holdSum (k + 1) (shiftHold ω)
              = ∑ i ∈ Finset.range (k + 1), holdTime (i + 1) ω :=
            Finset.sum_congr rfl fun i _ => by
              show (ω (1 + i)).2 = (ω (i + 1)).2
              rw [Nat.add_comm]
          rw [h1, h2, add_comm]
          rfl
        rw [hsplit]
        linarith

omit [NeZero N] [NeZero M] in
/-- The event, with its deadline shifted by a measurable amount, is measurable in the pair. -/
theorem measurableSet_acceptedWithin_comap {α : Type*} [MeasurableSpace α] {g : α → ℝ}
    (hg : Measurable g) (B : Finset (Jump N M)) (n : ℕ) (t : ℝ) :
    MeasurableSet {r : α × (ℕ → Hold (MarkJump N M)) |
      r.2 ∈ acceptedWithin B n (t - g r.1)} := by
  have hcoord : ∀ (i : ℕ) (c : Set (MarkJump N M)),
      MeasurableSet {r : α × (ℕ → Hold (MarkJump N M)) | (r.2 i).1 ∈ c} :=
    fun i c => (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))
      MeasurableSet.of_discrete
  have hset : {r : α × (ℕ → Hold (MarkJump N M)) | r.2 ∈ acceptedWithin B n (t - g r.1)}
      = ⋃ k ∈ Finset.range n,
          ((⋂ i ∈ Finset.range k, {r : α × (ℕ → Hold (MarkJump N M)) |
              (r.2 i).1 ∈ ({MarkJump.discard} : Set (MarkJump N M))})
            ∩ {r : α × (ℕ → Hold (MarkJump N M)) |
                (r.2 k).1 ∈ {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}}
            ∩ {r : α × (ℕ → Hold (MarkJump N M)) |
                holdSum (k + 1) r.2 + g r.1 ≤ t}) := by
    ext r
    simp only [acceptedWithin, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨k, hk, hdis, hjump, htime⟩
      exact ⟨k, hk, ⟨⟨fun i hi => hdis i hi, hjump⟩, by linarith⟩⟩
    · rintro ⟨k, hk, ⟨hdis, hjump⟩, htime⟩
      exact ⟨k, hk, fun i hi => hdis i hi, hjump, by linarith⟩
  rw [hset]
  refine MeasurableSet.biUnion (Finset.range n).countable_toSet fun k _ => ?_
  refine ((MeasurableSet.biInter (Finset.range k).countable_toSet fun i _ => hcoord i _).inter
    (hcoord k _)).inter ?_
  exact measurableSet_le
    (((measurable_holdSum (k + 1)).comp measurable_snd).add (hg.comp measurable_fst))
    measurable_const

omit [NeZero N] [NeZero M] in
theorem measurableSet_acceptedWithin_prod (B : Finset (Jump N M)) (n : ℕ) (t : ℝ) :
    MeasurableSet {q : Hold (MarkJump N M) × (ℕ → Hold (MarkJump N M)) |
      q.2 ∈ acceptedWithin B n (t - q.1.2)} :=
  measurableSet_acceptedWithin_comap measurable_snd B n t

/-- **The first expression, one mark at a time.**  Either the first mark expresses, or it is
discarded and the chain starts again from the same matrix. -/
theorem measure_acceptedWithin_succ (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (B : Finset (Jump N M))
    (n : ℕ) (t : ℝ) (v : Pressure N M) :
    markPathMeasure hM hβ v (acceptedWithin B (n + 1) t)
      = markLaw hM hβ v {z | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t}
        + ∫⁻ z in {z : Hold (MarkJump N M) | z.1 = MarkJump.discard},
            markPathMeasure hM hβ v (acceptedWithin B n (t - z.2)) ∂(markLaw hM hβ v) := by
  classical
  set D : Set (Hold (MarkJump N M)) := {z | z.1 = MarkJump.discard} with hDdef
  set A : Set (Hold (MarkJump N M)) :=
    {z | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t} with hAdef
  have hfirst : Measurable fun ω : ℕ → Hold (MarkJump N M) => ω 0 := measurable_pi_apply 0
  have hD : MeasurableSet D :=
    measurable_fst (measurableSet_singleton MarkJump.discard)
  have hA : MeasurableSet A := by
    have h1 : MeasurableSet ((fun z : Hold (MarkJump N M) => z.1) ⁻¹'
        {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}) :=
      measurable_fst MeasurableSet.of_discrete
    exact h1.inter (measurableSet_le measurable_snd measurable_const)
  set S₁ : Set (ℕ → Hold (MarkJump N M)) := (fun ω => ω 0) ⁻¹' A with hS₁
  set S₂ : Set (ℕ → Hold (MarkJump N M)) :=
    {ω | (ω 0).1 = MarkJump.discard ∧ shiftHold ω ∈ acceptedWithin B n (t - (ω 0).2)} with hS₂
  have hmeas1 : MeasurableSet S₁ := hfirst hA
  have hmeas2 : MeasurableSet S₂ := by
    have hpair : Measurable fun ω : ℕ → Hold (MarkJump N M) => (ω 0, shiftHold ω) :=
      hfirst.prodMk measurable_shiftHold
    have hrw : S₂ = ((fun ω : ℕ → Hold (MarkJump N M) => ω 0) ⁻¹' D)
        ∩ (fun ω : ℕ → Hold (MarkJump N M) => (ω 0, shiftHold ω)) ⁻¹'
          {q : Hold (MarkJump N M) × (ℕ → Hold (MarkJump N M)) |
            q.2 ∈ acceptedWithin B n (t - q.1.2)} := rfl
    rw [hrw]
    exact (hfirst hD).inter (hpair (measurableSet_acceptedWithin_prod B n t))
  have hunion : acceptedWithin B (n + 1) t = S₁ ∪ S₂ := acceptedWithin_succ B n t
  have hdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    rintro ω ⟨⟨p, -, hp⟩, -⟩ ⟨hd, -⟩
    rw [hp] at hd
    exact absurd hd (by simp)
  rw [hunion, measure_union hdisj hmeas2]
  congr 1
  · rw [hS₁, ← Measure.map_apply hfirst hA, markPathMeasure, map_drivenMeasure_first]
  · set f : Hold (MarkJump N M) → (ℕ → Hold (MarkJump N M)) → ℝ≥0∞ :=
      fun z ω' => if z ∈ D then
        Set.indicator (acceptedWithin B n (t - z.2))
          (1 : (ℕ → Hold (MarkJump N M)) → ℝ≥0∞) ω' else 0 with hf
    have hfmeas : Measurable (Function.uncurry f) := by
      refine Measurable.ite ?_ ?_ measurable_const
      · exact measurable_fst hD
      · exact measurable_const.indicator (measurableSet_acceptedWithin_prod B n t)
    have hind : ∀ ω : ℕ → Hold (MarkJump N M),
        Set.indicator S₂ (1 : (ℕ → Hold (MarkJump N M)) → ℝ≥0∞) ω
          = f (ω 0) (shiftHold ω) := by
      intro ω
      by_cases hd : ω 0 ∈ D
      · rw [hf]
        simp only [if_pos hd]
        by_cases hin : shiftHold ω ∈ acceptedWithin B n (t - (ω 0).2)
        · rw [Set.indicator_of_mem hin, Set.indicator_of_mem (show ω ∈ S₂ from ⟨hd, hin⟩)]
          rfl
        · rw [Set.indicator_of_notMem hin,
            Set.indicator_of_notMem (fun hcon => hin hcon.2)]
      · rw [hf]
        simp only [if_neg hd]
        rw [Set.indicator_of_notMem (fun hcon => hd hcon.1)]
    rw [← lintegral_indicator_one hmeas2, lintegral_congr hind, markPathMeasure,
      lintegral_drivenMeasure_restart markNext (markLaw hM hβ) v hfmeas,
      ← lintegral_indicator hD]
    refine lintegral_congr fun z => ?_
    by_cases hd : z ∈ D
    · rw [Set.indicator_of_mem hd, hf]
      simp only [if_pos hd]
      rw [lintegral_indicator_one (measurableSet_acceptedWithin B n (t - z.2))]
      show markPathMeasure hM hβ (markNext v z.1) _ = _
      rw [show z.1 = MarkJump.discard from hd]
      rfl
    · rw [Set.indicator_of_notMem hd, hf]
      simp only [if_neg hd]
      exact lintegral_zero

/-! ### The integral the fixed point needs -/

omit [NeZero N] [NeZero M] in
theorem integral_exp_neg_interval {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ s in (0:ℝ)..t, Real.exp (-(c * s)) = (1 - Real.exp (-(c * t))) / c := by
  have h : ∀ s : ℝ, Real.exp (-(c * s)) = Real.exp ((-c) * s) := by
    intro s; ring_nf
  simp_rw [h]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by linarith : (-c) ≠ 0),
    integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
  have hct : (-c) * t = -(c * t) := by ring
  rw [hct]
  field_simp
  ring

omit [NeZero N] [NeZero M] in
/-- **The convolution the construction turns on.**  Against a mark arriving at rate `Λ`, the
chance `1 - e^{-q(t-s)}` of expressing in the time that is left integrates to this. -/
theorem lintegral_oneSub_exp {Λ q : ℝ} (hΛ : 0 < Λ) (hq : 0 < q) (hqΛ : q < Λ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s, ENNReal.ofReal (1 - Real.exp (-(q * (t - s)))) ∂(expMeasure Λ)
      = ENNReal.ofReal ((1 - Real.exp (-(Λ * t)))
          - Real.exp (-(q * t)) * Λ / (Λ - q) * (1 - Real.exp (-((Λ - q) * t)))) := by
  have hmeasg : Measurable fun s : ℝ => ENNReal.ofReal (1 - Real.exp (-(q * (t - s)))) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.sub ?_)
    exact Real.measurable_exp.comp ((measurable_const.mul (measurable_const.sub measurable_id)).neg)
  -- the negative half-line and the times after `t` contribute nothing
  have hcompl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 := by ext x; simp
  have hzero : ∫⁻ s in Set.Ioi t, ENNReal.ofReal (1 - Real.exp (-(q * (t - s))))
      ∂(expMeasure Λ) = 0 := by
    refine setLIntegral_eq_zero (measurableSet_Ioi) fun s hs => ?_
    have h1 : 1 ≤ Real.exp (-(q * (t - s))) := by
      refine Real.one_le_exp ?_
      have : t - s < 0 := by simp only [Set.mem_Ioi] at hs; linarith
      nlinarith
    exact ENNReal.ofReal_eq_zero.2 (by linarith)
  have hsplit : ∫⁻ s, ENNReal.ofReal (1 - Real.exp (-(q * (t - s)))) ∂(expMeasure Λ)
      = ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (1 - Real.exp (-(q * (t - s))))
        ∂(expMeasure Λ) := by
    rw [← lintegral_add_compl _ (measurableSet_Ioi (a := (0 : ℝ))), hcompl,
      setLIntegral_measure_zero _ _ (expMeasure_Iic_zero hΛ), add_zero,
      show Set.Ioi (0 : ℝ) = Set.Ioc 0 t ∪ Set.Ioi t by
        ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]; constructor
        · intro hx; rcases le_or_gt x t with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr h
        · rintro (⟨hx, -⟩ | hx) ; · exact hx
          · linarith,
      lintegral_union measurableSet_Ioi (by
        rw [Set.disjoint_left]; rintro x ⟨-, hx⟩ hx'; simp only [Set.mem_Ioi] at hx'; linarith),
      hzero, add_zero]
  rw [hsplit]
  -- on `(0, t]` the density is `Λ e^{-Λ s}`
  have hdens : expMeasure Λ = MeasureTheory.volume.withDensity (exponentialPDF Λ) := rfl
  have hmeasd : Measurable (exponentialPDF Λ) := (measurable_exponentialPDFReal Λ).ennreal_ofReal
  rw [hdens, restrict_withDensity measurableSet_Ioc,
    lintegral_withDensity_eq_lintegral_mul _ hmeasd hmeasg]
  have hcongr : ∀ s ∈ Set.Ioc 0 t, (exponentialPDF Λ * fun s : ℝ =>
      ENNReal.ofReal (1 - Real.exp (-(q * (t - s))))) s
      = ENNReal.ofReal ((1 - Real.exp (-(q * (t - s)))) * (Λ * Real.exp (-(Λ * s)))) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs.1
    have hle : Real.exp (-(q * (t - s))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hs.2])
    simp only [Pi.mul_apply, exponentialPDF_eq, if_pos hs0]
    rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioc hcongr]
  -- and the integral is elementary
  have hint : IntervalIntegrable
      (fun s : ℝ => (1 - Real.exp (-(q * (t - s)))) * (Λ * Real.exp (-(Λ * s))))
      MeasureTheory.volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 t)]
      fun s : ℝ => (1 - Real.exp (-(q * (t - s)))) * (Λ * Real.exp (-(Λ * s))) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hle : Real.exp (-(q * (t - s))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hs.2])
    have : (0:ℝ) ≤ 1 - Real.exp (-(q * (t - s))) := by linarith
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1 hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le ht]
  -- expand into two elementary integrals
  have hexpand : ∀ s : ℝ, (1 - Real.exp (-(q * (t - s)))) * (Λ * Real.exp (-(Λ * s)))
      = Λ * Real.exp (-(Λ * s))
        - Λ * Real.exp (-(q * t)) * Real.exp (-((Λ - q) * s)) := by
    intro s
    rw [show -(q * (t - s)) = -(q * t) + q * s by ring, Real.exp_add]
    rw [show -((Λ - q) * s) = -(Λ * s) + q * s by ring, Real.exp_add]
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_neg_interval hΛ t, integral_exp_neg_interval (by linarith : 0 < Λ - q) t]
  field_simp

/-! ### The two ingredients of the recursion -/

/-- The chain never waits a negative time. -/
theorem markPathMeasure_holdTime_nonneg (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (n : ℕ) : markPathMeasure hM hβ v {ω | (ω n).2 < 0} = 0 := by
  refine drivenMeasure_holdTime_nonneg markNext (markLaw hM hβ) (fun w => ?_) v n
  have hset : {z : Hold (MarkJump N M) | z.2 < 0}
      = (Set.univ : Set (MarkJump N M)) ×ˢ (Set.Iio (0 : ℝ)) := by
    ext z; simp
  have hnull : expMeasure (bandRate β w) (Set.Iio (0 : ℝ)) = 0 :=
    measure_mono_null Set.Iio_subset_Iic_self (expMeasure_Iic_zero (bandRate_pos β w))
  have hprob : IsProbabilityMeasure (expMeasure (bandRate β w)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos β w)
  rw [markLaw, hset, Measure.prod_prod, hnull, mul_zero]

/-- Before time zero nothing has been expressed. -/
theorem measure_acceptedWithin_of_neg (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    (B : Finset (Jump N M)) (n : ℕ) {t : ℝ} (ht : t < 0) (v : Pressure N M) :
    markPathMeasure hM hβ v (acceptedWithin B n t) = 0 := by
  refine measure_mono_null (fun ω hω => ?_)
    (measure_biUnion_null_iff (Finset.range n).countable_toSet |>.2
      fun i _ => markPathMeasure_holdTime_nonneg hM hβ v i)
  obtain ⟨k, hk, -, -, htime⟩ := hω
  by_contra hcon
  have hnn : ∀ i ∈ Finset.range n, ¬ ((ω i).2 < 0) := by
    intro i hi hneg
    exact hcon (Set.mem_biUnion hi hneg)
  have : 0 ≤ holdSum (k + 1) ω :=
    Finset.sum_nonneg fun i hi => not_lt.1 (hnn i (Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hi) (by omega))))
  linarith

/-- The Gibbs mass of a family of pairs, read in the band. -/
theorem markPMF_toMeasure_image (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    (B : Finset (Jump N M)) :
    (markPMF hM hβ v).toMeasure {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}
      = ENNReal.ofReal ((∑ p ∈ B, jumpRate β v p.1 p.2) / bandRate β v) := by
  have hcoe : {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}
      = ↑(B.image MarkJump.jump) := by
    ext m; simp [eq_comm]
  rw [hcoe, markPMF_toMeasure_finset hM hβ v,
    Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p ∈ B, markWeight β v (MarkJump.jump p)
      = ENNReal.ofReal (∑ p ∈ B, jumpRate β v p.1 p.2) := by
    show ∑ p ∈ B, ENNReal.ofReal (jumpRate β v p.1 p.2) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le]
  rw [hjump, ← ENNReal.ofReal_inv_of_pos (bandRate_pos β v),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le),
    ← div_eq_mul_inv]

/-- The first mark expresses a pair of `B`, by time `t`. -/
theorem markLaw_apply_accept (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (B : Finset (Jump N M))
    (v : Pressure N M) {t : ℝ} (ht : 0 ≤ t) :
    markLaw hM hβ v {z | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t}
      = ENNReal.ofReal ((∑ p ∈ B, jumpRate β v p.1 p.2) / bandRate β v)
        * ENNReal.ofReal (1 - Real.exp (-(bandRate β v * t))) := by
  have hprob : IsProbabilityMeasure (expMeasure (bandRate β v)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos β v)
  have hset : {z : Hold (MarkJump N M) | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t}
      = {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p} ×ˢ Set.Iic t := rfl
  rw [markLaw, hset, Measure.prod_prod, markPMF_toMeasure_image hM hβ v B,
    expMeasure_Iic_of_nonneg (bandRate_pos β v) ht]

/-- The first mark is discarded: the chain starts again from the same matrix, after an
exponential time of the band's height. -/
theorem lintegral_discard_markLaw (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in {z : Hold (MarkJump N M) | z.1 = MarkJump.discard}, f z.2 ∂(markLaw hM hβ v)
      = ENNReal.ofReal ((clockBound N M β - lowRate β v) / bandRate β v)
        * ∫⁻ s, f s ∂(expMeasure (bandRate β v)) := by
  have hprob : IsProbabilityMeasure (expMeasure (bandRate β v)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos β v)
  have hD : ({z : Hold (MarkJump N M) | z.1 = MarkJump.discard})
      = ({MarkJump.discard} : Set (MarkJump N M)) ×ˢ (Set.univ : Set ℝ) := by
    ext z; simp
  have hmass : (markPMF hM hβ v).toMeasure ({MarkJump.discard} : Set (MarkJump N M))
      = ENNReal.ofReal ((clockBound N M β - lowRate β v) / bandRate β v) := by
    have hcoe : ({MarkJump.discard} : Set (MarkJump N M))
        = ↑({MarkJump.discard} : Finset (MarkJump N M)) := by simp
    rw [hcoe, markPMF_toMeasure_finset hM hβ v, Finset.sum_singleton]
    show ENNReal.ofReal (clockBound N M β - lowRate β v) * _ = _
    rw [← ENNReal.ofReal_inv_of_pos (bandRate_pos β v),
      ← ENNReal.ofReal_mul (by linarith [lowRate_le_clockBound hM hβ v]), ← div_eq_mul_inv]
  rw [← hmass, markLaw, hD, ← lintegral_indicator (by
      exact (measurableSet_singleton MarkJump.discard).prod MeasurableSet.univ)]
  have hfun : ∀ z : Hold (MarkJump N M),
      Set.indicator (({MarkJump.discard} : Set (MarkJump N M)) ×ˢ (Set.univ : Set ℝ))
        (fun z => f z.2) z
      = Set.indicator ({MarkJump.discard} : Set (MarkJump N M))
          (1 : MarkJump N M → ℝ≥0∞) z.1 * f z.2 := by
    intro z
    by_cases hz : z.1 = MarkJump.discard
    · rw [Set.indicator_of_mem
        (show z ∈ ({MarkJump.discard} : Set (MarkJump N M)) ×ˢ (Set.univ : Set ℝ) from
          ⟨hz, Set.mem_univ _⟩),
        Set.indicator_of_mem (show z.1 ∈ ({MarkJump.discard} : Set (MarkJump N M)) from hz)]
      show f z.2 = 1 * f z.2
      rw [one_mul]
    · rw [Set.indicator_of_notMem (fun hcon => hz hcon.1),
        Set.indicator_of_notMem (show z.1 ∉ ({MarkJump.discard} : Set (MarkJump N M)) from hz),
        zero_mul]
  rw [lintegral_congr hfun,
    lintegral_prod_mul
      (f := fun m : MarkJump N M =>
        Set.indicator ({MarkJump.discard} : Set (MarkJump N M))
          (1 : MarkJump N M → ℝ≥0∞) m)
      (g := f)
      (measurable_one.indicator
        (measurableSet_singleton MarkJump.discard)).aemeasurable hf.aemeasurable,
    lintegral_indicator_one (measurableSet_singleton MarkJump.discard)]

/-! ### The fixed point -/

omit [NeZero N] [NeZero M] in
theorem totalRate_le_bandRate (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    totalRate β v ≤ bandRate β v := by
  have := lowRate_le_clockBound hM hβ v
  rw [bandRate, highRate]
  linarith

omit [NeZero N] [NeZero M] in
theorem bandRate_sub_totalRate (β : ℝ) (v : Pressure N M) :
    bandRate β v - totalRate β v = clockBound N M β - lowRate β v := by
  rw [bandRate, highRate]
  ring

/-- **The step of [GL24]'s construction is the step of the jump-hold one, from above.** -/
theorem measure_acceptedWithin_le (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (B : Finset (Jump N M))
    (n : ℕ) (t : ℝ) (v : Pressure N M) :
    markPathMeasure hM hβ v (acceptedWithin B n t)
      ≤ ENNReal.ofReal ((∑ p ∈ B, jumpRate β v p.1 p.2) / totalRate β v
          * (1 - Real.exp (-(totalRate β v * t)))) := by
  induction n generalizing t with
  | zero =>
      have : acceptedWithin B 0 t = ∅ := by
        ext ω
        simp only [acceptedWithin, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨k, hk, -⟩
        omega
      rw [this, measure_empty]
      exact zero_le
  | succ n ih =>
      rcases lt_or_ge t 0 with ht | ht
      · rw [measure_acceptedWithin_of_neg hM hβ B (n + 1) ht v]
        exact zero_le
      set Λ := bandRate β v with hΛ
      set q := totalRate β v with hq
      set rB := ∑ p ∈ B, jumpRate β v p.1 p.2 with hrB
      have hqpos : 0 < q := totalRate_pos β v
      have hΛpos : 0 < Λ := bandRate_pos β v
      have hqΛ : q ≤ Λ := totalRate_le_bandRate hM hβ v
      have hrB0 : 0 ≤ rB :=
        Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le
      have hrho : Λ - q = clockBound N M β - lowRate β v := bandRate_sub_totalRate β v
      have hrho0 : 0 ≤ Λ - q := by linarith
      have hmeasf : Measurable fun s : ℝ =>
          markPathMeasure hM hβ v (acceptedWithin B n (t - s)) :=
        measurable_measure_prodMk_left
          (measurableSet_acceptedWithin_comap (measurable_id (α := ℝ)) B n t)
      rw [measure_acceptedWithin_succ hM hβ B n t v, markLaw_apply_accept hM hβ B v ht,
        lintegral_discard_markLaw hM hβ v hmeasf, ← hrho]
      simp only [← hΛ, ← hrB]
      -- the integral is bounded by the target's own convolution
      have hstep : ∫⁻ s, markPathMeasure hM hβ v (acceptedWithin B n (t - s))
            ∂(expMeasure Λ)
          ≤ ENNReal.ofReal (rB / q)
            * ∫⁻ s, ENNReal.ofReal (1 - Real.exp (-(q * (t - s)))) ∂(expMeasure Λ) := by
        rw [← lintegral_const_mul _ (by
          refine ENNReal.measurable_ofReal.comp (measurable_const.sub ?_)
          exact Real.measurable_exp.comp
            ((measurable_const.mul (measurable_const.sub measurable_id)).neg))]
        refine lintegral_mono fun s => le_trans (ih (t - s)) (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (div_nonneg hrB0 hqpos.le)]
      refine le_trans (add_le_add le_rfl (mul_le_mul' le_rfl hstep)) ?_
      rcases eq_or_lt_of_le hqΛ with heq | hlt
      · rw [← heq]
        simp only [sub_self, zero_div, ENNReal.ofReal_zero, zero_mul, add_zero]
        exact le_of_eq (by rw [← ENNReal.ofReal_mul (div_nonneg hrB0 hqpos.le)])
      · rw [lintegral_oneSub_exp hΛpos hqpos hlt ht]
        have hE : Real.exp (-(q * t)) * Real.exp (-((Λ - q) * t)) = Real.exp (-(Λ * t)) := by
          rw [← Real.exp_add]
          ring_nf
        have hconvex : Λ * Real.exp (-(q * t)) ≤ q * Real.exp (-(Λ * t)) + (Λ - q) := by
          have hb : (0:ℝ) ≤ 1 - q / Λ := by
            rw [sub_nonneg, div_le_one hΛpos]; linarith
          have h := convexOn_exp.2 (Set.mem_univ (-(Λ * t))) (Set.mem_univ (0:ℝ))
            (by positivity : (0:ℝ) ≤ q / Λ) hb (by ring)
          simp only [smul_eq_mul, mul_zero, Real.exp_zero, mul_one, add_zero] at h
          have hxy : q / Λ * -(Λ * t) = -(q * t) := by field_simp
          rw [hxy] at h
          have hmul : Λ * Real.exp (-(q * t))
              ≤ Λ * (q / Λ * Real.exp (-(Λ * t)) + (1 - q / Λ)) :=
            mul_le_mul_of_nonneg_left h hΛpos.le
          have hfix : Λ * (q / Λ * Real.exp (-(Λ * t)) + (1 - q / Λ))
              = q * Real.exp (-(Λ * t)) + (Λ - q) := by
            field_simp
          linarith [hmul, hfix]
        have hK : 0 ≤ (1 - Real.exp (-(Λ * t)))
            - Real.exp (-(q * t)) * Λ / (Λ - q) * (1 - Real.exp (-((Λ - q) * t))) := by
          have hlt' : 0 < Λ - q := by linarith
          rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hlt']
          have hexp : Real.exp (-(q * t)) * Λ * (1 - Real.exp (-((Λ - q) * t)))
              = Λ * Real.exp (-(q * t)) - Λ * Real.exp (-(Λ * t)) := by
            rw [← hE]; ring
          rw [hexp]
          nlinarith [hconvex]
        have h1mexp : (0:ℝ) ≤ 1 - Real.exp (-(Λ * t)) := by
          have : Real.exp (-(Λ * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          linarith
        rw [← ENNReal.ofReal_mul (div_nonneg hrB0 hqpos.le),
          ← ENNReal.ofReal_mul (div_nonneg hrho0 hΛpos.le),
          ← ENNReal.ofReal_mul (div_nonneg hrB0 hΛpos.le),
          ← ENNReal.ofReal_add (mul_nonneg (div_nonneg hrB0 hΛpos.le) h1mexp)
            (mul_nonneg (div_nonneg hrho0 hΛpos.le)
              (mul_nonneg (div_nonneg hrB0 hqpos.le) hK))]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [← hE]
        field_simp
        ring

omit [NeZero N] [NeZero M] in
theorem sum_le_totalRate (β : ℝ) (v : Pressure N M) (B : Finset (Jump N M)) :
    ∑ p ∈ B, jumpRate β v p.1 p.2 ≤ totalRate β v :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (jumpRate_pos β v p.1 p.2).le

/-- **The step of [GL24]'s construction is the step of the jump-hold one, from below.**  The
error is the chance that the first `n` marks are all discarded. -/
theorem measure_acceptedWithin_ge (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (B : Finset (Jump N M))
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (v : Pressure N M) :
    ENNReal.ofReal ((∑ p ∈ B, jumpRate β v p.1 p.2) / totalRate β v
        * (1 - Real.exp (-(totalRate β v * t))))
      ≤ markPathMeasure hM hβ v (acceptedWithin B n t)
        + ENNReal.ofReal (((bandRate β v - totalRate β v) / bandRate β v) ^ n) := by
  induction n generalizing t with
  | zero =>
      have hle : ENNReal.ofReal ((∑ p ∈ B, jumpRate β v p.1 p.2) / totalRate β v
          * (1 - Real.exp (-(totalRate β v * t)))) ≤ 1 := by
        refine ENNReal.ofReal_le_one.2 ?_
        have h1 : (∑ p ∈ B, jumpRate β v p.1 p.2) / totalRate β v ≤ 1 :=
          (div_le_one (totalRate_pos β v)).2 (sum_le_totalRate β v B)
        have h2 : 1 - Real.exp (-(totalRate β v * t)) ≤ 1 := by
          have := Real.exp_pos (-(totalRate β v * t)); linarith
        have h3 : 0 ≤ 1 - Real.exp (-(totalRate β v * t)) := by
          have : Real.exp (-(totalRate β v * t)) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [totalRate_pos β v])
          linarith
        have h4 : 0 ≤ (∑ p ∈ B, jumpRate β v p.1 p.2) / totalRate β v :=
          div_nonneg (Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le)
            (totalRate_pos β v).le
        nlinarith
      simpa using le_trans hle le_add_self
  | succ n ih =>
      set Λ := bandRate β v with hΛ
      set q := totalRate β v with hq
      set rB := ∑ p ∈ B, jumpRate β v p.1 p.2 with hrB
      have hqpos : 0 < q := totalRate_pos β v
      have hΛpos : 0 < Λ := bandRate_pos β v
      have hqΛ : q ≤ Λ := totalRate_le_bandRate hM hβ v
      have hrB0 : 0 ≤ rB :=
        Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le
      have hrho : Λ - q = clockBound N M β - lowRate β v := bandRate_sub_totalRate β v
      have hrho0 : 0 ≤ Λ - q := by linarith
      have hr0 : 0 ≤ (Λ - q) / Λ := by positivity
      have hmeasf : Measurable fun s : ℝ =>
          markPathMeasure hM hβ v (acceptedWithin B n (t - s)) :=
        measurable_measure_prodMk_left
          (measurableSet_acceptedWithin_comap (measurable_id (α := ℝ)) B n t)
      rw [measure_acceptedWithin_succ hM hβ B n t v, markLaw_apply_accept hM hβ B v ht,
        lintegral_discard_markLaw hM hβ v hmeasf, ← hrho]
      simp only [← hΛ, ← hrB]
      -- the target's convolution is below the chain's, up to the error
      have hpt : ∀ s : ℝ, ENNReal.ofReal (rB / q * (1 - Real.exp (-(q * (t - s)))))
          ≤ markPathMeasure hM hβ v (acceptedWithin B n (t - s))
            + ENNReal.ofReal (((Λ - q) / Λ) ^ n) := by
        intro s
        rcases le_or_gt 0 (t - s) with hts | hts
        · exact ih hts
        · refine le_trans (le_of_eq ?_) (zero_le)
          refine ENNReal.ofReal_eq_zero.2 ?_
          have hneg : q * (t - s) < 0 := mul_neg_of_pos_of_neg hqpos hts
          have h1 : 1 ≤ Real.exp (-(q * (t - s))) :=
            Real.one_le_exp (by linarith)
          have h2 : rB / q * (1 - Real.exp (-(q * (t - s)))) ≤ 0 := by
            have hc : 0 ≤ rB / q := by positivity
            nlinarith
          exact h2
      have hconv : ENNReal.ofReal (rB / q)
            * ∫⁻ s, ENNReal.ofReal (1 - Real.exp (-(q * (t - s)))) ∂(expMeasure Λ)
          ≤ (∫⁻ s, markPathMeasure hM hβ v (acceptedWithin B n (t - s)) ∂(expMeasure Λ))
            + ENNReal.ofReal (((Λ - q) / Λ) ^ n) := by
        have hprob : IsProbabilityMeasure (expMeasure Λ) :=
          isProbabilityMeasure_expMeasure hΛpos
        rw [← lintegral_const_mul _ (by
          refine ENNReal.measurable_ofReal.comp (measurable_const.sub ?_)
          exact Real.measurable_exp.comp
            ((measurable_const.mul (measurable_const.sub measurable_id)).neg))]
        calc ∫⁻ s, ENNReal.ofReal (rB / q) * ENNReal.ofReal
                (1 - Real.exp (-(q * (t - s)))) ∂(expMeasure Λ)
            = ∫⁻ s, ENNReal.ofReal (rB / q * (1 - Real.exp (-(q * (t - s)))))
                ∂(expMeasure Λ) := by
              refine lintegral_congr fun s => ?_
              rw [← ENNReal.ofReal_mul (by positivity)]
          _ ≤ ∫⁻ s, (markPathMeasure hM hβ v (acceptedWithin B n (t - s))
                + ENNReal.ofReal (((Λ - q) / Λ) ^ n)) ∂(expMeasure Λ) := lintegral_mono hpt
          _ = _ := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ,
                mul_one]
      -- assemble
      rcases eq_or_lt_of_le hqΛ with heq | hlt
      · rw [← heq]
        simp only [sub_self, zero_div, ENNReal.ofReal_zero, zero_mul, add_zero,
          zero_pow (Nat.succ_ne_zero n)]
        exact le_of_eq (by rw [← ENNReal.ofReal_mul (by positivity)])
      · have hE : Real.exp (-(q * t)) * Real.exp (-((Λ - q) * t)) = Real.exp (-(Λ * t)) := by
          rw [← Real.exp_add]
          ring_nf
        have hconvex : Λ * Real.exp (-(q * t)) ≤ q * Real.exp (-(Λ * t)) + (Λ - q) := by
          have hb : (0:ℝ) ≤ 1 - q / Λ := by
            rw [sub_nonneg, div_le_one hΛpos]; linarith
          have h := convexOn_exp.2 (Set.mem_univ (-(Λ * t))) (Set.mem_univ (0:ℝ))
            (by positivity : (0:ℝ) ≤ q / Λ) hb (by ring)
          simp only [smul_eq_mul, mul_zero, Real.exp_zero, mul_one, add_zero] at h
          have hxy : q / Λ * -(Λ * t) = -(q * t) := by field_simp
          rw [hxy] at h
          have hmul : Λ * Real.exp (-(q * t))
              ≤ Λ * (q / Λ * Real.exp (-(Λ * t)) + (1 - q / Λ)) :=
            mul_le_mul_of_nonneg_left h hΛpos.le
          have hfix : Λ * (q / Λ * Real.exp (-(Λ * t)) + (1 - q / Λ))
              = q * Real.exp (-(Λ * t)) + (Λ - q) := by
            field_simp
          linarith [hmul, hfix]
        have hK : 0 ≤ (1 - Real.exp (-(Λ * t)))
            - Real.exp (-(q * t)) * Λ / (Λ - q) * (1 - Real.exp (-((Λ - q) * t))) := by
          have hlt' : 0 < Λ - q := by linarith
          rw [sub_nonneg, div_mul_eq_mul_div, div_le_iff₀ hlt']
          have hexp : Real.exp (-(q * t)) * Λ * (1 - Real.exp (-((Λ - q) * t)))
              = Λ * Real.exp (-(q * t)) - Λ * Real.exp (-(Λ * t)) := by
            rw [← hE]; ring
          rw [hexp]
          nlinarith [hconvex]
        have hsplit : ENNReal.ofReal (rB / q * (1 - Real.exp (-(q * t))))
            = ENNReal.ofReal (rB / Λ) * ENNReal.ofReal (1 - Real.exp (-(Λ * t)))
              + ENNReal.ofReal ((Λ - q) / Λ)
                * (ENNReal.ofReal (rB / q)
                  * ENNReal.ofReal ((1 - Real.exp (-(Λ * t)))
                    - Real.exp (-(q * t)) * Λ / (Λ - q)
                      * (1 - Real.exp (-((Λ - q) * t))))) := by
          have h1mexp : (0:ℝ) ≤ 1 - Real.exp (-(Λ * t)) := by
            have : Real.exp (-(Λ * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
            linarith
          rw [← ENNReal.ofReal_mul (div_nonneg hrB0 hΛpos.le),
            ← ENNReal.ofReal_mul (div_nonneg hrB0 hqpos.le),
            ← ENNReal.ofReal_mul hr0,
            ← ENNReal.ofReal_add (mul_nonneg (div_nonneg hrB0 hΛpos.le) h1mexp)
              (mul_nonneg hr0 (mul_nonneg (div_nonneg hrB0 hqpos.le) hK))]
          congr 1
          rw [← hE]
          field_simp
          ring
        rw [hsplit, ← lintegral_oneSub_exp hΛpos hqpos hlt ht]
        calc ENNReal.ofReal (rB / Λ) * ENNReal.ofReal (1 - Real.exp (-(Λ * t)))
              + ENNReal.ofReal ((Λ - q) / Λ) * (ENNReal.ofReal (rB / q)
                * ∫⁻ s, ENNReal.ofReal (1 - Real.exp (-(q * (t - s)))) ∂(expMeasure Λ))
            ≤ ENNReal.ofReal (rB / Λ) * ENNReal.ofReal (1 - Real.exp (-(Λ * t)))
              + ENNReal.ofReal ((Λ - q) / Λ)
                * ((∫⁻ s, markPathMeasure hM hβ v (acceptedWithin B n (t - s))
                    ∂(expMeasure Λ)) + ENNReal.ofReal (((Λ - q) / Λ) ^ n)) := by
              gcongr
          _ = _ := by
              rw [mul_add, ← add_assoc, ← ENNReal.ofReal_mul hr0]
              congr 2
              ring

/-! ### The macro-step law -/

theorem discardRatio_nonneg (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) :
    0 ≤ (bandRate β v - totalRate β v) / bandRate β v :=
  div_nonneg (by linarith [totalRate_le_bandRate hM hβ v]) (bandRate_pos β v).le

theorem discardRatio_lt_one (β : ℝ) (v : Pressure N M) :
    (bandRate β v - totalRate β v) / bandRate β v < 1 := by
  rw [div_lt_one (bandRate_pos β v)]
  linarith [totalRate_pos β v]

/-- **The law of the first expression of [GL24]'s construction.**  Letting the number of marks
grow, the two bounds meet: the first mark of the band that is not discarded carries a pair in
`B` and does so by time `t` with probability

`(∑_{p ∈ B} rate p / q) (1 - e^{-q t})`,

which is `SocialNetwork.stepLaw` read on the rectangle `B ×ˢ Iic t`.  The geometric number of
discarded marks has been summed away: that is the content of [GL24]'s Figure 2. -/
theorem iSup_measure_acceptedWithin (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (B : Finset (Jump N M))
    {t : ℝ} (ht : 0 ≤ t) (v : Pressure N M) :
    ⨆ n, markPathMeasure hM hβ v (acceptedWithin B n t)
      = ENNReal.ofReal ((∑ p ∈ B, jumpRate β v p.1 p.2) / totalRate β v
          * (1 - Real.exp (-(totalRate β v * t)))) := by
  refine le_antisymm (iSup_le fun n => measure_acceptedWithin_le hM hβ B n t v) ?_
  set L := ⨆ n, markPathMeasure hM hβ v (acceptedWithin B n t) with hLdef
  have hLle : L ≤ 1 := iSup_le fun n => prob_le_one
  have hLne : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hLle
  set δ := (bandRate β v - totalRate β v) / bandRate β v with hδdef
  have hδ0 : 0 ≤ δ := discardRatio_nonneg hM hβ v
  have hδ1 : δ < 1 := discardRatio_lt_one β v
  have h0 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (δ ^ n)) Filter.atTop (nhds 0) := by
    simp_rw [ENNReal.ofReal_pow hδ0]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hδ1)
  have htend : Filter.Tendsto (fun n : ℕ => L + ENNReal.ofReal (δ ^ n)) Filter.atTop (nhds L) := by
    simpa using h0.const_add L
  refine ge_of_tendsto' htend fun n => ?_
  exact (measure_acceptedWithin_ge hM hβ B n ht v).trans
    (add_le_add (le_iSup (fun n => markPathMeasure hM hβ v (acceptedWithin B n t)) n) le_rfl)

end SocialNetwork
