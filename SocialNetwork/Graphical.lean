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

/-- The matrix after `n` marks: the discarded marks leave it alone, the others express. -/
def markState (u : Pressure N M) (j : ℕ → MarkJump N M) : ℕ → Pressure N M
  | 0 => u
  | n + 1 =>
    match j n with
    | .discard => markState u j n
    | .jump p => express p.1 p.2 (markState u j n)

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_zero (u : Pressure N M) (j : ℕ → MarkJump N M) : markState u j 0 = u := rfl

omit [NeZero N] [NeZero M] in
theorem markState_succ (u : Pressure N M) (j : ℕ → MarkJump N M) (n : ℕ) :
    markState u j (n + 1)
      = match j n with
        | .discard => markState u j n
        | .jump p => express p.1 p.2 (markState u j n) := rfl

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_succ_discard (u : Pressure N M) (j : ℕ → MarkJump N M) {n : ℕ}
    (h : j n = .discard) : markState u j (n + 1) = markState u j n := by
  rw [markState_succ, h]

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_succ_jump (u : Pressure N M) (j : ℕ → MarkJump N M) {n : ℕ} {p : Jump N M}
    (h : j n = .jump p) :
    markState u j (n + 1) = express p.1 p.2 (markState u j n) := by
  rw [markState_succ, h]

omit [NeZero N] [NeZero M] in
/-- The matrix after `n` marks depends only on the first `n` of them. -/
theorem markState_congr (u : Pressure N M) {j j' : ℕ → MarkJump N M} :
    ∀ n : ℕ, (∀ k < n, j k = j' k) → markState u j n = markState u j' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [markState_succ, markState_succ, ih fun k hk => h k (by omega), h n (by omega)]

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
theorem measurable_markStateHistory (u : Pressure N M) (n k : ℕ) :
    Measurable fun h : (i : Finset.Iic n) → Hold (MarkJump N M) =>
      markState u (jumpExtend fun i => (h i).1) k :=
  (Measurable.of_discrete (f := fun g : (i : Finset.Iic n) → MarkJump N M =>
    markState u (jumpExtend g) k)).comp (measurable_holdHistoryJumps n)

/-- The kernel driving the mark chain: replay the marks so far, and read the band at the
matrix they reach. -/
noncomputable def markDrivingKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M)
    (n : ℕ) : Kernel ((i : Finset.Iic n) → Hold (MarkJump N M)) (Hold (MarkJump N M)) where
  toFun h := markLaw hM hβ (markState u (jumpExtend fun i => (h i).1) (n + 1))
  measurable' :=
    (Measurable.of_discrete (f := fun v : Pressure N M => markLaw hM hβ v)).comp
      (measurable_markStateHistory u n (n + 1))

theorem markDrivingKernel_apply (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M) (n : ℕ)
    (h : (i : Finset.Iic n) → Hold (MarkJump N M)) :
    markDrivingKernel hM hβ u n h
      = markLaw hM hβ (markState u (jumpExtend fun i => (h i).1) (n + 1)) := rfl

instance isMarkovKernel_markDrivingKernel (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M)
    (n : ℕ) : IsMarkovKernel (markDrivingKernel hM hβ u n) :=
  ⟨fun h => by rw [markDrivingKernel_apply]; infer_instance⟩

/-- **The construction of [GL24]**: the sequence of marks of the band, read from the matrix
they drive. -/
noncomputable def markPathMeasure (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (u : Pressure N M) :
    Measure (ℕ → Hold (MarkJump N M)) :=
  jumpHoldMeasure (markDrivingKernel hM hβ u) (markLaw hM hβ u)

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
  rw [markPathMeasure]
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

end SocialNetwork
