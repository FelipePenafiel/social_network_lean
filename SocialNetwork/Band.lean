/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.NonExplosion

/-!
# The band of [GL24]'s Figure 2

The proof of Theorem 1.1 at p. 16 of arXiv:2607.19651 asserts a sandwich (11): the expressions
coming from an actor carrying pressure below `N` "can be constructed in such a way that" they
are the points of a Poisson process of rate `λ = NMe^{βN}`.  [GL24] pp. 12–14 carries that
construction out, and this file is it, written for an arbitrary `SocialNetwork.Band` so that
both the model of equation (3) and the biased model of Section 3 instantiate it.

## The band

A `SocialNetwork.Band` is the data the construction needs: a state space `S`, a positive rate
for each pair at each state, the state each pair leads to, a distinguished family of pairs at
each state, and a bound `λ` on the rate that family carries, uniform in the state.

At the state `v` the band is `[0, λ + q^>(v))`, where `q^>(v)` is the rate carried by the
pairs outside the distinguished family.  [GL24]'s stacking functions `Φ^{<,±}_v` cut the strip
`[0, q^<(v))` into one interval per distinguished pair; the rest of `[0, λ)` is discarded,
which is possible because `q^<(v) ≤ λ` whatever `v` is; and `Φ^{>,±}_v` cut
`[λ, λ + q^>(v))` into one interval per remaining pair.  A mark of the Poisson point process on
`[0,∞)²` is thus read as an element of `SocialNetwork.MarkJump`: a pair, or a discard.

Mathlib has no Poisson point process, so the marks are carried by the jump-hold form instead:
`SocialNetwork.markPathMeasure` draws a mark from `SocialNetwork.markPMF` and then holds for an
exponential time of the band's height `Λ = λ + q^>(v)`, independently.  That is the same law,
and it is the form `SocialNetwork.JumpHold` is written for.

## What this file proves

* `SocialNetwork.measure_markPathMeasure_blowUp` — the marks do not accumulate, given that at
  least one mark in every `b` lands in the strip `[0, λ)`.  This is [GL24]'s "`T^λ` is a
  rate-`λ` Poisson process, so `sup T^λ_n = ∞`", proved by the supermartingale criterion
  `SocialNetwork.measure_holdBlowUp_eq_one` instead.
* `SocialNetwork.iSup_measure_acceptedWithin` — **the law of the first expression**: the first
  mark that is not discarded carries a pair of `B` by time `t` with probability
  `(∑_{p ∈ B} rate p / q(v))(1 - e^{-q(v)t})`, which is the rectangle `B × [0,t]` of
  equation (3).  The geometric number of discarded marks, and the exponential times between
  them, are summed away by a two-sided induction whose fixed point is exact.

`SocialNetwork.BandCollapse` then identifies the realisation the band carries with the process,
`SocialNetwork.Graphical` instantiates the whole for the model of equation (3), and
`SocialNetwork.BiasedGraphical` for the biased model.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SocialNetwork

variable {N M : ℕ}

/-! ### The data the construction runs on -/

/-- The data of [GL24]'s band: a state space, a rate for each pair at each state, the state a
pair leads to, a distinguished family of pairs, and a bound `λ` on the rate it carries that
does not depend on the state.

The distinguished family is what the construction is built around: the strip `[0, λ)` of the
band holds it, and carries rate exactly `λ` whatever the state is, which is why its marks are
the points of a homogeneous process. -/
structure Band (N M : ℕ) (S : Type*) [MeasurableSpace S] [DiscreteMeasurableSpace S] where
  /-- The rate of the pair `p` at the state `s`. -/
  rate : S → Jump N M → ℝ
  rate_pos : ∀ s p, 0 < rate s p
  /-- The state the pair `p` leads to from `s`. -/
  next : S → Jump N M → S
  /-- The distinguished, slow family of pairs at the state `s`. -/
  low : S → Finset (Jump N M)
  /-- The height `λ` of the strip: a bound on the rate the distinguished family carries,
  uniform in the state. -/
  lam : ℝ
  lam_pos : 0 < lam
  low_le_lam : ∀ s, ∑ p ∈ low s, rate s p ≤ lam

namespace Band

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] (bd : Band N M S)

/-- The total rate out of the state `s`. -/
noncomputable def totRate (s : S) : ℝ := ∑ p : Jump N M, bd.rate s p

/-- The rate the distinguished family carries at the state `s`: the height `q^<(s)` of the
red region of [GL24]'s Figure 2. -/
noncomputable def loRate (s : S) : ℝ := ∑ p ∈ bd.low s, bd.rate s p

theorem loRate_nonneg (s : S) : 0 ≤ bd.loRate s :=
  Finset.sum_nonneg fun p _ => (bd.rate_pos s p).le

theorem totRate_nonneg (s : S) : 0 ≤ bd.totRate s :=
  Finset.sum_nonneg fun p _ => (bd.rate_pos s p).le

theorem loRate_le_totRate (s : S) : bd.loRate s ≤ bd.totRate s :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (bd.rate_pos s p).le

theorem totRate_pos [NeZero N] [NeZero M] (s : S) : 0 < bd.totRate s :=
  Finset.sum_pos (fun p _ => bd.rate_pos s p) (univ_jump_nonempty N M)

theorem totRate_ne_zero [NeZero N] [NeZero M] (s : S) : bd.totRate s ≠ 0 :=
  (bd.totRate_pos s).ne'

/-- The weight of a pair in the Gibbs law of equation (3). -/
noncomputable def weight (s : S) (p : Jump N M) : ℝ≥0∞ := ENNReal.ofReal (bd.rate s p)

/-- The Gibbs law of equation (3) at the state `s`: the pair `p` is chosen with probability
proportional to its rate. -/
noncomputable def jumpPMF [NeZero N] [NeZero M] (s : S) : PMF (Jump N M) :=
  PMF.normalize (bd.weight s)
    (by
      rw [tsum_fintype]
      refine fun hcon => absurd (Finset.sum_eq_zero_iff.1 hcon (default : Jump N M)
        (Finset.mem_univ _)) ?_
      exact (ENNReal.ofReal_pos.2 (bd.rate_pos s _)).ne')
    (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.2 fun p _ => ENNReal.ofReal_ne_top)

theorem tsum_weight [NeZero N] [NeZero M] (s : S) :
    ∑' p : Jump N M, bd.weight s p = ENNReal.ofReal (bd.totRate s) := by
  rw [tsum_fintype, Band.totRate]
  exact (ENNReal.ofReal_sum_of_nonneg fun p _ => (bd.rate_pos s p).le).symm

theorem jumpPMF_eq_ofReal [NeZero N] [NeZero M] (s : S) (p : Jump N M) :
    bd.jumpPMF s p = ENNReal.ofReal (bd.rate s p / bd.totRate s) := by
  rw [Band.jumpPMF, PMF.normalize_apply, bd.tsum_weight s, Band.weight,
    ← ENNReal.ofReal_inv_of_pos (bd.totRate_pos s),
    ← ENNReal.ofReal_mul (bd.rate_pos s p).le, ← div_eq_mul_inv]

/-- The law of one step of the process the band carries: the pair follows the Gibbs law of
equation (3), and the holding time is exponential of the total rate, independently. -/
noncomputable def stepLaw [NeZero N] [NeZero M] (s : S) : Measure (Hold (Jump N M)) :=
  (bd.jumpPMF s).toMeasure.prod (expMeasure (bd.totRate s))

instance isProbabilityMeasure_stepLaw [NeZero N] [NeZero M] (s : S) :
    IsProbabilityMeasure (bd.stepLaw s) := by
  have : IsProbabilityMeasure (expMeasure (bd.totRate s)) :=
    isProbabilityMeasure_expMeasure (bd.totRate_pos s)
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- The law of a realisation of the process the band carries. -/
noncomputable def ctsPath [NeZero N] [NeZero M] (u : S) : Measure (ℕ → Hold (Jump N M)) :=
  drivenMeasure bd.next bd.stepLaw u

instance isProbabilityMeasure_ctsPath [NeZero N] [NeZero M] (u : S) :
    IsProbabilityMeasure (bd.ctsPath u) := by
  rw [Band.ctsPath]; infer_instance

/-- The ratio `d = (λ + θ)/λ` the supermartingale of
`SocialNetwork.measure_holdBlowUp_eq_one` discounts by at each mark of the strip. -/
theorem one_lt_discountRatio {θ : ℝ} (hθ : 0 < θ) :
    1 < ENNReal.ofReal ((bd.lam + θ) / bd.lam) := by
  refine ENNReal.one_lt_ofReal.2 ?_
  rw [lt_div_iff₀ bd.lam_pos]
  linarith

end Band

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] (bd : Band N M S)

/-! ### The band of Figure 2 -/

/-- The rate carried by the pairs outside the distinguished family: the blue region of
[GL24]'s Figure 2, of height `q^>(v)`. -/
noncomputable def highRate (v : S) : ℝ := bd.totRate v - bd.loRate v

theorem highRate_nonneg (v : S) : 0 ≤ highRate bd v :=
  sub_nonneg.2 (bd.loRate_le_totRate v)

/-- The height of the band the marks are read in: `λ + q^>(v)`.  Below `λ` sits the strip that
carries the distinguished pairs and the discarded region; above it, the rest. -/
noncomputable def bandRate (v : S) : ℝ :=
  bd.lam + highRate bd v

theorem clockBound_le_bandRate (v : S) :
    bd.lam ≤ bandRate bd v := by
  rw [bandRate]
  linarith [highRate_nonneg bd v]

theorem bandRate_pos (v : S) : 0 < bandRate bd v :=
  lt_of_lt_of_le bd.lam_pos (clockBound_le_bandRate bd v)

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
noncomputable def markWeight (v : S) : MarkJump N M → ℝ≥0∞
  | .discard => ENNReal.ofReal (bd.lam - bd.loRate v)
  | .jump p => ENNReal.ofReal (bd.rate v p)

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
theorem markWeight_ne_top (v : S) (m : MarkJump N M) :
    markWeight bd v m ≠ ∞ := by
  cases m <;> exact ENNReal.ofReal_ne_top

theorem sum_markWeight (v : S) :
    ∑' m : MarkJump N M, markWeight bd v m = ENNReal.ofReal (bandRate bd v) := by
  have hlow : bd.loRate v ≤ bd.lam := bd.low_le_lam v
  rw [tsum_fintype, Fintype.sum_eq_add_sum_compl MarkJump.discard,
    show ({MarkJump.discard} : Finset (MarkJump N M))ᶜ
      = Finset.univ.image MarkJump.jump by
      ext m; cases m <;> simp]
  rw [Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p : Jump N M, markWeight bd v (MarkJump.jump p)
      = ENNReal.ofReal (bd.totRate v) := by
    show ∑ p : Jump N M, ENNReal.ofReal (bd.rate v p) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (bd.rate_pos v p).le]
    rfl
  rw [hjump]
  show ENNReal.ofReal (bd.lam - bd.loRate v) + ENNReal.ofReal (bd.totRate v) = _
  rw [← ENNReal.ofReal_add (by linarith) (bd.totRate_pos v).le]
  congr 1
  rw [bandRate, highRate]
  ring

theorem sum_markWeight_ne_zero (v : S) :
    (∑' m : MarkJump N M, markWeight bd v m) ≠ 0 := by
  rw [sum_markWeight bd v]
  exact (ENNReal.ofReal_pos.2 (bandRate_pos bd v)).ne'

theorem sum_markWeight_ne_top (v : S) :
    (∑' m : MarkJump N M, markWeight bd v m) ≠ ∞ := by
  rw [sum_markWeight bd v]
  exact ENNReal.ofReal_ne_top

/-- **The law of one mark of the band**: a uniform point of `[0, λ + q^>(v))` decodes to the
pair whose interval it lands in, or to `none` when it lands in the discarded region.  The
stacking functions of [GL24] make the decoding explicit; what the argument uses of them is
that each interval has the width of its rate, which is this law. -/
noncomputable def markPMF (v : S) :
    PMF (MarkJump N M) :=
  PMF.normalize (markWeight bd v) (sum_markWeight_ne_zero bd v) (sum_markWeight_ne_top bd v)

theorem markPMF_apply (v : S) (m : MarkJump N M) :
    markPMF bd v m = markWeight bd v m * (∑' q : MarkJump N M, markWeight bd v q)⁻¹ := rfl

/-- The law of one step of the mark chain: the decoded mark, and the time until the next mark
of the band, which is exponential of the band's height. -/
noncomputable def markLaw (v : S) :
    Measure (Hold (MarkJump N M)) :=
  (markPMF bd v).toMeasure.prod (expMeasure (bandRate bd v))

instance isProbabilityMeasure_markLaw (v : S) :
    IsProbabilityMeasure (markLaw bd v) := by
  have : IsProbabilityMeasure (expMeasure (bandRate bd v)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos bd v)
  exact Measure.prod.instIsProbabilityMeasure _ _

/-! ### The chain the marks drive -/

/-- The rule moving the matrix along a mark: a discarded mark leaves it alone, the others
express. -/
def markNext (v : S) : MarkJump N M → S
  | .discard => v
  | .jump p => bd.next v p

/-- The matrix after `n` marks. -/
def markState (u : S) (j : ℕ → MarkJump N M) (n : ℕ) : S :=
  stateAfterJumps (markNext bd) u j n

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_zero (u : S) (j : ℕ → MarkJump N M) : markState bd u j 0 = u := rfl

omit [NeZero N] [NeZero M] in
theorem markState_succ (u : S) (j : ℕ → MarkJump N M) (n : ℕ) :
    markState bd u j (n + 1) = (markNext bd) (markState bd u j n) (j n) := rfl

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_succ_discard (u : S) (j : ℕ → MarkJump N M) {n : ℕ}
    (h : j n = .discard) : markState bd u j (n + 1) = markState bd u j n := by
  rw [markState_succ, h]
  rfl

omit [NeZero N] [NeZero M] in
@[simp]
theorem markState_succ_jump (u : S) (j : ℕ → MarkJump N M) {n : ℕ} {p : Jump N M}
    (h : j n = .jump p) :
    markState bd u j (n + 1) = bd.next (markState bd u j n) p := by
  rw [markState_succ, h]
  rfl

omit [NeZero N] [NeZero M] in
/-- The matrix after `n` marks depends only on the first `n` of them. -/
theorem markState_congr (u : S) {j j' : ℕ → MarkJump N M} (n : ℕ)
    (h : ∀ k < n, j k = j' k) : markState bd u j n = markState bd u j' n :=
  stateAfterJumps_congr (markNext bd) u n h

omit [NeZero N] [NeZero M] in
/-- The kernel driving the mark chain: replay the marks so far, and read the band at the
matrix they reach. -/
noncomputable abbrev markDrivingKernel (u : S) :
    (n : ℕ) → Kernel ((i : Finset.Iic n) → Hold (MarkJump N M)) (Hold (MarkJump N M)) :=
  drivenKernel (markNext bd) (markLaw bd) u

theorem markDrivingKernel_apply (u : S) (n : ℕ)
    (h : (i : Finset.Iic n) → Hold (MarkJump N M)) :
    markDrivingKernel bd u n h
      = markLaw bd (markState bd u (jumpExtend fun i => (h i).1) (n + 1)) := rfl

/-- **The construction of [GL24]**: the sequence of marks of the band, read from the matrix
they drive. -/
noncomputable def markPathMeasure (u : S) :
    Measure (ℕ → Hold (MarkJump N M)) :=
  drivenMeasure (markNext bd) (markLaw bd) u

instance isProbabilityMeasure_markPathMeasure 
    (u : S) : IsProbabilityMeasure (markPathMeasure bd u) := by
  rw [markPathMeasure]; infer_instance

/-! ### The strip of height `λ` -/

/-- The marks of the strip `[0, λ)`: the discarded ones, and the expressions by an actor under
pressure below `N`.  [GL24] writes their times `T^λ`, and the whole point of the construction is
that they arrive at rate `λ` whatever the matrix does. -/
def lambdaFinset (v : S) : Finset (MarkJump N M) :=
  insert MarkJump.discard ((bd.low v).image MarkJump.jump)

omit [NeZero N] [NeZero M] in
theorem mem_lambdaFinset {bd : Band N M S} {v : S} {m : MarkJump N M} :
    m ∈ lambdaFinset bd v ↔ m = .discard ∨ ∃ p ∈ bd.low v, m = .jump p := by
  simp [lambdaFinset, eq_comm]

/-- The strip has height exactly `λ`: the discarded region and the low-pressure intervals fill
`[0, λ)`. -/
theorem sum_markWeight_lambdaFinset (v : S) :
    ∑ m ∈ lambdaFinset bd v, markWeight bd v m = ENNReal.ofReal (bd.lam) := by
  have hlow : bd.loRate v ≤ bd.lam := bd.low_le_lam v
  have hnot : MarkJump.discard ∉ (bd.low v).image MarkJump.jump := by simp
  rw [lambdaFinset, Finset.sum_insert hnot,
    Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p ∈ bd.low v, markWeight bd v (MarkJump.jump p)
      = ENNReal.ofReal (bd.loRate v) := by
    show ∑ p ∈ bd.low v, ENNReal.ofReal (bd.rate v p) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (bd.rate_pos v p).le]
    rfl
  rw [hjump]
  show ENNReal.ofReal (bd.lam - bd.loRate v) + ENNReal.ofReal (bd.loRate v) = _
  rw [← ENNReal.ofReal_add (by linarith) (bd.loRate_nonneg v)]
  congr 1
  ring

/-! ### Lemma 10 of [GL24], read on the marks -/

/-- Mark `k` lands in the strip of height `λ`. -/
def IsLambdaAt (u : S) (k : ℕ) (j : ℕ → MarkJump N M) : Prop :=
  j k ∈ lambdaFinset bd (markState bd u j k)

instance decidableIsLambdaAt (u : S) (k : ℕ) (j : ℕ → MarkJump N M) :
    Decidable (IsLambdaAt bd u k j) := inferInstanceAs (Decidable (_ ∈ _))

omit [NeZero N] [NeZero M] in
/-- Whether mark `k` lands in the strip is read off the first `k + 1` marks. -/
theorem isLambdaAt_congr (u : S) (k : ℕ) (j j' : ℕ → MarkJump N M)
    (h : ∀ i ≤ k, j i = j' i) : IsLambdaAt bd u k j ↔ IsLambdaAt bd u k j' := by
  rw [IsLambdaAt, IsLambdaAt, markState_congr bd u k fun i hi => h i hi.le, h k le_rfl]

omit [NeZero N] [NeZero M] in
/-- At least one mark in every `b` lands in the strip, so after `m` blocks at least `m` do. -/
theorem le_lowCountOf_lambda {u : S} {b : ℕ} {j : ℕ → MarkJump N M}
    (hblock : ∀ m : ℕ, ∃ k, m * b ≤ k ∧ k < m * b + b ∧ IsLambdaAt bd u k j) (m : ℕ) :
    m ≤ lowCountOf (IsLambdaAt bd u) (m * b) j := by
  induction m with
  | zero => simp [lowCountOf]
  | succ m ih =>
      obtain ⟨k, hk1, hk2, hk3⟩ := hblock m
      have hsub : {i ∈ Finset.range (m * b) | IsLambdaAt bd u i j}
          ⊆ {i ∈ Finset.range ((m + 1) * b) | IsLambdaAt bd u i j} := by
        have hrange : Finset.range (m * b) ⊆ Finset.range ((m + 1) * b) := by
          have hsucc : (m + 1) * b = m * b + b := by ring
          rw [hsucc]
          exact Finset.range_subset.2 fun x hx => Finset.mem_range.2 (by omega)
        exact Finset.filter_subset_filter _ hrange
      have hmem : k ∈ {i ∈ Finset.range ((m + 1) * b) | IsLambdaAt bd u i j} := by
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hk3⟩
        have hsucc : (m + 1) * b = m * b + b := by ring
        rw [hsucc]
        omega
      have hnot : k ∉ {i ∈ Finset.range (m * b) | IsLambdaAt bd u i j} := by
        intro hcon
        exact absurd (Finset.mem_range.1 (Finset.mem_filter.1 hcon).1) (by omega)
      have hlt : lowCountOf (IsLambdaAt bd u) (m * b) j
          < lowCountOf (IsLambdaAt bd u) ((m + 1) * b) j :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨k, hmem, hnot⟩)
      omega

/-! ### The marks of the band do not accumulate -/

theorem markPMF_toMeasure_finset (v : S)
    (s : Finset (MarkJump N M)) :
    (markPMF bd v).toMeasure ↑s
      = (∑ m ∈ s, markWeight bd v m) * (ENNReal.ofReal (bandRate bd v))⁻¹ := by
  rw [PMF.toMeasure_apply_finset]
  simp only [markPMF_apply, sum_markWeight bd v]
  rw [← Finset.sum_mul]

omit [NeZero N] [NeZero M] in
theorem compl_lambdaFinset (v : S) :
    (lambdaFinset bd v)ᶜ = ((bd.low v)ᶜ).image MarkJump.jump := by
  ext m
  cases m with
  | discard => simp [lambdaFinset]
  | jump p => simp [lambdaFinset]

omit [NeZero N] [NeZero M] in
theorem sum_markWeight_compl_lambdaFinset (v : S) :
    ∑ m ∈ (lambdaFinset bd v)ᶜ, markWeight bd v m = ENNReal.ofReal (highRate bd v) := by
  rw [compl_lambdaFinset, Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p ∈ (bd.low v)ᶜ, markWeight bd v (MarkJump.jump p)
      = ENNReal.ofReal (∑ p ∈ (bd.low v)ᶜ, bd.rate v p) := by
    show ∑ p ∈ (bd.low v)ᶜ, ENNReal.ofReal (bd.rate v p) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (bd.rate_pos v p).le]
  rw [hjump]
  congr 1
  have hsplit := Finset.sum_compl_add_sum (bd.low v) fun p : Jump N M => bd.rate v p
  rw [highRate, Band.loRate, Band.totRate]
  linarith [hsplit]

/-- **One mark of the band, discounted.**  The strip of height `λ` carries exactly the rate
`λ` out of the band's `λ + q^>(v)`, so discounting the marks that land in it by
`(λ + θ)/λ` costs nothing.  This is where the construction pays: the height of the strip does
not depend on the matrix. -/
theorem lintegral_markLaw_stepWeight_le_one {θ : ℝ}
    (hθ : 0 < θ) (v : S) :
    ∫⁻ z, stepWeight (ENNReal.ofReal ((bd.lam + θ) / bd.lam)) θ
      (lambdaFinset bd v) z ∂(markLaw bd v) ≤ 1 := by
  have hband : 0 < bandRate bd v := bandRate_pos bd v
  have hmass : (markPMF bd v).toMeasure ↑(lambdaFinset bd v)
      = ENNReal.ofReal (bd.lam / bandRate bd v) := by
    rw [markPMF_toMeasure_finset bd v, sum_markWeight_lambdaFinset bd v,
      ← ENNReal.ofReal_inv_of_pos hband,
      ← ENNReal.ofReal_mul (bd.lam_pos).le, ← div_eq_mul_inv]
  have hmassc : (markPMF bd v).toMeasure ((↑(lambdaFinset bd v) : Set (MarkJump N M))ᶜ)
      = ENNReal.ofReal ((bandRate bd v - bd.lam) / bandRate bd v) := by
    rw [← Finset.coe_compl, markPMF_toMeasure_finset bd v,
      sum_markWeight_compl_lambdaFinset bd v, ← ENNReal.ofReal_inv_of_pos hband,
      ← ENNReal.ofReal_mul (highRate_nonneg bd v), ← div_eq_mul_inv]
    congr 2
    rw [bandRate]
    ring
  exact lintegral_stepWeight_le_one hband (bd.lam_pos) hθ
    (bd.lam_pos).le (clockBound_le_bandRate bd v) le_rfl hmass hmassc

/-- **[GL24], steps 4 and 5.**  The marks of the band do not accumulate: the strip of height
`λ` carries at least one mark in every `N`, by Lemma 10, and its marks arrive at rate `λ`
whatever the matrix does. -/
theorem measure_markPathMeasure_blowUp {u : S} {b : ℕ}
    (hblock : ∀ (j : ℕ → MarkJump N M) (m : ℕ),
      ∃ k, m * b ≤ k ∧ k < m * b + b ∧ IsLambdaAt bd u k j) :
    markPathMeasure bd u {ω | holdBlowUp ω = ⊤} = 1 := by
  rw [markPathMeasure, drivenMeasure]
  refine measure_holdBlowUp_eq_one (low := IsLambdaAt bd u) (D := ENNReal.ofReal
      ((bd.lam + 1) / bd.lam)) (θ := 1) _ _ (isLambdaAt_congr bd u)
    (fun n h => lambdaFinset bd (markState bd u (jumpExtend fun i => (h i).1) (n + 1)))
    (lambdaFinset bd u) ?_ ?_ ?_ ?_ one_pos (bd.one_lt_discountRatio one_pos) (b := b) ?_
  · intro z
    rw [IsLambdaAt, markState_zero]
  · intro n h x hx
    have hstate : markState bd u (jumpExtend fun i => (x i).1) (n + 1)
        = markState bd u (jumpExtend fun i => (h i).1) (n + 1) := by
      refine markState_congr bd u (n + 1) fun i hi => ?_
      rw [jumpExtend_apply _ (show i ≤ n + 1 by omega),
        jumpExtend_apply _ (show i ≤ n by omega), ← hx]
      rfl
    rw [IsLambdaAt, jumps_stepExtend, hstate, stepExtend_apply _ (le_refl (n + 1))]
  · exact lintegral_markLaw_stepWeight_le_one bd one_pos u
  · intro n h
    rw [markDrivingKernel_apply]
    exact lintegral_markLaw_stepWeight_le_one bd one_pos _
  · exact fun j q => le_lowCountOf_lambda bd (hblock j) q

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
theorem measure_acceptedWithin_succ (B : Finset (Jump N M))
    (n : ℕ) (t : ℝ) (v : S) :
    markPathMeasure bd v (acceptedWithin B (n + 1) t)
      = markLaw bd v {z | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t}
        + ∫⁻ z in {z : Hold (MarkJump N M) | z.1 = MarkJump.discard},
            markPathMeasure bd v (acceptedWithin B n (t - z.2)) ∂(markLaw bd v) := by
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
      lintegral_drivenMeasure_restart (markNext bd) (markLaw bd) v hfmeas,
      ← lintegral_indicator hD]
    refine lintegral_congr fun z => ?_
    by_cases hd : z ∈ D
    · rw [Set.indicator_of_mem hd, hf]
      simp only [if_pos hd]
      rw [lintegral_indicator_one (measurableSet_acceptedWithin B n (t - z.2))]
      show markPathMeasure bd ((markNext bd) v z.1) _ = _
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
theorem markPathMeasure_holdTime_nonneg (v : S)
    (n : ℕ) : markPathMeasure bd v {ω | (ω n).2 < 0} = 0 := by
  refine drivenMeasure_holdTime_nonneg (markNext bd) (markLaw bd) (fun w => ?_) v n
  have hset : {z : Hold (MarkJump N M) | z.2 < 0}
      = (Set.univ : Set (MarkJump N M)) ×ˢ (Set.Iio (0 : ℝ)) := by
    ext z; simp
  have hnull : expMeasure (bandRate bd w) (Set.Iio (0 : ℝ)) = 0 :=
    measure_mono_null Set.Iio_subset_Iic_self (expMeasure_Iic_zero (bandRate_pos bd w))
  have hprob : IsProbabilityMeasure (expMeasure (bandRate bd w)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos bd w)
  rw [markLaw, hset, Measure.prod_prod, hnull, mul_zero]

/-- Before time zero nothing has been expressed. -/
theorem measure_acceptedWithin_of_neg 
    (B : Finset (Jump N M)) (n : ℕ) {t : ℝ} (ht : t < 0) (v : S) :
    markPathMeasure bd v (acceptedWithin B n t) = 0 := by
  refine measure_mono_null (fun ω hω => ?_)
    (measure_biUnion_null_iff (Finset.range n).countable_toSet |>.2
      fun i _ => markPathMeasure_holdTime_nonneg bd v i)
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
theorem markPMF_toMeasure_image (v : S)
    (B : Finset (Jump N M)) :
    (markPMF bd v).toMeasure {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}
      = ENNReal.ofReal ((∑ p ∈ B, bd.rate v p) / bandRate bd v) := by
  have hcoe : {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p}
      = ↑(B.image MarkJump.jump) := by
    ext m; simp [eq_comm]
  rw [hcoe, markPMF_toMeasure_finset bd v,
    Finset.sum_image (by intro x _ y _ h; cases h; rfl)]
  have hjump : ∑ p ∈ B, markWeight bd v (MarkJump.jump p)
      = ENNReal.ofReal (∑ p ∈ B, bd.rate v p) := by
    show ∑ p ∈ B, ENNReal.ofReal (bd.rate v p) = _
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => (bd.rate_pos v p).le]
  rw [hjump, ← ENNReal.ofReal_inv_of_pos (bandRate_pos bd v),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun p _ => (bd.rate_pos v p).le),
    ← div_eq_mul_inv]

/-- The first mark expresses a pair of `B`, by time `t`. -/
theorem markLaw_apply_accept (B : Finset (Jump N M))
    (v : S) {t : ℝ} (ht : 0 ≤ t) :
    markLaw bd v {z | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t}
      = ENNReal.ofReal ((∑ p ∈ B, bd.rate v p) / bandRate bd v)
        * ENNReal.ofReal (1 - Real.exp (-(bandRate bd v * t))) := by
  have hprob : IsProbabilityMeasure (expMeasure (bandRate bd v)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos bd v)
  have hset : {z : Hold (MarkJump N M) | (∃ p ∈ B, z.1 = MarkJump.jump p) ∧ z.2 ≤ t}
      = {m : MarkJump N M | ∃ p ∈ B, m = MarkJump.jump p} ×ˢ Set.Iic t := rfl
  rw [markLaw, hset, Measure.prod_prod, markPMF_toMeasure_image bd v B,
    expMeasure_Iic_of_nonneg (bandRate_pos bd v) ht]

/-- The first mark is discarded: the chain starts again from the same matrix, after an
exponential time of the band's height. -/
theorem lintegral_discard_markLaw (v : S)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in {z : Hold (MarkJump N M) | z.1 = MarkJump.discard}, f z.2 ∂(markLaw bd v)
      = ENNReal.ofReal ((bd.lam - bd.loRate v) / bandRate bd v)
        * ∫⁻ s, f s ∂(expMeasure (bandRate bd v)) := by
  have hprob : IsProbabilityMeasure (expMeasure (bandRate bd v)) :=
    isProbabilityMeasure_expMeasure (bandRate_pos bd v)
  have hD : ({z : Hold (MarkJump N M) | z.1 = MarkJump.discard})
      = ({MarkJump.discard} : Set (MarkJump N M)) ×ˢ (Set.univ : Set ℝ) := by
    ext z; simp
  have hmass : (markPMF bd v).toMeasure ({MarkJump.discard} : Set (MarkJump N M))
      = ENNReal.ofReal ((bd.lam - bd.loRate v) / bandRate bd v) := by
    have hcoe : ({MarkJump.discard} : Set (MarkJump N M))
        = ↑({MarkJump.discard} : Finset (MarkJump N M)) := by simp
    rw [hcoe, markPMF_toMeasure_finset bd v, Finset.sum_singleton]
    show ENNReal.ofReal (bd.lam - bd.loRate v) * _ = _
    rw [← ENNReal.ofReal_inv_of_pos (bandRate_pos bd v),
      ← ENNReal.ofReal_mul (by
        have := bd.low_le_lam v
        rw [Band.loRate]
        linarith), ← div_eq_mul_inv]
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
theorem totRate_le_bandRate (v : S) :
    bd.totRate v ≤ bandRate bd v := by
  have := bd.low_le_lam v
  rw [bandRate, highRate, Band.loRate]
  linarith

omit [NeZero N] [NeZero M] in
theorem bandRate_sub_totRate (v : S) :
    bandRate bd v - bd.totRate v = bd.lam - bd.loRate v := by
  rw [bandRate, highRate]
  ring

/-- **The step of [GL24]'s construction is the step of the jump-hold one, from above.** -/
theorem measure_acceptedWithin_le (B : Finset (Jump N M))
    (n : ℕ) (t : ℝ) (v : S) :
    markPathMeasure bd v (acceptedWithin B n t)
      ≤ ENNReal.ofReal ((∑ p ∈ B, bd.rate v p) / bd.totRate v
          * (1 - Real.exp (-(bd.totRate v * t)))) := by
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
      · rw [measure_acceptedWithin_of_neg bd B (n + 1) ht v]
        exact zero_le
      set Λ := bandRate bd v with hΛ
      set q := bd.totRate v with hq
      set rB := ∑ p ∈ B, bd.rate v p with hrB
      have hqpos : 0 < q := bd.totRate_pos v
      have hΛpos : 0 < Λ := bandRate_pos bd v
      have hqΛ : q ≤ Λ := totRate_le_bandRate bd v
      have hrB0 : 0 ≤ rB :=
        Finset.sum_nonneg fun p _ => (bd.rate_pos v p).le
      have hrho : Λ - q = bd.lam - bd.loRate v := bandRate_sub_totRate bd v
      have hrho0 : 0 ≤ Λ - q := by linarith
      have hmeasf : Measurable fun s : ℝ =>
          markPathMeasure bd v (acceptedWithin B n (t - s)) :=
        measurable_measure_prodMk_left
          (measurableSet_acceptedWithin_comap (measurable_id (α := ℝ)) B n t)
      rw [measure_acceptedWithin_succ bd B n t v, markLaw_apply_accept bd B v ht,
        lintegral_discard_markLaw bd v hmeasf, ← hrho]
      simp only [← hΛ, ← hrB]
      -- the integral is bounded by the target's own convolution
      have hstep : ∫⁻ s, markPathMeasure bd v (acceptedWithin B n (t - s))
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
theorem sum_le_totRate (v : S) (B : Finset (Jump N M)) :
    ∑ p ∈ B, bd.rate v p ≤ bd.totRate v :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun p _ _ => (bd.rate_pos v p).le

/-- **The step of [GL24]'s construction is the step of the jump-hold one, from below.**  The
error is the chance that the first `n` marks are all discarded. -/
theorem measure_acceptedWithin_ge (B : Finset (Jump N M))
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (v : S) :
    ENNReal.ofReal ((∑ p ∈ B, bd.rate v p) / bd.totRate v
        * (1 - Real.exp (-(bd.totRate v * t))))
      ≤ markPathMeasure bd v (acceptedWithin B n t)
        + ENNReal.ofReal (((bandRate bd v - bd.totRate v) / bandRate bd v) ^ n) := by
  induction n generalizing t with
  | zero =>
      have hle : ENNReal.ofReal ((∑ p ∈ B, bd.rate v p) / bd.totRate v
          * (1 - Real.exp (-(bd.totRate v * t)))) ≤ 1 := by
        refine ENNReal.ofReal_le_one.2 ?_
        have h1 : (∑ p ∈ B, bd.rate v p) / bd.totRate v ≤ 1 :=
          (div_le_one (bd.totRate_pos v)).2 (sum_le_totRate bd v B)
        have h2 : 1 - Real.exp (-(bd.totRate v * t)) ≤ 1 := by
          have := Real.exp_pos (-(bd.totRate v * t)); linarith
        have h3 : 0 ≤ 1 - Real.exp (-(bd.totRate v * t)) := by
          have : Real.exp (-(bd.totRate v * t)) ≤ 1 :=
            Real.exp_le_one_iff.2 (by nlinarith [bd.totRate_pos v])
          linarith
        have h4 : 0 ≤ (∑ p ∈ B, bd.rate v p) / bd.totRate v :=
          div_nonneg (Finset.sum_nonneg fun p _ => (bd.rate_pos v p).le)
            (bd.totRate_pos v).le
        nlinarith
      simpa using le_trans hle le_add_self
  | succ n ih =>
      set Λ := bandRate bd v with hΛ
      set q := bd.totRate v with hq
      set rB := ∑ p ∈ B, bd.rate v p with hrB
      have hqpos : 0 < q := bd.totRate_pos v
      have hΛpos : 0 < Λ := bandRate_pos bd v
      have hqΛ : q ≤ Λ := totRate_le_bandRate bd v
      have hrB0 : 0 ≤ rB :=
        Finset.sum_nonneg fun p _ => (bd.rate_pos v p).le
      have hrho : Λ - q = bd.lam - bd.loRate v := bandRate_sub_totRate bd v
      have hrho0 : 0 ≤ Λ - q := by linarith
      have hr0 : 0 ≤ (Λ - q) / Λ := by positivity
      have hmeasf : Measurable fun s : ℝ =>
          markPathMeasure bd v (acceptedWithin B n (t - s)) :=
        measurable_measure_prodMk_left
          (measurableSet_acceptedWithin_comap (measurable_id (α := ℝ)) B n t)
      rw [measure_acceptedWithin_succ bd B n t v, markLaw_apply_accept bd B v ht,
        lintegral_discard_markLaw bd v hmeasf, ← hrho]
      simp only [← hΛ, ← hrB]
      -- the target's convolution is below the chain's, up to the error
      have hpt : ∀ s : ℝ, ENNReal.ofReal (rB / q * (1 - Real.exp (-(q * (t - s)))))
          ≤ markPathMeasure bd v (acceptedWithin B n (t - s))
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
          ≤ (∫⁻ s, markPathMeasure bd v (acceptedWithin B n (t - s)) ∂(expMeasure Λ))
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
          _ ≤ ∫⁻ s, (markPathMeasure bd v (acceptedWithin B n (t - s))
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
                * ((∫⁻ s, markPathMeasure bd v (acceptedWithin B n (t - s))
                    ∂(expMeasure Λ)) + ENNReal.ofReal (((Λ - q) / Λ) ^ n)) := by
              gcongr
          _ = _ := by
              rw [mul_add, ← add_assoc, ← ENNReal.ofReal_mul hr0]
              congr 2
              ring

/-! ### The macro-step law -/

omit [NeZero N] [NeZero M] in
theorem discardRatio_nonneg (v : S) :
    0 ≤ (bandRate bd v - bd.totRate v) / bandRate bd v :=
  div_nonneg (by linarith [totRate_le_bandRate bd v]) (bandRate_pos bd v).le

theorem discardRatio_lt_one (v : S) :
    (bandRate bd v - bd.totRate v) / bandRate bd v < 1 := by
  rw [div_lt_one (bandRate_pos bd v)]
  linarith [bd.totRate_pos v]

/-- **The law of the first expression of [GL24]'s construction.**  Letting the number of marks
grow, the two bounds meet: the first mark of the band that is not discarded carries a pair in
`B` and does so by time `t` with probability

`(∑_{p ∈ B} rate p / q) (1 - e^{-q t})`,

which is `SocialNetwork.stepLaw` read on the rectangle `B ×ˢ Iic t`.  The geometric number of
discarded marks has been summed away: that is the content of [GL24]'s Figure 2. -/
theorem iSup_measure_acceptedWithin (B : Finset (Jump N M))
    {t : ℝ} (ht : 0 ≤ t) (v : S) :
    ⨆ n, markPathMeasure bd v (acceptedWithin B n t)
      = ENNReal.ofReal ((∑ p ∈ B, bd.rate v p) / bd.totRate v
          * (1 - Real.exp (-(bd.totRate v * t)))) := by
  refine le_antisymm (iSup_le fun n => measure_acceptedWithin_le bd B n t v) ?_
  set L := ⨆ n, markPathMeasure bd v (acceptedWithin B n t) with hLdef
  have hLle : L ≤ 1 := iSup_le fun n => prob_le_one
  have hLne : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hLle
  set δ := (bandRate bd v - bd.totRate v) / bandRate bd v with hδdef
  have hδ0 : 0 ≤ δ := discardRatio_nonneg bd v
  have hδ1 : δ < 1 := discardRatio_lt_one bd v
  have h0 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (δ ^ n)) Filter.atTop (nhds 0) := by
    simp_rw [ENNReal.ofReal_pow hδ0]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hδ1)
  have htend : Filter.Tendsto (fun n : ℕ => L + ENNReal.ofReal (δ ^ n)) Filter.atTop (nhds L) := by
    simpa using h0.const_add L
  refine ge_of_tendsto' htend fun n => ?_
  exact (measure_acceptedWithin_ge bd B n ht v).trans
    (add_le_add (le_iSup (fun n => markPathMeasure bd v (acceptedWithin B n t)) n) le_rfl)

end SocialNetwork
