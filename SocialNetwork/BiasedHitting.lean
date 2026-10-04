/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.BiasedConsensusExit

/-!
# Lemma 28: hitting a biased ladder within `2β`

Appendix C of arXiv:2607.19651 states Lemma 28 and says only that its proof "follows as the
proof of Lemma 13".  Lemma 13 is proved from two displays and Remark 4:

* the display inside the proof of part 2 of Theorem 2, which bounds `P (R^{β,u} (L) > t)` for
  `u ≠ 0` by the failure of the greedy run and an exponential race among its holding times;
* equation (19), which restarts the process at its first jump from the zero matrix;
* Remark 4, which bounds the failure of the greedy run.

The transposition is the one Appendix C prescribes for Theorem 27: the near-greedy run of
Remark 7 in place of the greedy one, Proposition 23 in place of Proposition 7, Proposition 24 in
place of Proposition 8, and the rate floor `e^{β(M-1)α}` of Remark 8 in place of `e^{β/(M-1)}`.
And equation (19) has nothing to do: by Remark 1 the zero matrix is not in `S^α`, so there is no
starting point to restart from.  What is left is the display, at `t = 2β`, and Remark 4.

## What the transposition does not give for free

Lemma 13 closes with the bound `e^{β/(M-1)} ≥ 1`, which turns the race term
`(M+1)N exp (-e^{β/(M-1)} β / ((M+1)N))` into `(M+1)N e^{-β/((M+1)N)}`: the exponent of Lemma 13
*is* the inverse horizon.  Transposed, the same step gives the exponent `2/K`, with `K` the
horizon of Proposition 23, which the paper never compares with `γ/2`.  The exponent `γ/2` that
Lemma 28 states still holds, because the rate floor `e^{β(M-1)α}` grows with `β`: with
`e^x ≥ 1 + x` the race term is at most `K exp (-2(M-1)αβ²/K)`, a Gaussian in `β`, which any
exponential dominates.  That is the one step supplied here beyond the transposition.

## Main statements

* `SocialNetwork.Bias.exp_le_biasedTotalRate` — Remark 8 as a bound on the total rate.
* `SocialNetwork.Bias.biasedCtsPathMeasure_holdingTime_gt` — every holding time of a run in
  `S^α` is dominated by an exponential of rate `e^{β(M-1)α}`.
* `SocialNetwork.Bias.biasedZeta_pow_le_ctsNearGreedyEvents` — **Proposition 24** on the sample
  space of the process in continuous time.
* `SocialNetwork.Bias.biasedProbHittingGT_le_of_horizon` — the display, for any horizon at which
  the near-greedy run is on `L_α`.
* `SocialNetwork.Bias.biasedProbHitting_le` — **Lemma 28**.
* `SocialNetwork.Bias.tendsto_biasedHittingTime` — **Theorem 27.2**, the limit of the display, as
  Theorem 2.2 is the limit of the unbiased one.
-/

namespace SocialNetwork

namespace Bias

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

section Lemma28

variable [NeZero N] [NeZero M]

omit [NeZero N] [NeZero M] in
/-- **Remark 8**, as a bound on the rate: every profile of `S^α` jumps at total rate at least
`e^{β(M-1)α}`.

**Supplies a step the paper asserts.**  Remark 8 closes with "the jump rate in any state other
than the zero matrix is greater than or equal to `e^{β(M-1)α}`", and the zero matrix is not in
`S^α` (Remark 1).  The actor this needs, one that has heard something, is any actor other than
the one with the null row: the `nₐ` of a profile of `S^α` are pairwise distinct. -/
theorem exp_le_biasedTotalRate (hM : 2 ≤ M) (hN : 2 ≤ N) {γ α β : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) (hβ : 0 ≤ β)
    {P : Profile N M} (hP : IsBiasedState P) :
    Real.exp (β * (((M : ℝ) - 1) * α)) ≤ biasedTotalRate γ β P := by
  obtain ⟨a, ha⟩ := hP.exists_zero_row
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Actor N) by simp only [Fintype.card_fin]; omega) a
  have hheard : 1 ≤ P.heard b := by
    rcases Nat.eq_zero_or_pos (P.heard b) with h0 | h0
    · exact absurd (hP.injective_heard (h0.trans ha.symm)) hb
    · exact h0
  obtain ⟨p, hp⟩ := le_max_pressure hM hγ h hα hheard
  have hterm : Real.exp (β * (((M : ℝ) - 1) * α)) ≤ biasedJumpRate γ β P b p := by
    rw [biasedJumpRate]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hp hβ)
  refine hterm.trans ?_
  rw [biasedTotalRate]
  exact Finset.single_le_sum (f := fun p : Jump N M => biasedJumpRate γ β P p.1 p.2)
    (fun p _ => (biasedJumpRate_pos γ β P p.1 p.2).le) (Finset.mem_univ (b, p))

/-- Every holding time of a run started in `S^α` exceeds `s` with probability at most
`exp (-e^{β(M-1)α} s)`.

**No counterpart in the paper**, which uses it inside the proof of part 2 of Theorem 2 (the
`Eₙ` there) and, through "as the proof of Theorem 2", for Theorem 27.  The `n`-th holding time is
read after `n` restarts at the first jump (`SocialNetwork.Bias.biasedCtsPathMeasure_firstStep_apply`):
`S^α` is stable under every expression, so each restart is again in `S^α`, where the rate is at
least `e^{β(M-1)α}` by `SocialNetwork.Bias.exp_le_biasedTotalRate`.  Unlike the unbiased display,
nothing has to keep the run away from the zero matrix. -/
theorem biasedCtsPathMeasure_holdingTime_gt (hM : 2 ≤ M) (hN : 2 ≤ N) {γ α β : ℝ}
    (hγ : 0 < γ) (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) (hβ : 0 ≤ β)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ (n : ℕ) (P : Profile N M), IsBiasedState P →
      biasedCtsPathMeasure γ β P {ω | s < holdingTime n ω}
        ≤ ENNReal.ofReal (Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α)) * s))) := by
  intro n
  induction n with
  | zero =>
      intro P hP
      rw [biasedCtsPathMeasure_lt_holdingTime γ β P hs]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have := mul_le_mul_of_nonneg_right (exp_le_biasedTotalRate hM hN hγ h hα hβ hP) hs
      linarith
  | succ n ih =>
      intro P hP
      have hS : MeasurableSet {x : Step N M × (ℕ → Step N M) | s < holdingTime n x.2} :=
        measurableSet_lt measurable_const ((measurable_holdingTime n).comp measurable_snd)
      have hset : {ω : ℕ → Step N M | s < holdingTime (n + 1) ω}
          = {ω | (ω 0, shiftStepPath ω) ∈
              {x : Step N M × (ℕ → Step N M) | s < holdingTime n x.2}} := by
        ext ω
        simp only [Set.mem_ofPred_eq, holdingTime_shiftStepPath]
      rw [hset, biasedCtsPathMeasure_firstStep_apply γ β P hS]
      calc ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 P)
              {ω' | (z, ω') ∈ {x : Step N M × (ℕ → Step N M) | s < holdingTime n x.2}}
              ∂(biasedStepLaw γ β P)
          ≤ ∫⁻ _z, ENNReal.ofReal (Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α)) * s)))
              ∂(biasedStepLaw γ β P) :=
            lintegral_mono fun z => ih _ (hP.express z.1.1 z.1.2)
        _ = ENNReal.ofReal (Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α)) * s))) := by
            rw [lintegral_const, measure_univ, mul_one]

omit [NeZero N] [NeZero M] in
/-- The expressed pairs of a realisation of the process in continuous time. -/
theorem measurable_jumps : Measurable fun ω : ℕ → Step N M => fun n => (ω n).1 :=
  measurable_pi_lambda _ fun n => measurable_fst.comp (measurable_pi_apply n)

/-- `⋂_{j=1}^{n} ξ̃_j^{α,u}` on the sample space of the process in continuous time: the near-greedy
event read off the expressed pairs. -/
def ctsNearGreedyEvents (γ : ℝ) (u : Profile N M) (n : ℕ) : Set (ℕ → Step N M) :=
  (fun ω : ℕ → Step N M => fun j => (ω j).1) ⁻¹' nearGreedyEvents γ u n

omit [NeZero N] [NeZero M] in
/-- **No counterpart in the paper**, which does not address measurability. -/
theorem measurableSet_ctsNearGreedyEvents (γ : ℝ) (u : Profile N M) (n : ℕ) :
    MeasurableSet (ctsNearGreedyEvents (N := N) (M := M) γ u n) :=
  measurable_jumps (measurableSet_nearGreedyEvents γ u n)

/-- The near-greedy event of length `m + 1` is a near-greedy first expression followed by a
near-greedy event of length `m` from the profile it reaches. -/
theorem mem_ctsNearGreedyEvents_succ (γ : ℝ) (u : Profile N M) (m : ℕ) (ω : ℕ → Step N M) :
    ω ∈ ctsNearGreedyEvents γ u (m + 1) ↔
      (ω 0).1 ∈ nearArgmaxFinset γ u ∧
        shiftStepPath ω ∈ ctsNearGreedyEvents γ (Profile.express (ω 0).1.1 (ω 0).1.2 u) m := by
  have hcons : (fun n => (ω n).1)
      = consPath (ω 0).1 (fun n => (shiftStepPath ω n).1) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => show (ω (n + 1)).1 = (ω (1 + n)).1; rw [Nat.add_comm]
  show (∀ k < m + 1, IsNearGreedyAt γ u (fun n => (ω n).1) k) ↔
    _ ∧ ∀ k < m, IsNearGreedyAt γ _ (fun n => (shiftStepPath ω n).1) k
  rw [hcons]
  constructor
  · intro hω
    refine ⟨?_, fun k hk => (isNearGreedyAt_consPath_succ γ u _ _ k).1 (hω (k + 1) (by omega))⟩
    exact (isNearGreedyAt_iff_mem γ u _ 0).1 (hω 0 (by omega))
  · rintro ⟨h0, hrest⟩ k hk
    cases k with
    | zero => exact (isNearGreedyAt_iff_mem γ u _ 0).2 h0
    | succ k => exact (isNearGreedyAt_consPath_succ γ u _ _ k).2 (hrest k (by omega))

/-- **Proposition 24** on the sample space of the process in continuous time:
`P (⋂_{j=1}^{m} ξ̃_j^{α,u}) ≥ ζ_{α,β}^m`.

**Follows the paper's proof of Proposition 8**, which Appendix C invokes for Proposition 24,
by the same induction on `m`: here the step is the restart at the first jump rather than the
finite-horizon kernels of `SocialNetwork.Bias.biasedZeta_pow_le`, since the restart is what the
process in continuous time comes with.  The bound on one step is
`SocialNetwork.Bias.biasedZeta_le_biasedJumpPMF_nearArgmaxFinset`, as there. -/
theorem biasedZeta_pow_le_ctsNearGreedyEvents {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 ≤ β) (m : ℕ) :
    ∀ u : Profile N M,
      ENNReal.ofReal (biasedZeta N M γ β) ^ m
        ≤ biasedCtsPathMeasure γ β u (ctsNearGreedyEvents γ u m) := by
  induction m with
  | zero =>
      intro u
      have huniv : ctsNearGreedyEvents (N := N) (M := M) γ u 0 = Set.univ := by
        ext ω
        simp [ctsNearGreedyEvents, nearGreedyEvents]
      rw [pow_zero, huniv, measure_univ]
  | succ m ih =>
      intro u
      set S : Set (Step N M × (ℕ → Step N M)) :=
        {x | x.1.1 ∈ nearArgmaxFinset γ u ∧
          x.2 ∈ ctsNearGreedyEvents γ (Profile.express x.1.1.1 x.1.1.2 u) m} with hSdef
      have hS : MeasurableSet S := by
        have hU : S = ⋃ p : Jump N M, ((Prod.fst ∘ Prod.fst) ⁻¹' ({p} : Set (Jump N M)))
            ∩ (Prod.snd ⁻¹' {ω | p ∈ nearArgmaxFinset γ u ∧
                ω ∈ ctsNearGreedyEvents γ (Profile.express p.1 p.2 u) m}) := by
          ext x
          simp only [hSdef, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
            Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff]
          constructor
          · intro hx
            exact ⟨x.1.1, rfl, hx⟩
          · rintro ⟨p, rfl, hx⟩
            exact hx
        rw [hU]
        refine MeasurableSet.iUnion fun p => ?_
        refine MeasurableSet.inter ((measurable_fst.comp measurable_fst)
          (MeasurableSet.of_discrete : MeasurableSet ({p} : Set (Jump N M)))) (measurable_snd ?_)
        by_cases hp : p ∈ nearArgmaxFinset γ u
        · simp only [hp, true_and]
          exact measurableSet_ctsNearGreedyEvents γ _ m
        · simp only [hp, false_and, Set.ofPred_false]
          exact MeasurableSet.empty
      have hset : ctsNearGreedyEvents γ u (m + 1) = {ω | (ω 0, shiftStepPath ω) ∈ S} :=
        Set.ext fun ω => mem_ctsNearGreedyEvents_succ γ u m ω
      have hA : MeasurableSet (Prod.fst ⁻¹' (↑(nearArgmaxFinset γ u) : Set (Jump N M)) :
          Set (Step N M)) :=
        measurable_fst MeasurableSet.of_discrete
      have := isProbabilityMeasure_expMeasure (biasedTotalRate_pos γ β u)
      rw [hset, biasedCtsPathMeasure_firstStep_apply γ β u hS]
      calc ENNReal.ofReal (biasedZeta N M γ β) ^ (m + 1)
          = ENNReal.ofReal (biasedZeta N M γ β) ^ m * ENNReal.ofReal (biasedZeta N M γ β) :=
            pow_succ _ _
        _ ≤ ENNReal.ofReal (biasedZeta N M γ β) ^ m
              * (biasedJumpPMF γ β u).toMeasure (nearArgmaxFinset γ u) :=
            mul_le_mul' le_rfl (biasedZeta_le_biasedJumpPMF_nearArgmaxFinset hγ hβ u)
        _ = ∫⁻ z, (Prod.fst ⁻¹' (↑(nearArgmaxFinset γ u) : Set (Jump N M))).indicator
              (fun _ => ENNReal.ofReal (biasedZeta N M γ β) ^ m) z ∂(biasedStepLaw γ β u) := by
            rw [lintegral_indicator_const hA, biasedStepLaw, ← Set.prod_univ,
              Measure.prod_prod, measure_univ, mul_one]
        _ ≤ ∫⁻ z, biasedCtsPathMeasure γ β (Profile.express z.1.1 z.1.2 u)
              {ω' | (z, ω') ∈ S} ∂(biasedStepLaw γ β u) := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z.1 ∈ nearArgmaxFinset γ u
            · rw [Set.indicator_of_mem (show z ∈ Prod.fst ⁻¹'
                  (↑(nearArgmaxFinset γ u) : Set (Jump N M)) from hz)]
              have hz' : {ω' : ℕ → Step N M | (z, ω') ∈ S}
                  = ctsNearGreedyEvents γ (Profile.express z.1.1 z.1.2 u) m := by
                ext ω'
                simp only [hSdef, Set.mem_ofPred_eq, hz, true_and]
              rw [hz']
              exact ih _
            · rw [Set.indicator_of_notMem (show z ∉ Prod.fst ⁻¹'
                  (↑(nearArgmaxFinset γ u) : Set (Jump N M)) from hz)]
              exact zero_le

omit [NeZero N] [NeZero M] in
/-- If the `k`-th profile of a realisation is already in `θ`, the hitting time of `θ` is at most
the `k`-th jump time.  The biased twin of `SocialNetwork.hittingTimeCts_le_jumpTime`. -/
theorem biasedHittingTimeCts_le_jumpTime {u : Profile N M} {θ : Set (Profile N M)}
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) {k : ℕ} (hk : k ≠ 0)
    (hmem : stateAfter u (fun n => (ω n).1) k ∈ θ) :
    biasedHittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime k ω) := by
  refine sInf_le ⟨jumpTime k ω, ⟨?_, ?_⟩, rfl⟩
  · exact Finset.sum_nonneg fun n _ => (hpos n).le
  · rw [biasedProcess, jumpCount_jumpTime ω hpos hk]
    exact hmem

/-- **The bound displayed inside the proof of part 2 of Theorem 2, for the biased model.**  For
`u ∈ S^α`, `t > 0`, and a horizon `K` at which the near-greedy run from `u` is on `L_α`,

```
P (R^{α,β,u} (L_α) > t) ≤ 1 - ζ_{α,β}^K + K exp (-e^{β(M-1)α} t / K).
```

**Follows the paper's proof** of the unbiased display (`SocialNetwork.probHittingGT_ladderSet_le_of_ne_zero`),
transposed as Appendix C prescribes for Theorem 27: split on the near-greedy event, which costs
`1 - ζ_{α,β}^K` by Proposition 24; on it the process is on `L_α` at the `K`-th jump, so
`R > t` forces `T_K > t`, hence one of the `K` holding times above `t/K`; each of those is
dominated by an exponential of rate `e^{β(M-1)α}` (Remark 8), and a union bound finishes.

The horizon enters as a hypothesis, so this is proved outright: Proposition 23, which supplies
the horizon, is where `SocialNetwork.Bias.biasedProbHitting_le` meets it. -/
theorem biasedProbHittingGT_le_of_horizon (hM : 2 ≤ M) (hN : 3 ≤ N) {γ α β : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) (hβ : 0 ≤ β)
    {K : ℕ} (hK : 0 < K) {u : Profile N M}
    (hlad : nearGreedyEvents γ u K ⊆ {ω | stateAfter u ω K ∈ biasedLadderSet N M γ})
    (hu : IsBiasedState u) {t : ℝ} (ht : 0 < t) :
    biasedProbHittingGT γ β u (biasedLadderSet N M γ) (ENNReal.ofReal t)
      ≤ ENNReal.ofReal (1 - biasedZeta N M γ β ^ K
          + (K : ℝ) * Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α)) * t) / (K : ℝ))) := by
  have hN2 : 2 ≤ N := by omega
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set r : ℝ := Real.exp (β * (((M : ℝ) - 1) * α)) with hr
  set G := ctsNearGreedyEvents (N := N) (M := M) γ u K with hG
  set Z : Set (ℕ → Step N M) := {ω | ∃ n, holdingTime n ω ≤ 0} with hZ
  have hZnull : biasedCtsPathMeasure γ β u Z = 0 := by
    have hcover : Z = ⋃ n, {ω : ℕ → Step N M | holdingTime n ω ≤ 0} := by
      ext ω
      simp [hZ]
    rw [hcover]
    exact measure_iUnion_null fun n => biasedCtsPathMeasure_holdingTime_nonpos γ β n u
  -- either the run is not near-greedy, or some holding time vanishes, or `T_K` exceeds `t`
  have hsub : {ω : ℕ → Step N M |
        ENNReal.ofReal t < biasedHittingTimeCts u (biasedLadderSet N M γ) ω}
      ⊆ (Gᶜ ∪ Z) ∪ {ω | t < jumpTime K ω} := by
    intro ω hω
    by_cases hg : ω ∈ G
    · by_cases hz : ω ∈ Z
      · exact Or.inl (Or.inr hz)
      · refine Or.inr ?_
        have hpos : ∀ n, 0 < holdingTime n ω := fun n => by
          by_contra hcon
          exact hz ⟨n, not_lt.1 hcon⟩
        have hmem : stateAfter u (fun n => (ω n).1) K ∈ biasedLadderSet N M γ := hlad hg
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).1
          (lt_of_lt_of_le hω (biasedHittingTimeCts_le_jumpTime hpos hK.ne' hmem))
    · exact Or.inl (Or.inl hg)
  -- the near-greedy event: Proposition 24
  have hzpow : biasedZeta N M γ β ^ K ≤ 1 :=
    pow_le_one₀ (biasedZeta_pos N M γ β).le (biasedZeta_le_one N M γ β)
  have h1 : biasedCtsPathMeasure γ β u (Gᶜ ∪ Z) ≤ ENNReal.ofReal (1 - biasedZeta N M γ β ^ K) := by
    refine le_trans (measure_union_le _ _) ?_
    rw [hZnull, add_zero, prob_compl_eq_one_sub (measurableSet_ctsNearGreedyEvents γ u K)]
    have hge : ENNReal.ofReal (biasedZeta N M γ β ^ K) ≤ biasedCtsPathMeasure γ β u G := by
      rw [ENNReal.ofReal_pow (biasedZeta_pos N M γ β).le]
      exact biasedZeta_pow_le_ctsNearGreedyEvents hγ hβ K u
    rw [ENNReal.ofReal_sub _ (pow_nonneg (biasedZeta_pos N M γ β).le K), ENNReal.ofReal_one]
    exact tsub_le_tsub_left hge 1
  -- the clock: Remark 8 and a union bound over the `K` holding times
  have h2 : biasedCtsPathMeasure γ β u {ω | t < jumpTime K ω}
      ≤ ENNReal.ofReal ((K : ℝ) * Real.exp (-(r * t) / (K : ℝ))) := by
    have hcover : {ω : ℕ → Step N M | t < jumpTime K ω}
        ⊆ ⋃ n ∈ Finset.range K, {ω : ℕ → Step N M | t / (K : ℝ) < holdingTime n ω} := by
      intro ω hj
      have hsum : ∑ _n ∈ Finset.range K, t / (K : ℝ) < ∑ n ∈ Finset.range K, holdingTime n ω := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hKr.ne']
        exact hj
      obtain ⟨n, hn, hlt⟩ := Finset.exists_lt_of_sum_lt hsum
      exact Set.mem_biUnion hn hlt
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hbound : ∀ n ∈ Finset.range K,
        biasedCtsPathMeasure γ β u {ω : ℕ → Step N M | t / (K : ℝ) < holdingTime n ω}
          ≤ ENNReal.ofReal (Real.exp (-(r * (t / (K : ℝ))))) := fun n _ =>
      biasedCtsPathMeasure_holdingTime_gt hM hN2 hγ h hα hβ (by positivity) n u hu
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : -(r * (t / (K : ℝ))) = -(r * t) / (K : ℝ) := by field_simp
    rw [this]
  -- putting the two together
  refine le_trans (le_trans (measure_mono hsub) (measure_union_le _ _)) ?_
  refine le_trans (add_le_add h1 h2) ?_
  rw [← ENNReal.ofReal_add (by linarith) (by positivity)]

/-- **Lemma 28.**  `P (R^{α,β,u} (L_α) > 2β) ≤ C e^{-βγ/2}`, with `C` depending only on
`α`, `M` and `N`.

**Follows the paper's proof**, which is "as the proof of Lemma 13": the display
`SocialNetwork.Bias.biasedProbHittingGT_le_of_horizon` at `t = 2β`, with the horizon of
Proposition 23, and Remark 4 for the biased model (`SocialNetwork.Bias.one_sub_le_biasedZeta_pow`)
to bound `1 - ζ_{α,β}^K` by `K MN e^{-βγ/2}`.  Lemma 13's other ingredient, equation (19), is the
restart from the zero matrix, and has nothing to do here: `0 ∉ S^α` (Remark 1).

**Supplies the arithmetic of "putting the inequalities together"**, which in the transposition is
not Lemma 13's.  Lemma 13 bounds its race term with `e^{β/(M-1)} ≥ 1`, and the same step here
would give `e^{-2β/K}`, with `K` the horizon of Proposition 23, not `e^{-βγ/2}`.  The race term is
`K exp (-2β e^{β(M-1)α} / K)`; with `e^x ≥ 1 + x` it is at most `K exp (-2(M-1)αβ² / K)`, and
completing the square, `K exp (γ² K / (32 (M-1) α)) e^{-βγ/2}`.

**Rests on** Proposition 23, which supplies the horizon. -/
theorem biasedProbHitting_le (hM : 2 ≤ M) (hN : 3 ≤ N) {γ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < 1 / ((M : ℝ) - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → ∀ u : Profile N M, IsBiasedState u →
      biasedProbHittingGT γ β u (biasedLadderSet N M γ) (ENNReal.ofReal (2 * β))
        ≤ ENNReal.ofReal (C * Real.exp (-β * γ / 2)) := by
  obtain ⟨K, hK, hlad⟩ := exists_horizon_isBiasedLadder hM hN hγ
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  -- `α = 1/(M-1) - γ`, so that `(M-1) α = 1 - (M-1) γ` is the exponent of Remark 8.
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 / ((M : ℝ) - 1) - γ := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαdef]; linarith
  have h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α := by
    rw [hαdef, mul_sub, mul_one_div_cancel hM1.ne']
    ring
  have hc : 0 < ((M : ℝ) - 1) * α := mul_pos hM1 hα
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  -- The constant, which depends on `K`, `M`, `N` and `γ` only.
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = γ ^ 2 * (K : ℝ) / (32 * (((M : ℝ) - 1) * α)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (K : ℝ) * (((M * N : ℕ) : ℝ) + Real.exp D) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by
    rw [hC]
    refine one_le_mul_of_one_le_of_one_le hK1 ?_
    have := Real.one_le_exp hD0
    have : (0 : ℝ) ≤ ((M * N : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨C, by linarith, fun β hβ u hu => ?_⟩
  rcases hβ.eq_or_lt with hβ0 | hβpos
  · -- At `β = 0` the bound says nothing, since `C ≥ 1`.
    subst hβ0
    refine le_trans (prob_le_one (μ := biasedCtsPathMeasure γ 0 u)) ?_
    rw [show -(0 : ℝ) * γ / 2 = 0 by ring, Real.exp_zero, mul_one]
    exact ENNReal.one_le_ofReal.2 hC1
  refine (biasedProbHittingGT_le_of_horizon hM hN hγ h hα hβ hK (hlad u hu) hu
    (by positivity : (0 : ℝ) < 2 * β)).trans (ENNReal.ofReal_le_ofReal ?_)
  -- Remark 4 for the biased model.
  have h1 : 1 - biasedZeta N M γ β ^ K
      ≤ (K : ℝ) * (((M * N : ℕ) : ℝ) * Real.exp (-β * γ / 2)) := by
    have := one_sub_le_biasedZeta_pow N M γ β K
    rw [show -(β * γ / 2) = -β * γ / 2 by ring] at this
    linarith
  -- The race term: `e^x ≥ 1 + x`, then completing the square.
  have h2 : Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α)) * (2 * β)) / (K : ℝ))
      ≤ Real.exp D * Real.exp (-β * γ / 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hr : 1 + β * (((M : ℝ) - 1) * α) ≤ Real.exp (β * (((M : ℝ) - 1) * α)) := by
      have := Real.add_one_le_exp (β * (((M : ℝ) - 1) * α))
      linarith
    have hstep : -(Real.exp (β * (((M : ℝ) - 1) * α)) * (2 * β)) / (K : ℝ)
        ≤ -((1 + β * (((M : ℝ) - 1) * α)) * (2 * β)) / (K : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ hKr.le
      have := mul_le_mul_of_nonneg_right hr (by linarith : (0 : ℝ) ≤ 2 * β)
      linarith
    have hsq : -((1 + β * (((M : ℝ) - 1) * α)) * (2 * β)) / (K : ℝ) ≤ D + -β * γ / 2 := by
      rw [div_le_iff₀ hKr]
      have hid : (D + -β * γ / 2) * (K : ℝ) + (1 + β * (((M : ℝ) - 1) * α)) * (2 * β)
          = (8 * (((M : ℝ) - 1) * α) * β - γ * (K : ℝ)) ^ 2 / (32 * (((M : ℝ) - 1) * α))
            + 2 * β := by
        rw [hD]
        field_simp
        ring
      have hnn : 0 ≤ (8 * (((M : ℝ) - 1) * α) * β - γ * (K : ℝ)) ^ 2
          / (32 * (((M : ℝ) - 1) * α)) := by positivity
      linarith
    linarith
  calc 1 - biasedZeta N M γ β ^ K
        + (K : ℝ) * Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α)) * (2 * β)) / (K : ℝ))
      ≤ (K : ℝ) * (((M * N : ℕ) : ℝ) * Real.exp (-β * γ / 2))
        + (K : ℝ) * (Real.exp D * Real.exp (-β * γ / 2)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 hKr.le)
    _ = C * Real.exp (-β * γ / 2) := by rw [hC]; ring

end Lemma28

/-! ### Theorem 27.2 -/

section Theorem272

variable [NeZero N] [NeZero M]

/-- **Theorem 27.2.**  For every fixed `δ > 0`,
`sup_{u ∈ S^α} P (R^{α,β,u} (L_α) > e^{-β (M-1) α (1-δ)}) → 0` as `β → +∞`.

The zero matrix does not have to be excluded here: by Remark 1 it is not in `S^α`.

**Follows the paper's proof**, which is "as the proof of Theorem 2" with the rate floor
`e^{β(M-1)α}` of Remark 8: the display `SocialNetwork.Bias.biasedProbHittingGT_le_of_horizon`
at `t = e^{-β(M-1)α(1-δ)}`, with the horizon `K` of Proposition 23.  There
`e^{β(M-1)α} t = e^{β(M-1)αδ} → ∞` kills the race term, and Remark 4 for the biased model kills
`1 - ζ_{α,β}^K ≤ K MN e^{-βγ/2}`.  The bound does not depend on `u`, so it bounds the supremum.
This is `SocialNetwork.tendsto_hittingTime_ladderSet` transposed.

**Rests on** Proposition 23, which supplies the horizon. -/
theorem tendsto_biasedHittingTime (hM : 2 ≤ M) (hN : 3 ≤ N) {γ α : ℝ} (hγ : 0 < γ)
    (h : ((M : ℝ) - 1) * γ = 1 - ((M : ℝ) - 1) * α) (hα : 0 < α) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun β : ℝ => ⨆ u ∈ biasedStateSet N M,
        biasedProbHittingGT γ β u (biasedLadderSet N M γ)
          (ENNReal.ofReal (Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ)))))
      Filter.atTop (nhds 0) := by
  obtain ⟨K, hK, hlad⟩ := exists_horizon_isBiasedLadder hM hN hγ
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hc : 0 < ((M : ℝ) - 1) * α := mul_pos hM1 hα
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  -- The display, uniformly in `u`.
  have key : ∀ β : ℝ, 0 ≤ β →
      (⨆ u ∈ biasedStateSet N M,
        biasedProbHittingGT γ β u (biasedLadderSet N M γ)
          (ENNReal.ofReal (Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ)))))
        ≤ ENNReal.ofReal (1 - biasedZeta N M γ β ^ K
          + (K : ℝ) * Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α))
              * Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ))) / (K : ℝ))) := by
    intro β hβ
    refine iSup₂_le fun u hu => ?_
    exact biasedProbHittingGT_le_of_horizon hM hN hγ h hα hβ hK (hlad u hu) hu (Real.exp_pos _)
  -- Remark 4 for the biased model kills the first term.
  have h1 : Filter.Tendsto (fun β : ℝ => 1 - biasedZeta N M γ β ^ K)
      Filter.atTop (nhds 0) := by
    have hle : ∀ β : ℝ, 1 - biasedZeta N M γ β ^ K
        ≤ (K : ℝ) * (((M * N : ℕ) : ℝ) * Real.exp (-(β * γ / 2))) := fun β => by
      have := one_sub_le_biasedZeta_pow N M γ β K
      linarith
    have hnn : ∀ β : ℝ, 0 ≤ 1 - biasedZeta N M γ β ^ K := fun β => by
      have := pow_le_one₀ (biasedZeta_pos N M γ β).le (biasedZeta_le_one N M γ β) (n := K)
      linarith
    have hlin : Filter.Tendsto (fun β : ℝ => -(β * γ / 2)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp
        ((Filter.tendsto_id.atTop_mul_const hγ).atTop_div_const two_pos)
    have hright := (Real.tendsto_exp_atBot.comp hlin).const_mul ((K : ℝ) * ((M * N : ℕ) : ℝ))
    rw [mul_zero] at hright
    refine squeeze_zero hnn hle (Filter.Tendsto.congr (fun β => ?_) hright)
    simp only [Function.comp_apply]
    ring
  -- The rate floor grows, and kills the race term.
  have h2 : Filter.Tendsto
      (fun β : ℝ => (K : ℝ) * Real.exp (-(Real.exp (β * (((M : ℝ) - 1) * α))
          * Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ))) / (K : ℝ)))
      Filter.atTop (nhds 0) := by
    have hin : ∀ β : ℝ, Real.exp (β * (((M : ℝ) - 1) * α))
        * Real.exp (-β * (((M : ℝ) - 1) * α) * (1 - δ))
        = Real.exp (β * (((M : ℝ) - 1) * α) * δ) := fun β => by
      rw [← Real.exp_add]
      congr 1
      ring
    have hgrow : Filter.Tendsto (fun β : ℝ => Real.exp (β * (((M : ℝ) - 1) * α) * δ))
        Filter.atTop Filter.atTop :=
      Real.tendsto_exp_atTop.comp ((Filter.tendsto_id.atTop_mul_const hc).atTop_mul_const hδ)
    have hneg : Filter.Tendsto
        (fun β : ℝ => -Real.exp (β * (((M : ℝ) - 1) * α) * δ) / (K : ℝ))
        Filter.atTop Filter.atBot :=
      (Filter.tendsto_neg_atTop_atBot.comp hgrow).atBot_div_const hKr
    have h3 := (Real.tendsto_exp_atBot.comp hneg).const_mul (K : ℝ)
    rw [mul_zero] at h3
    refine Filter.Tendsto.congr (fun β => ?_) h3
    simp only [Function.comp_apply]
    rw [hin β]
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have hbE := (ENNReal.continuous_ofReal.tendsto 0).comp hsum
  rw [ENNReal.ofReal_zero] at hbE
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbE
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with β hβ using key β hβ

end Theorem272

end Bias

end SocialNetwork
