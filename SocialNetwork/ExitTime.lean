/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Metastability

/-!
# The mean exit time from a consensus set is finite

Theorem 3 and Proposition 12 compare the mean exit times `E (R^{β,u} (C^{-o}))` of two
consensus states through their ratio.  In Lean that mean is `SocialNetwork.expHittingTimeCts`,
valued in `ℝ≥0∞`, and the statements read it through `ENNReal.toReal`, which sends `∞` to `0`.
Were the mean infinite for some consensus state, the ratio would read `0` or a division by `0`,
both statements would be false for large `β`, and Theorem 3, which takes Proposition 12 as a
hypothesis, would hold vacuously.  This file proves that the mean is finite, from every state
of `S` and for every `β ≥ 0`.

**No counterpart in the paper**, which takes the finiteness of the mean exit time for granted
when it divides by it.

## The argument

The exit time is at most the jump time `T_τ` at which the jump chain first enters `C^{-o}`, and
`T_τ = ∑_{n < τ} H_n` is a sum of holding times.  Two facts then close it.

* **The jump chain enters `C^{-o}` quickly.**  The Doeblin minorisation of the skeleton
  (`SocialNetwork.minorisation_iterateKernel`) gives, from every state of `S`, probability at
  least `c > 0` of standing on the canonical ladder `l^{o'}` after `2N` expressions, for any
  opinion `o'`.  Taking `o' ≠ o` puts `l^{o'}` in `C^{-o}`, and the probability of having
  avoided it for `1 + 2Nk` steps is at most `(1 - c)^k`
  (`SocialNetwork.kacAvoid_le_pow`): the expected number of steps is finite.
* **Each holding time has bounded mean.**  Conditionally on the past, the holding time is
  exponential of rate `q_β ≥ M ≥ 1` on `S` (`SocialNetwork.IsState.le_totalRate`), so the
  probability that it exceeds `k` is at most `e^{-k}`, whatever the past.

What connects the two is that the expressed pairs of the process have the law of the skeleton
(`SocialNetwork.map_ctsPathMeasure_jumps`), which is the paper's `Ũ_n = U_{T_n}` of
Definition 3: the minorisation is a statement about the skeleton, and the exit time is one about
the process.

## Main results

* `SocialNetwork.kacAvoid_le_pow` — the geometric tail of the time to reach a point at which
  an iterate of a kernel is minorised.
* `SocialNetwork.map_ctsPathMeasure_jumps` — the expressed pairs of the process are distributed
  as the skeleton.
* `SocialNetwork.expHittingTimeCts_lt_top` — the mean hitting time of any set containing a
  canonical ladder is finite.
* `SocialNetwork.expHittingTimeCts_consensusSetOther_lt_top` — the mean exit time from a
  consensus set is finite.
* `SocialNetwork.expHittingTimeCts_consensusSetOther_pos` — and positive, so that the ratios
  of Theorem 3 compare two positive reals.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

/-! ### Avoiding a point at which an iterate is minorised -/

section Tail

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- Avoiding `l` for `j + n` steps entails avoiding it for `j` steps from wherever the chain
stands at time `n`. -/
theorem kacAvoid_add_le (κ : Kernel α α) [IsMarkovKernel κ] (l : α) (j : ℕ) :
    ∀ (n : ℕ) (v : α),
      kacAvoid κ l (j + n) v ≤ ∫⁻ w, kacAvoid κ l j w ∂(iterateKernel κ n v)
  | 0, v => by
      rw [Nat.add_zero, iterateKernel_zero, Kernel.id_apply, lintegral_dirac]
  | n + 1, v => by
      rw [← Nat.add_assoc, kacAvoid_succ]
      calc Set.indicator {l}ᶜ (fun v => ∫⁻ w, kacAvoid κ l (j + n) w ∂(κ v)) v
          ≤ ∫⁻ w, kacAvoid κ l (j + n) w ∂(κ v) := Set.indicator_le_self _ _ _
        _ ≤ ∫⁻ w, ∫⁻ w', kacAvoid κ l j w' ∂(iterateKernel κ n w) ∂(κ v) :=
            lintegral_mono fun w => kacAvoid_add_le κ l j n w
        _ = ∫⁻ w', kacAvoid κ l j w' ∂(iterateKernel κ (n + 1) v) := by
            rw [iterateKernel_succ', Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]

/-- **The geometric tail.**  If the `n`-step kernel puts mass at least `c` on `l` from every
state of an absorbing set `S`, then from `S` the chain avoids `l` for `1 + kn` steps with
probability at most `(1 - c)^k`: every block of `n` steps gives it a fresh chance `c` of
landing there. -/
theorem kacAvoid_le_pow (κ : Kernel α α) [IsMarkovKernel κ] {S : Set α} {l : α} {c : ℝ≥0∞}
    {n : ℕ} (habs : ∀ x ∈ S, κ x Sᶜ = 0) (hmin : ∀ x ∈ S, c ≤ iterateKernel κ n x {l}) :
    ∀ (k : ℕ), ∀ v ∈ S, kacAvoid κ l (1 + k * n) v ≤ (1 - c) ^ k
  | 0, v, _ => by simpa using kacAvoid_le_one κ l 1 v
  | k + 1, v, hv => by
      rw [show 1 + (k + 1) * n = 1 + k * n + n by ring]
      refine (kacAvoid_add_le κ l (1 + k * n) n v).trans ?_
      have hS : iterateKernel κ n v Sᶜ = 0 := iterateKernel_absorbing κ habs n v hv
      have hle : ∀ᵐ w ∂(iterateKernel κ n v),
          kacAvoid κ l (1 + k * n) w ≤ Set.indicator {l}ᶜ (fun _ => (1 - c) ^ k) w := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS] with w hw
        have hwS : w ∈ S := by simpa using hw
        by_cases hwl : w = l
        · rw [hwl, add_comm, kacAvoid_succ, Set.indicator_of_notMem (by simp)]
          exact zero_le
        · rw [Set.indicator_of_mem (by simpa using hwl)]
          exact kacAvoid_le_pow κ habs hmin k w hwS
      calc ∫⁻ w, kacAvoid κ l (1 + k * n) w ∂(iterateKernel κ n v)
          ≤ ∫⁻ w, Set.indicator {l}ᶜ (fun _ => (1 - c) ^ k) w ∂(iterateKernel κ n v) :=
            lintegral_mono_ae hle
        _ = (1 - c) ^ k * iterateKernel κ n v {l}ᶜ :=
            lintegral_indicator_const (measurableSet_singleton l).compl _
        _ ≤ (1 - c) ^ k * (1 - c) := by
            gcongr
            rw [prob_compl_eq_one_sub (measurableSet_singleton l)]
            exact tsub_le_tsub_left (hmin v hv) 1
        _ = (1 - c) ^ (k + 1) := (pow_succ _ k).symm

/-- `∑_m r^{⌊m/n⌋} = n ∑_k r^k`: each power is taken `n` times. -/
theorem tsum_pow_div (r : ℝ≥0∞) {n : ℕ} (hn : 0 < n) :
    ∑' m : ℕ, r ^ (m / n) = n * ∑' k : ℕ, r ^ k := by
  have : NeZero n := ⟨hn.ne'⟩
  have hdiv : ∀ c : ℕ × Fin n, (Nat.divModEquiv n).symm c / n = c.1 := by
    rintro ⟨k, i⟩
    simp only [Nat.divModEquiv_symm_apply]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt i.2, Nat.zero_add]
  calc ∑' m : ℕ, r ^ (m / n) = ∑' c : ℕ × Fin n, r ^ c.1 := by
        rw [← (Nat.divModEquiv n).symm.tsum_eq]
        exact tsum_congr fun c => by rw [hdiv]
    _ = ∑' k : ℕ, ∑' _ : Fin n, r ^ k := ENNReal.tsum_prod (f := fun k (_ : Fin n) => r ^ k)
    _ = n * ∑' k : ℕ, r ^ k := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun k => ?_
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **The time to reach `l` has finite mean** from every state of `S`, under the hypotheses of
`SocialNetwork.kacAvoid_le_pow` with `c > 0`: `∑_m P_v (the chain avoids l for m steps) < ∞`. -/
theorem tsum_kacAvoid_ne_top (κ : Kernel α α) [IsMarkovKernel κ] {S : Set α} {l : α}
    {c : ℝ≥0∞} {n : ℕ} (hn : 0 < n) (hc : 0 < c) (habs : ∀ x ∈ S, κ x Sᶜ = 0)
    (hmin : ∀ x ∈ S, c ≤ iterateKernel κ n x {l}) {v : α} (hv : v ∈ S) :
    ∑' m : ℕ, kacAvoid κ l m v ≠ ∞ := by
  have hstep : ∀ m : ℕ, kacAvoid κ l (m + 1) v ≤ (1 - c) ^ (m / n) := by
    intro m
    have hle : 1 + m / n * n ≤ m + 1 := by
      have := Nat.div_mul_le_self m n
      omega
    exact (kacAvoid_antitone κ l hle v).trans (kacAvoid_le_pow κ habs hmin (m / n) v hv)
  have hlt : 1 - c < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc.ne'
  have hgeom : ∑' k : ℕ, (1 - c) ^ k ≠ ∞ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hlt).ne'
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.one_ne_top (kacAvoid_le_one κ l 0 v),
    ?_⟩
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hstep)
  rw [tsum_pow_div _ hn]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hgeom

end Tail

/-! ### The expressed pairs of the process are the skeleton -/

section Bridge

/-- Two finite measures on a space of sequences that agree on every initial segment agree.
This is the uniqueness of a projective limit, `MeasureTheory.IsProjectiveLimit.unique`, read
on the initial segments `Iic b`, which are cofinal among the finite sets of indices. -/
theorem eq_of_map_frestrictLe {X : Type*} [MeasurableSpace X] {μ ν : Measure (ℕ → X)}
    [IsFiniteMeasure ν]
    (h : ∀ b, μ.map (Preorder.frestrictLe (π := fun _ : ℕ => X) b)
      = ν.map (Preorder.frestrictLe (π := fun _ : ℕ => X) b)) : μ = ν := by
  have hν : IsProjectiveLimit ν (fun J : Finset ℕ => ν.map J.restrict) := fun _ => rfl
  have hμ : IsProjectiveLimit μ (fun J : Finset ℕ => ν.map J.restrict) := by
    intro J
    have hJ : J ⊆ Finset.Iic (J.sup id) := J.subset_Iic_sup_id
    show μ.map J.restrict = ν.map J.restrict
    rw [← Finset.restrict₂_comp_restrict hJ,
      ← Measure.map_map (Finset.measurable_restrict₂ hJ) (Finset.measurable_restrict _),
      ← Measure.map_map (Finset.measurable_restrict₂ hJ) (Finset.measurable_restrict _),
      ← Preorder.frestrictLe, h]
  exact hμ.unique hν

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The expressed pairs of a realisation of the process, its holding times forgotten. -/
def stepJumps (ω : ℕ → Step N M) : ℕ → Jump N M := fun k => (ω k).1

omit [NeZero N] [NeZero M] in
theorem measurable_stepJumps : Measurable (stepJumps (N := N) (M := M)) :=
  measurable_pi_lambda _ fun k => measurable_fst.comp (measurable_pi_apply k)

omit [NeZero N] [NeZero M] in
/-- The matrices a realisation of the process shows are those of the skeleton along its
expressed pairs. -/
theorem state_ofStepPath (u : Pressure N M) (ω : ℕ → Step N M) (k : ℕ) :
    (Trajectory.ofStepPath ω).state u k = skeleton u k (stepJumps ω) := rfl

omit [NeZero N] [NeZero M] in
/-- One more step appended to a history: the expressed pairs are those of `x` exactly when the
history carries the first ones and the new step the last. -/
theorem extendStepHistory_jumps_eq_iff {n : ℕ} (h : (i : Finset.Iic n) → Step N M)
    (z : Step N M) (x : (i : Finset.Iic (n + 1)) → Jump N M) :
    (fun i => (extendStepHistory h z i).1) = x
      ↔ (fun i => (h i).1) = Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x
        ∧ z.1 = x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
  constructor
  · intro hx
    refine ⟨funext fun i => ?_, ?_⟩
    · have hi : i.1 ≤ n := Finset.mem_Iic.1 i.2
      have := congrFun hx ⟨i.1, Finset.mem_Iic.2 (by omega)⟩
      simpa [extendStepHistory, hi] using this
    · have := congrFun hx ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩
      simpa [extendStepHistory] using this
  · rintro ⟨h1, h2⟩
    funext i
    by_cases hi : i.1 ≤ n
    · have := congrFun h1 ⟨i.1, Finset.mem_Iic.2 hi⟩
      simpa [extendStepHistory, hi] using this
    · have hin : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ :=
        Subtype.ext (by have := Finset.mem_Iic.1 i.2; simp only; omega)
      subst hin
      simpa [extendStepHistory] using h2

/-- **The law of the expressed pairs of a finite history of the process**: the probability of
one prescribed sequence of pairs is the product of the one-step probabilities along it, as for
the skeleton (`SocialNetwork.historyMeasure_singleton`).  The holding times integrate out,
because each is drawn independently of the pair it follows. -/
theorem ctsHistoryMeasure_jumps_singleton (β : ℝ) (u : Pressure N M) (n : ℕ)
    (x : (i : Finset.Iic n) → Jump N M) :
    ctsHistoryMeasure β u n
        ((fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1) ⁻¹' {x})
      = ∏ m ∈ Finset.range (n + 1),
          jumpPMF β (stateAfterHistory u x m) (ofHistoryPath x m) := by
  induction n with
  | zero =>
      have h0 : ctsHistoryMeasure β u 0 = (stepLaw β u).map toStepHistoryZero := by
        unfold ctsHistoryMeasure
        rw [Kernel.partialTraj_self, Measure.id_comp]
      have hpre : toStepHistoryZero ⁻¹'
            ((fun h : (i : Finset.Iic 0) → Step N M => fun i => (h i).1) ⁻¹' {x})
          = (fun z : Step N M => z.1) ⁻¹' {ofHistoryPath x 0} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hz
          have := congrFun hz ⟨0, Finset.mem_Iic.2 le_rfl⟩
          simpa [ofHistoryPath, toStepHistoryZero] using this
        · intro hz
          funext i
          have hi : i = (⟨0, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic 0) :=
            Subtype.ext (Nat.le_zero.1 (Finset.mem_Iic.1 i.2))
          rw [hi]
          simpa [ofHistoryPath, toStepHistoryZero] using hz
      rw [h0, Measure.map_apply measurable_toStepHistoryZero
          ((measurable_stepHistoryJumps 0) (measurableSet_singleton x)), hpre,
        stepLaw_preimage_fst, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        Finset.prod_range_one]
      rfl
  | succ n ih =>
      have hmeasS : MeasurableSet
          ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x}) :=
        (measurable_stepHistoryJumps (n + 1)) (measurableSet_singleton x)
      have hstep : ctsHistoryMeasure β u (n + 1)
            ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
              (ctsDrivingKernel β u) n (n + 1) h
              ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
              ∂(ctsHistoryMeasure β u n) := by
        unfold ctsHistoryMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply hmeasS (Kernel.aemeasurable _)]
      set h₀ := Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x with hh₀
      have hind : (fun h : (i : Finset.Iic n) → Step N M =>
            Kernel.partialTraj (X := fun _ : ℕ => Step N M) (ctsDrivingKernel β u) n (n + 1) h
              ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x}))
          = Set.indicator
              ((fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1) ⁻¹' {h₀})
              (fun _ => jumpPMF β (stateAfterHistory u h₀ (n + 1))
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)) := by
        funext h
        rw [ctsPartialTraj_succ_apply, Measure.map_apply (measurable_extendStepHistory h) hmeasS]
        by_cases hc : (fun i => (h i).1) = h₀
        · rw [Set.indicator_of_mem (by simpa using hc)]
          have hpre : extendStepHistory h ⁻¹'
                ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
              = (fun z : Step N M => z.1) ⁻¹' {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩} := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            rw [extendStepHistory_jumps_eq_iff]
            exact ⟨fun hz => hz.2, fun hz => ⟨hc, hz⟩⟩
          have hst : (Trajectory.ofStepHistory h).state u (n + 1)
              = stateAfterHistory u h₀ (n + 1) := by
            rw [← hc]
            rfl
          rw [hpre, stepLaw_preimage_fst,
            PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), hst]
        · rw [Set.indicator_of_notMem (by simpa using hc)]
          have hpre : extendStepHistory h ⁻¹'
                ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
              = ∅ := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
              iff_false]
            rw [extendStepHistory_jumps_eq_iff]
            exact fun hz => hc hz.1
          rw [hpre, measure_empty]
      have hlhs : ctsHistoryMeasure β u (n + 1)
            ((fun h : (i : Finset.Iic (n + 1)) → Step N M => fun i => (h i).1) ⁻¹' {x})
          = jumpPMF β (stateAfterHistory u h₀ (n + 1)) (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
            * ∏ m ∈ Finset.range (n + 1),
                jumpPMF β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m) := by
        rw [hstep, hind, lintegral_indicator
            ((measurable_stepHistoryJumps n) (measurableSet_singleton h₀)),
          setLIntegral_const, ih h₀]
      have hprod : ∀ m ∈ Finset.range (n + 1),
          jumpPMF β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m)
            = jumpPMF β (stateAfterHistory u x m) (ofHistoryPath x m) := by
        intro m hm
        have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        have h1 : stateAfterHistory u h₀ m = stateAfterHistory u x m :=
          (skeleton_ofHistoryPath_eq (hx := hh₀.symm) u (k := m) (by omega)).symm
        have h2 : ofHistoryPath h₀ m = ofHistoryPath x m :=
          (ofHistoryPath_eq (hx := hh₀.symm) hmn).symm
        rw [h1, h2]
      have hlast : jumpPMF β (stateAfterHistory u h₀ (n + 1))
          (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
          = jumpPMF β (stateAfterHistory u x (n + 1)) (ofHistoryPath x (n + 1)) := by
        rw [ofHistoryPath_apply x (le_refl (n + 1)),
          show stateAfterHistory u h₀ (n + 1) = stateAfterHistory u x (n + 1) from
            (skeleton_ofHistoryPath_eq (hx := hh₀.symm) u (k := n + 1) le_rfl).symm]
      rw [hlhs, Finset.prod_congr rfl hprod, hlast,
        Finset.prod_range_succ (f := fun m =>
          jumpPMF β (stateAfterHistory u x m) (ofHistoryPath x m)) (n := n + 1)]
      ring

/-- The expressed pairs of a finite history of the process have the law of the same history of
the skeleton. -/
theorem ctsHistoryMeasure_map_jumps (β : ℝ) (u : Pressure N M) (n : ℕ) :
    (ctsHistoryMeasure β u n).map
        (fun h : (i : Finset.Iic n) → Step N M => fun i => (h i).1)
      = historyMeasure β u n := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.map_apply (measurable_stepHistoryJumps n) (measurableSet_singleton x),
    ctsHistoryMeasure_jumps_singleton, historyMeasure_singleton]

/-- **The expressed pairs of the process are distributed as the skeleton.**  This is the
paper's `Ũ_n = U_{T_n}` of Definition 3, read on the two sample spaces of this library: the
skeleton is the jump chain of the process.

**No counterpart in the paper**, where the skeleton is *defined* as the jump chain; here the
two are built separately, from two applications of the Ionescu-Tulcea theorem, and this is
where they meet. -/
theorem map_ctsPathMeasure_jumps (β : ℝ) (u : Pressure N M) :
    (ctsPathMeasure β u).map stepJumps = pathMeasure β u := by
  refine eq_of_map_frestrictLe fun b => ?_
  rw [Measure.map_map (Preorder.measurable_frestrictLe b) measurable_stepJumps]
  have hcomp : Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b ∘ stepJumps
      = (fun h : (i : Finset.Iic b) → Step N M => fun i => (h i).1)
        ∘ Preorder.frestrictLe (π := fun _ : ℕ => Step N M) b := rfl
  rw [hcomp, ← Measure.map_map (measurable_stepHistoryJumps b)
      (Preorder.measurable_frestrictLe b), ctsPathMeasure_map_frestrictLe,
    ctsHistoryMeasure_map_jumps]
  unfold historyMeasure pathMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe b), Kernel.traj_map_frestrictLe]

/-- An event about the expressed pairs alone has the same probability under the process as
under the skeleton. -/
theorem ctsPathMeasure_preimage_stepJumps (β : ℝ) (u : Pressure N M)
    {E : Set (ℕ → Jump N M)} (hE : MeasurableSet E) :
    ctsPathMeasure β u (stepJumps ⁻¹' E) = pathMeasure β u E := by
  rw [← map_ctsPathMeasure_jumps, Measure.map_apply measurable_stepJumps hE]

end Bridge

/-! ### The holding times -/

section Holding

/-- `x ≤ #{k ∈ ℕ : k < x}`, read in `ℝ≥0∞`: a real number is at most the number of naturals
below it, rounded up. -/
theorem ofReal_le_tsum_indicator_Ioi (x : ℝ) :
    ENNReal.ofReal x ≤ ∑' k : ℕ, Set.indicator (Set.Ioi (k : ℝ)) (fun _ => (1 : ℝ≥0∞)) x := by
  calc ENNReal.ofReal x ≤ ENNReal.ofReal (⌈x⌉₊ : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil x)
    _ = ∑ k ∈ Finset.range ⌈x⌉₊, Set.indicator (Set.Ioi (k : ℝ)) (fun _ => (1 : ℝ≥0∞)) x := by
        have h : ∀ k ∈ Finset.range ⌈x⌉₊,
            Set.indicator (Set.Ioi (k : ℝ)) (fun _ => (1 : ℝ≥0∞)) x = 1 := fun k hk =>
          Set.indicator_of_mem (Set.mem_Ioi.2 (Nat.lt_ceil.1 (Finset.mem_range.1 hk))) _
        rw [Finset.sum_congr rfl h]
        simp
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- `∑_k e^{-k}` is finite. -/
theorem tsum_ofReal_exp_neg_ne_top :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) ≠ ∞ := by
  have hpow : ∀ k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ)))
      = ENNReal.ofReal (Real.exp (-1)) ^ k := by
    intro k
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [tsum_congr hpow, ENNReal.tsum_geometric]
  refine ENNReal.inv_ne_top.2 (tsub_pos_of_lt ?_).ne'
  exact ENNReal.ofReal_lt_one.2 (Real.exp_lt_one_iff.2 (by norm_num))

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- **The holding-time bound, relative to the history.**  If, after every history of the
first `n + 1` steps lying in `G`, the holding time that follows has `expMeasure` mass at most
`c` on `A`, then the probability that the history lies in `G` and the holding time in `A` is at
most `c` times the probability of `G`.  This is
`SocialNetwork.ctsPathMeasure_history_holdingTime_le` with the factor `P (G)` kept. -/
theorem ctsPathMeasure_history_holdingTime_le_mul (β : ℝ) (u : Pressure N M) (n : ℕ)
    {G : Set ((i : Finset.Iic n) → Step N M)} (hmeasG : MeasurableSet G) {A : Set ℝ}
    (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hc : ∀ h ∈ G,
      expMeasure (totalRate β ((Trajectory.ofStepHistory h).state u (n + 1))) A ≤ c) :
    ctsPathMeasure β u ((Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
        ∩ {ω | holdingTime (n + 1) ω ∈ A})
      ≤ c * ctsPathMeasure β u (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G) := by
  set S : Set ((i : Finset.Iic (n + 1)) → Step N M) :=
    (Preorder.frestrictLe₂ (π := fun _ : ℕ => Step N M) (Nat.le_succ n) ⁻¹' G) ∩
      ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
        (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) with hS
  have hmeasLast : MeasurableSet ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
      (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A) :=
    (measurable_snd.comp (measurable_pi_apply _)) hA
  have hmeasS : MeasurableSet S :=
    ((Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Step N M) (Nat.le_succ n)) hmeasG).inter
      hmeasLast
  have hsplit : (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
        ∩ {ω : ℕ → Step N M | holdingTime (n + 1) ω ∈ A}
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) (n + 1) ⁻¹' S := rfl
  have hG : ctsPathMeasure β u (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) n ⁻¹' G)
      = ctsHistoryMeasure β u n G := by
    rw [← Measure.map_apply (Preorder.measurable_frestrictLe n) hmeasG,
      ctsPathMeasure_map_frestrictLe]
  rw [hsplit, ← Measure.map_apply (Preorder.measurable_frestrictLe (n + 1)) hmeasS,
    ctsPathMeasure_map_frestrictLe, hG]
  have hstep : ctsHistoryMeasure β u (n + 1) S
      = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
          (ctsDrivingKernel β u) n (n + 1) h S ∂(ctsHistoryMeasure β u n) := by
    unfold ctsHistoryMeasure
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
      Measure.bind_apply hmeasS (Kernel.aemeasurable _)]
  rw [hstep]
  calc ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Step N M)
        (ctsDrivingKernel β u) n (n + 1) h S ∂(ctsHistoryMeasure β u n)
      ≤ ∫⁻ h, G.indicator (fun _ => c) h ∂(ctsHistoryMeasure β u n) := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ G
        · rw [Set.indicator_of_mem hh]
          refine le_trans (measure_mono Set.inter_subset_right) ?_
          have hcomp : ((fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩).2) ⁻¹' A)
              = (fun x : (i : Finset.Iic (n + 1)) → Step N M =>
                  x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
                ((fun z : Step N M => z.2) ⁻¹' A) := rfl
          rw [hcomp, ctsPartialTraj_last_apply β u n h (measurable_snd hA),
            stepLaw_preimage_snd]
          exact hc h hh
        · rw [Set.indicator_of_notMem hh]
          refine le_trans (measure_mono Set.inter_subset_left) (le_of_eq ?_)
          rw [ctsPartialTraj_frestrictLe₂_apply β u n h hmeasG,
            Measure.dirac_apply' _ hmeasG, Set.indicator_of_notMem hh]
    _ = c * ctsHistoryMeasure β u n G := lintegral_indicator_const hmeasG c

/-- On `S`, a holding time exceeds `k` with probability at most `e^{-k}`: its rate is at least
`M ≥ 1`. -/
theorem expMeasure_totalRate_Ioi_le (hM : 2 ≤ M) (β : ℝ) {v : Pressure N M} (hv : IsState v)
    (k : ℕ) :
    expMeasure (totalRate β v) (Set.Ioi (k : ℝ)) ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [expMeasure_Ioi_of_nonneg (totalRate_pos β v) (Nat.cast_nonneg k)]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hq : (1 : ℝ) ≤ totalRate β v :=
    le_trans (by exact_mod_cast (by omega : 1 ≤ M)) (hv.le_totalRate β)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

end Holding

/-! ### The mean exit time -/

section ExitTime

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The realisations whose first `n + 1` matrices all differ from `l`. -/
def avoidUpTo (u l : Pressure N M) (n : ℕ) : Set (ℕ → Step N M) :=
  {ω | ∀ k ≤ n, (Trajectory.ofStepPath ω).state u k ≠ l}

omit [NeZero N] [NeZero M] in
theorem avoidUpTo_eq_preimage (u l : Pressure N M) (n : ℕ) :
    avoidUpTo u l n = stepJumps ⁻¹' avoidSet u l (n + 1) := by
  ext ω
  simp only [avoidUpTo, avoidSet, Set.mem_preimage, Set.mem_ofPred_eq, state_ofStepPath]
  exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩

omit [NeZero N] [NeZero M] in
theorem measurableSet_avoidUpTo (u l : Pressure N M) (n : ℕ) :
    MeasurableSet (avoidUpTo u l n) := by
  rw [avoidUpTo_eq_preimage]
  exact measurable_stepJumps (measurableSet_avoidSet u l (n + 1))

omit [NeZero N] [NeZero M] in
/-- After the first `m + 1` steps, whether the first `m + 2` matrices avoid `l` is decided. -/
theorem avoidUpTo_succ_eq_preimage (u l : Pressure N M) (m : ℕ) :
    avoidUpTo u l (m + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Step N M) m ⁻¹'
        {h | ∀ k ≤ m + 1, (Trajectory.ofStepHistory h).state u k ≠ l} := by
  ext ω
  simp only [avoidUpTo, Set.mem_preimage, Set.mem_ofPred_eq]
  have hst : ∀ k ≤ m + 1, (Trajectory.ofStepHistory
        (Preorder.frestrictLe (π := fun _ : ℕ => Step N M) m ω)).state u k
      = (Trajectory.ofStepPath ω).state u k :=
    fun k hk => Trajectory.state_ofHistory_frestrictLe u (stepJumps ω) hk
  exact ⟨fun h k hk => by rw [hst k hk]; exact h k hk,
    fun h k hk => by rw [← hst k hk]; exact h k hk⟩

omit [NeZero N] [NeZero M] in
/-- With every holding time positive, no time has elapsed at time `0`. -/
theorem jumpCount_zero {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) :
    jumpCount ω 0 = 0 := by
  have hset : {n : ℕ | jumpTime n ω ≤ 0} = {0} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hn
      by_contra hne
      exact absurd hn (not_le.2 (jumpTime_pos hpos (Nat.pos_of_ne_zero hne)))
    · rintro rfl
      simp
  rw [jumpCount, hset, csSup_singleton]

omit [NeZero N] [NeZero M] in
/-- **The exit time is at most the sum of the holding times spent away from `l`.**  On a
realisation with positive holding times that reaches `θ ∋ l`, the hitting time of `θ` is the
jump time `T_k` of the first matrix in `θ`, and every holding time before it is spent at a
matrix outside `θ`, so in particular different from `l`. -/
theorem hittingTimeCts_le_tsum {u l : Pressure N M} {θ : Set (Pressure N M)} (hl : l ∈ θ)
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω)
    (hhit : ∃ k, (Trajectory.ofStepPath ω).state u k ∈ θ) :
    hittingTimeCts u θ ω
      ≤ ∑' n : ℕ, Set.indicator (avoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω := by
  classical
  have hk : (Trajectory.ofStepPath ω).state u (Nat.find hhit) ∈ θ := Nat.find_spec hhit
  have hmin : ∀ j < Nat.find hhit, (Trajectory.ofStepPath ω).state u j ∉ θ :=
    fun j hj => Nat.find_min hhit hj
  rcases Nat.eq_zero_or_pos (Nat.find hhit) with hk0 | hk0
  · have h0 : hittingTimeCts u θ ω ≤ ENNReal.ofReal 0 := by
      refine sInf_le ⟨0, ⟨le_rfl, ?_⟩, rfl⟩
      rw [process, jumpCount_zero hpos]
      rwa [hk0] at hk
    rw [ENNReal.ofReal_zero] at h0
    exact h0.trans zero_le
  · calc hittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime (Nat.find hhit) ω) :=
          hittingTimeCts_le_jumpTime hpos hk0.ne' hk
      _ = ∑ n ∈ Finset.range (Nat.find hhit), ENNReal.ofReal (holdingTime n ω) :=
          ENNReal.ofReal_sum_of_nonneg fun n _ => (hpos n).le
      _ = ∑ n ∈ Finset.range (Nat.find hhit), Set.indicator (avoidUpTo u l n)
            (fun ω => ENNReal.ofReal (holdingTime n ω)) ω := by
          refine Finset.sum_congr rfl fun n hn =>
            (Set.indicator_of_mem ?_ (fun ω => ENNReal.ofReal (holdingTime n ω))).symm
          intro j hj heq
          exact hmin j (by have := Finset.mem_range.1 hn; omega) (heq ▸ hl)
      _ ≤ _ := ENNReal.sum_le_tsum _

/-- **The mean hitting time of any set containing a canonical ladder is finite**, from every
state of `S` and for every `β ≥ 0`.

**No counterpart in the paper.**  The skeleton reaches `l^o` within `2N` steps with probability
at least `c > 0` from anywhere in `S` (`SocialNetwork.minorisation_iterateKernel`), so the
number of steps it spends away from `l^o` has a geometric tail
(`SocialNetwork.tsum_kacAvoid_ne_top`); the process follows the skeleton
(`SocialNetwork.map_ctsPathMeasure_jumps`); and each step costs a holding time of mean at most
`∑_k e^{-k}` whatever the past (`SocialNetwork.ctsPathMeasure_history_holdingTime_le_mul`). -/
theorem expHittingTimeCts_lt_top (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {u : Pressure N M}
    (hu : IsState u) {θ : Set (Pressure N M)} {o : Opinion M} (hθ : ladderOf N o ∈ θ) :
    expHittingTimeCts β u θ < ∞ := by
  set l := ladderOf N o with hl
  set P := ctsPathMeasure β u with hP
  -- the skeleton spends a summable number of steps away from `l`
  have hNN : 0 < N + N := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    omega
  have hc : 0 < ENNReal.ofReal (zeta N M β) ^ N
      * ENNReal.ofReal (stepFloor N M β (greedyBound N M + (N : ℤ) * ((M : ℤ) - 1))) ^ N := by
    refine ENNReal.mul_pos (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
    · exact (ENNReal.ofReal_pos.2 (zeta_pos N M β)).ne'
    · exact (ENNReal.ofReal_pos.2 (stepFloor_pos N M β _)).ne'
  have hsum : ∑' m : ℕ, kacAvoid (skeletonKernel β) l m u ≠ ∞ :=
    tsum_kacAvoid_ne_top (skeletonKernel β) (S := stateSet N M) hNN hc
      (fun v hv => skeletonKernel_compl_stateSet β hv)
      (fun v hv => minorisation_iterateKernel hM hβ o hv) hu
  have hsum' : ∑' n : ℕ, kacAvoid (skeletonKernel β) l (n + 1) u ≠ ∞ := by
    refine ne_top_of_le_ne_top hsum ?_
    rw [tsum_eq_zero_add' (f := fun m => kacAvoid (skeletonKernel β) l m u) ENNReal.summable]
    exact le_add_self
  -- and so does the process
  have hPavoid : ∀ n, P (avoidUpTo u l n) = kacAvoid (skeletonKernel β) l (n + 1) u := by
    intro n
    rw [hP, avoidUpTo_eq_preimage, ctsPathMeasure_preimage_stepJumps β u
      (measurableSet_avoidSet u l (n + 1)), kacAvoid_skeletonKernel]
  -- almost every realisation has positive holding times and reaches `θ`
  have hpos_ae : ∀ᵐ ω ∂P, ∀ n, 0 < holdingTime n ω := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (ctsPathMeasure_holdingTime_nonpos β u n)]
      with ω hω
    simpa using hω
  have hhit_ae : ∀ᵐ ω ∂P, ∃ k, (Trajectory.ofStepPath ω).state u k ∈ θ := by
    have hnull : P (⋂ n, avoidUpTo u l n) = 0 := by
      have htend : Filter.Tendsto (fun n => kacAvoid (skeletonKernel β) l (n + 1) u)
          Filter.atTop (nhds 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum'
      refine le_antisymm (ge_of_tendsto' htend fun n => ?_) zero_le
      rw [← hPavoid n]
      exact measure_mono (Set.iInter_subset _ n)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
    by_contra hne
    exact hω (Set.mem_iInter.2 fun n k _ heq => (not_exists.1 hne) k (heq ▸ hθ))
  -- the per-step bound
  have hmeasH : ∀ n, Measurable fun ω : ℕ → Step N M => ENNReal.ofReal (holdingTime n ω) :=
    fun n => ENNReal.measurable_ofReal.comp (measurable_holdingTime n)
  have hterm : ∀ n, ∫⁻ ω, Set.indicator (avoidUpTo u l n)
        (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P
      ≤ ∑' k : ℕ, P (avoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) := by
    intro n
    have hmeasE : ∀ k : ℕ,
        MeasurableSet (avoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) :=
      fun k => (measurableSet_avoidUpTo u l n).inter
        ((measurable_holdingTime n) measurableSet_Ioi)
    calc ∫⁻ ω, Set.indicator (avoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P
        ≤ ∫⁻ ω, ∑' k : ℕ, Set.indicator
            (avoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)})
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ avoidUpTo u l n
          · rw [Set.indicator_of_mem hω]
            refine (ofReal_le_tsum_indicator_Ioi _).trans (le_of_eq (tsum_congr fun k => ?_))
            by_cases hk : holdingTime n ω ∈ Set.Ioi (k : ℝ)
            · rw [Set.indicator_of_mem hk,
                Set.indicator_of_mem (show ω ∈ avoidUpTo u l n ∩
                  {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)} from ⟨hω, hk⟩)]
            · rw [Set.indicator_of_notMem hk,
                Set.indicator_of_notMem fun h => hk h.2]
          · rw [Set.indicator_of_notMem hω]
            exact zero_le
      _ = ∑' k : ℕ, P (avoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) := by
          rw [lintegral_tsum fun k => (measurable_const.indicator (hmeasE k)).aemeasurable]
          exact tsum_congr fun k => lintegral_indicator_one (hmeasE k)
  have hterm0 : ∀ k : ℕ, P (avoidUpTo u l 0 ∩ {ω | holdingTime 0 ω ∈ Set.Ioi (k : ℝ)})
      ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
    intro k
    refine (measure_mono Set.inter_subset_right).trans ?_
    rw [hP, ctsPathMeasure_holdingTime_zero β u measurableSet_Ioi]
    exact expMeasure_totalRate_Ioi_le hM β hu k
  have htermS : ∀ m k : ℕ,
      P (avoidUpTo u l (m + 1) ∩ {ω | holdingTime (m + 1) ω ∈ Set.Ioi (k : ℝ)})
        ≤ ENNReal.ofReal (Real.exp (-(k : ℝ))) * P (avoidUpTo u l (m + 1)) := by
    intro m k
    have hmeasG : MeasurableSet {h : (i : Finset.Iic m) → Step N M |
        ∀ k ≤ m + 1, (Trajectory.ofStepHistory h).state u k ≠ l} := by
      have hpre : {h : (i : Finset.Iic m) → Step N M |
            ∀ k ≤ m + 1, (Trajectory.ofStepHistory h).state u k ≠ l}
          = (fun h : (i : Finset.Iic m) → Step N M => fun i => (h i).1) ⁻¹'
            {y | ∀ k ≤ m + 1, (Trajectory.ofHistory y).state u k ≠ l} := rfl
      rw [hpre]
      exact (measurable_stepHistoryJumps m) MeasurableSet.of_discrete
    rw [avoidUpTo_succ_eq_preimage]
    exact ctsPathMeasure_history_holdingTime_le_mul β u m hmeasG measurableSet_Ioi
      fun h _ => expMeasure_totalRate_Ioi_le hM β (Trajectory.isState_state _ hu (m + 1)) k
  -- assemble
  set D := ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) with hD
  calc expHittingTimeCts β u θ
      ≤ ∫⁻ ω, ∑' n : ℕ, Set.indicator (avoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpos_ae, hhit_ae] with ω h1 h2
        exact hittingTimeCts_le_tsum hθ h1 h2
    _ = ∑' n : ℕ, ∫⁻ ω, Set.indicator (avoidUpTo u l n)
          (fun ω => ENNReal.ofReal (holdingTime n ω)) ω ∂P :=
        lintegral_tsum fun n => ((hmeasH n).indicator (measurableSet_avoidUpTo u l n)).aemeasurable
    _ ≤ ∑' n : ℕ, ∑' k : ℕ, P (avoidUpTo u l n ∩ {ω | holdingTime n ω ∈ Set.Ioi (k : ℝ)}) :=
        ENNReal.tsum_le_tsum hterm
    _ = (∑' k : ℕ, P (avoidUpTo u l 0 ∩ {ω | holdingTime 0 ω ∈ Set.Ioi (k : ℝ)}))
          + ∑' m : ℕ, ∑' k : ℕ,
            P (avoidUpTo u l (m + 1) ∩ {ω | holdingTime (m + 1) ω ∈ Set.Ioi (k : ℝ)}) :=
        tsum_eq_zero_add' ENNReal.summable
    _ ≤ D + ∑' m : ℕ, D * kacAvoid (skeletonKernel β) l (m + 2) u := by
        gcongr with m
        · exact ENNReal.tsum_le_tsum hterm0
        · calc ∑' k : ℕ,
                P (avoidUpTo u l (m + 1) ∩ {ω | holdingTime (m + 1) ω ∈ Set.Ioi (k : ℝ)})
              ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) * P (avoidUpTo u l (m + 1)) :=
                ENNReal.tsum_le_tsum (htermS m)
            _ = D * kacAvoid (skeletonKernel β) l (m + 2) u := by
                rw [ENNReal.tsum_mul_right, hPavoid]
    _ < ∞ := by
        refine ENNReal.add_lt_top.2 ⟨tsum_ofReal_exp_neg_ne_top.lt_top, ?_⟩
        rw [ENNReal.tsum_mul_left]
        refine ENNReal.mul_lt_top tsum_ofReal_exp_neg_ne_top.lt_top ?_
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun m => ?_) hsum'.lt_top
        exact kacAvoid_antitone (skeletonKernel β) l (Nat.le_succ (m + 1)) u

/-- **The mean exit time from a consensus set is finite**, from every state of `S` and for
every `β ≥ 0`: `E (R^{β,u} (C^{-o})) < ∞`.  This is what makes the ratios of Theorem 3 and
Proposition 12 mean what they say. -/
theorem expHittingTimeCts_consensusSetOther_lt_top (hM : 2 ≤ M) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) {u : Pressure N M} (hu : IsState u) (o : Opinion M) :
    expHittingTimeCts β u (consensusSetOther N o) < ∞ := by
  obtain ⟨o', ho'⟩ : ∃ o' : Opinion M, o' ≠ o := by
    by_cases h0 : (o : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
  refine expHittingTimeCts_lt_top hM hβ hu (o := o') ?_
  exact ⟨o', ho', (isLadder_ladderOf (N := N) o').isConsensus hM hN⟩

/-- **The mean exit time from a consensus set is positive**: from `u ∈ C^o` the process sits at
`u`, which is not in `C^{-o}`, until its first jump, and the first holding time is positive. -/
theorem expHittingTimeCts_consensusSetOther_pos (β : ℝ) {o : Opinion M} {u : Pressure N M}
    (hu : IsConsensus o u) : 0 < expHittingTimeCts β u (consensusSetOther N o) := by
  set P := ctsPathMeasure β u with hP
  have hpos_ae : ∀ᵐ ω ∂P, ∀ n, 0 < holdingTime n ω := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (ctsPathMeasure_holdingTime_nonpos β u n)]
      with ω hω
    simpa using hω
  have hR : ∀ᵐ ω ∂P, 0 < hittingTimeCts u (consensusSetOther N o) ω := by
    filter_upwards [hpos_ae] with ω hω
    have h := jumpTime_lt_hittingTimeCts (u := u) (θ := consensusSetOther N o) hω (k := 0)
      fun n hn => by
        rw [Nat.le_zero.1 hn, Trajectory.state_zero]
        exact hu.notMem_consensusSetOther
    simpa using h
  rw [pos_iff_ne_zero, Ne, expHittingTimeCts,
    lintegral_eq_zero_iff (measurable_hittingTimeCts _ _)]
  intro h0
  have hfalse : ∀ᵐ _ω ∂P, False := by
    filter_upwards [hR, h0] with ω h1 h2
    rw [h2, Pi.zero_apply] at h1
    exact lt_irrefl _ h1
  have hnull := ae_iff.1 hfalse
  simp only [not_false_eq_true, Set.ofPred_true, measure_univ] at hnull
  exact one_ne_zero hnull

end ExitTime

end SocialNetwork
