/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Greedy
import SocialNetwork.Kac

/-!
# The Markov property of the skeleton, at a deterministic time

Proposition 9 of arXiv:2607.19651 lower-bounds the return time of the skeleton by running two
different estimates one after the other: a run of greedy expressions reaches `L`
(Proposition 7), and from there a run of positive expressions keeps the process in `L̂`
(Remark 5).  Composing them is the Markov property: after the first `n` expressed pairs are
prescribed, the remaining ones have the law of the chain started afresh at the matrix so
reached.

Mathlib has the Ionescu-Tulcea construction (`ProbabilityTheory.Kernel.traj`) and its
decompositions, but those relate the *same* kernel family to itself; what is needed here is
that the shifted realisation is distributed as `P^{β,v}` for the matrix `v` the chain has
reached, which is a statement about this particular family and is proved from the exact law of
a cylinder.

**No counterpart in the paper**, which uses the Markov property without comment.

This file is the transposition to the skeleton of
`SocialNetwork.Bias.pathMeasure_cylinder` and `SocialNetwork.Bias.pathMeasure_restart`, proved
first for the biased chain in `SocialNetwork/BiasedResults.lean`; the arguments are the same
and the docstrings say what each step does.

## Main definitions

* `SocialNetwork.ofHistoryPath`, `SocialNetwork.stateAfterHistory` — a finite history read as
  a realisation, and the matrix it reaches.
* `SocialNetwork.shiftPath` — dropping the first `n` expressed pairs.
* `SocialNetwork.concatPath` — following a prescribed history by an arbitrary realisation.

## Main results

* `SocialNetwork.pathMeasure_cylinder` — the exact law of a cylinder: the probability of a
  prescribed run of `n` expressed pairs is the product of the one-step probabilities along it.
* `SocialNetwork.pathMeasure_restart` — the Markov property at a deterministic time.
* `SocialNetwork.kacAvoid_skeletonKernel` — the avoidance probabilities of
  `SocialNetwork.kacAvoid`, which are defined by a recursion on the kernel, are the
  probabilities of the corresponding events on realisations.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace SocialNetwork

variable {N M : ℕ} [NeZero N] [NeZero M] {β : ℝ} {u : Pressure N M}

/-! ### A finite history, read as a realisation -/

omit [NeZero N] [NeZero M] in
/-- Read a finite history `(A₁, O₁), …, (A_{n+1}, O_{n+1})` back as a realisation, by repeating
the last pair forever.  Only the entries of index `≤ n` are ever used.  This is
`SocialNetwork.Trajectory.ofHistory` without the detour through `Trajectory`. -/
def ofHistoryPath {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) : ℕ → Jump N M :=
  fun k => h ⟨min k n, Finset.mem_Iic.2 (min_le_right k n)⟩

omit [NeZero N] [NeZero M] in
theorem ofHistoryPath_apply {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) {j : ℕ} (hj : j ≤ n) :
    ofHistoryPath h j = h ⟨j, Finset.mem_Iic.2 hj⟩ := by
  have hmin : (⟨min j n, Finset.mem_Iic.2 (min_le_right j n)⟩ : Finset.Iic n)
      = ⟨j, Finset.mem_Iic.2 hj⟩ := Subtype.ext (min_eq_left hj)
  simp only [ofHistoryPath, hmin]

omit [NeZero N] [NeZero M] in
@[simp]
theorem ofHistory_eq_ofPath {n : ℕ} (h : (i : Finset.Iic n) → Jump N M) :
    Trajectory.ofHistory h = Trajectory.ofPath (ofHistoryPath h) := rfl

/-- The matrix a finite history reaches, its last pair being repeated forever. -/
def stateAfterHistory (u : Pressure N M) {n : ℕ} (h : (i : Finset.Iic n) → Jump N M)
    (k : ℕ) : Pressure N M :=
  (Trajectory.ofHistory h).state u k

omit [NeZero N] [NeZero M] in
theorem stateAfterHistory_eq_state (u : Pressure N M) {n : ℕ}
    (h : (i : Finset.Iic n) → Jump N M) (k : ℕ) :
    stateAfterHistory u h k = (Trajectory.ofHistory h).state u k := rfl

omit [NeZero N] [NeZero M] in
theorem stateAfterHistory_eq_skeleton (u : Pressure N M) {n : ℕ}
    (h : (i : Finset.Iic n) → Jump N M) (k : ℕ) :
    stateAfterHistory u h k = skeleton u k (ofHistoryPath h) := rfl

omit [NeZero N] [NeZero M] in
/-- `Ũ_n` depends only on the first `n` expressed pairs. -/
theorem skeleton_congr (u : Pressure N M) (n : ℕ) {ω ω' : ℕ → Jump N M}
    (h : ∀ k < n, ω k = ω' k) : skeleton u n ω = skeleton u n ω' :=
  Trajectory.state_congr u n (fun k hk => by rw [Trajectory.actor_ofPath,
    Trajectory.actor_ofPath, h k hk]) fun k hk => by
      rw [Trajectory.opinion_ofPath, Trajectory.opinion_ofPath, h k hk]

omit [NeZero N] [NeZero M] in
theorem skeleton_succ (u : Pressure N M) (ω : ℕ → Jump N M) (n : ℕ) :
    skeleton u (n + 1) ω = express (ω n).1 (ω n).2 (skeleton u n ω) :=
  Trajectory.state_succ _ u n

omit [NeZero N] [NeZero M] in
/-- Truncating a realisation to its first `n + 1` entries and reading the result back as a
realisation changes no matrix up to time `n + 1`. -/
theorem skeleton_ofHistoryPath_frestrictLe (u : Pressure N M) (ω : ℕ → Jump N M) {n k : ℕ}
    (hk : k ≤ n + 1) :
    skeleton u k (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω))
      = skeleton u k ω :=
  Trajectory.state_ofHistory_frestrictLe u ω hk

omit [NeZero N] [NeZero M] in
theorem ofHistoryPath_eq {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h) {j : ℕ}
    (hj : j ≤ n) : ofHistoryPath x j = ofHistoryPath h j := by
  rw [ofHistoryPath_apply _ (show j ≤ n + 1 by omega), ofHistoryPath_apply _ hj, ← hx,
    Preorder.frestrictLe₂_apply]

omit [NeZero N] [NeZero M] in
theorem skeleton_ofHistoryPath_eq {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (u : Pressure N M) {k : ℕ} (hk : k ≤ n + 1) :
    skeleton u k (ofHistoryPath x) = skeleton u k (ofHistoryPath h) :=
  skeleton_congr u k fun j hj => ofHistoryPath_eq hx (by omega)

theorem partialTraj_compl_null (n : ℕ) (h : (i : Finset.Iic n) → Jump N M) :
    Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
        (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})ᶜ = 0 := by
  have hmapA : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (drivingKernel β u) n (n + 1) h).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      = Measure.dirac h := by
    rw [Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Jump N M) h
      (Nat.le_succ n), Kernel.partialTraj_self, Kernel.id_apply]
  have hAone : Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
      (drivingKernel β u) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h}) = 1 := by
    have hm := Measure.map_apply
      (μ := Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (drivingKernel β u) n (n + 1) h)
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
        (drivingKernel β u) n (n + 1) h).map
      (fun x : (i : Finset.Iic (n + 1)) → Jump N M => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      = (jumpPMF β (stateAfterHistory u h (n + 1))).toMeasure := by
  rw [← Kernel.map_apply _ Measurable.of_discrete, Kernel.map_partialTraj_succ_self,
    drivingKernel_apply]
  rfl

/-- The event that the `k`-th expressed pair lies in `S k` at the profile reached then, for
every `k < m`.

The set is allowed to depend on the step as well as on the profile: at a constant `S` this is
the event `⋂_{j=1}^{m} ξ_j` of Propositions 17 and 24, and at the singleton
`S k _ = {ζ k}` it is the cylinder `{ω : ω_k = ζ_k for k < m}` of Proposition 18. -/
def stepEvents (S : ℕ → Pressure N M → Finset (Jump N M)) (u : Pressure N M) (m : ℕ) :
    Set (ℕ → Jump N M) :=
  {ω | ∀ k < m, ω k ∈ S k (skeleton u k ω)}

/-- The same event, read on histories of the first `n + 1` expressed pairs. -/
def stepHistory (S : ℕ → Pressure N M → Finset (Jump N M)) (u : Pressure N M) (n : ℕ) :
    Set ((i : Finset.Iic n) → Jump N M) :=
  {h | ∀ k ≤ n, ofHistoryPath h k ∈ S k (skeleton u k (ofHistoryPath h))}

omit [NeZero N] [NeZero M] in
theorem measurableSet_stepHistory (S : ℕ → Pressure N M → Finset (Jump N M)) (u : Pressure N M)
    (n : ℕ) : MeasurableSet (stepHistory S u n) := MeasurableSet.of_discrete

omit [NeZero N] [NeZero M] in
/-- `⋂_{j=1}^{n+1}` of the event is the cylinder over `stepHistory S u n`. -/
theorem stepEvents_succ_eq_preimage (S : ℕ → Pressure N M → Finset (Jump N M))
    (u : Pressure N M) (n : ℕ) :
    stepEvents S u (n + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹' stepHistory S u n := by
  have key : ∀ (ω : ℕ → Jump N M) (k : ℕ), k ≤ n →
      (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω) k
        ∈ S k (skeleton u k
            (ofHistoryPath (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ω)))
        ↔ ω k ∈ S k (skeleton u k ω)) := by
    intro ω k hk
    rw [skeleton_ofHistoryPath_frestrictLe u ω (show k ≤ n + 1 by omega),
      ofHistoryPath_apply _ hk, Preorder.frestrictLe_apply]
  ext ω
  simp only [stepEvents, stepHistory, Set.mem_ofPred_eq, Set.mem_preimage]
  exact ⟨fun hω k hk => (key ω k hk).2 (hω k (by omega)),
    fun hω k hk => (key ω k (by omega)).1 (hω k (by omega))⟩

omit [NeZero N] [NeZero M] in
theorem measurableSet_stepEvents (S : ℕ → Pressure N M → Finset (Jump N M)) (u : Pressure N M)
    (m : ℕ) : MeasurableSet (stepEvents S u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : stepEvents S u 0 = Set.univ := by ext ω; simp [stepEvents]
    rw [h0]
    exact MeasurableSet.univ
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [stepEvents_succ_eq_preimage]
    exact Preorder.measurable_frestrictLe n (measurableSet_stepHistory S u n)

omit [NeZero N] [NeZero M] in
/-- If a history of length `n + 2` restricts to one in `stepHistory S u n` and its last
coordinate lies in `S (n + 1)` at the profile that history reaches, then it is in
`stepHistory S u (n + 1)`. -/
theorem mem_stepHistory_succ {S : ℕ → Pressure N M → Finset (Jump N M)} {n : ℕ}
    {x : (i : Finset.Iic (n + 1)) → Jump N M} {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (hh : h ∈ stepHistory S u n)
    (hlast : x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ ∈ S (n + 1) (stateAfterHistory u h (n + 1))) :
    x ∈ stepHistory S u (n + 1) := by
  intro k hk
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · have hkn : k ≤ n := by omega
    rw [skeleton_ofHistoryPath_eq hx u (k := k) (by omega), ofHistoryPath_eq hx hkn]
    exact hh k hkn
  · have hkeq : k = n + 1 := le_antisymm hk hge
    subst hkeq
    rw [skeleton_ofHistoryPath_eq hx u (k := n + 1) le_rfl,
      ofHistoryPath_apply _ (le_refl (n + 1))]
    exact hlast

/-- **The induction step**, for whatever one-step bound holds at the profile this history
reaches. -/
theorem le_partialTraj_succ {S : ℕ → Pressure N M → Finset (Jump N M)} {c : ℝ≥0∞}
    (n : ℕ) {h : (i : Finset.Iic n) → Jump N M} (hh : h ∈ stepHistory S u n)
    (hone : c ≤ (jumpPMF β (stateAfterHistory u h (n + 1))).toMeasure
      (S (n + 1) (stateAfterHistory u h (n + 1)))) :
    c ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
          (stepHistory S u (n + 1)) := by
  have hB : c
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
          (drivingKernel β u) n (n + 1) h
          ((fun x : (i : Finset.Iic (n + 1)) → Jump N M =>
              x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            (S (n + 1) (stateAfterHistory u h (n + 1)))) := by
    rw [← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      partialTraj_map_last]
    exact hone
  exact le_measure_of_inter (partialTraj_compl_null n h) hB
    fun x hx => mem_stepHistory_succ hx.1 hh hx.2


theorem le_historyMeasure_zero {S : ℕ → Pressure N M → Finset (Jump N M)} {c : ℝ≥0∞}
    (hone : c ≤ (jumpPMF β u).toMeasure (S 0 u)) :
    c ≤ historyMeasure β u 0 (stepHistory S u 0) := by
  have hpre : toHistoryZero ⁻¹' stepHistory S u 0 = (S 0 u : Set (Jump N M)) := by
    ext z
    have hz : ofHistoryPath (toHistoryZero z) 0 = z := rfl
    constructor
    · intro hzz
      have h0 := hzz 0 le_rfl
      rwa [hz, skeleton_zero] at h0
    · intro hzz k hk
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      rw [hz, skeleton_zero]
      exact hzz
  unfold historyMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply measurable_toHistoryZero MeasurableSet.of_discrete, hpre]
  exact hone

/-- The one-step bound, in the form the induction consumes: it may depend on the step and on
the whole past, as long as the past is admissible. -/
def IsStepBound (β : ℝ) (S : ℕ → Pressure N M → Finset (Jump N M)) (u : Pressure N M)
    (c : ℕ → ℝ≥0∞) : Prop :=
  ∀ (m : ℕ) (ω : ℕ → Jump N M), (∀ k < m, ω k ∈ S k (skeleton u k ω)) →
    c m ≤ (jumpPMF β (skeleton u m ω)).toMeasure (S m (skeleton u m ω))

theorem prod_le_historyMeasure {S : ℕ → Pressure N M → Finset (Jump N M)} {c : ℕ → ℝ≥0∞}
    (hone : IsStepBound β S u c) (n : ℕ) :
    ∏ m ∈ Finset.range (n + 1), c m ≤ historyMeasure β u n (stepHistory S u n) := by
  induction n with
  | zero =>
      have h0 := hone 0 (fun _ => default) (by omega)
      rw [skeleton_zero] at h0
      simpa using le_historyMeasure_zero h0
  | succ n ih =>
      have hstep : historyMeasure β u (n + 1) (stepHistory S u (n + 1))
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (drivingKernel β u) n (n + 1) h
              (stepHistory S u (n + 1)) ∂(historyMeasure β u n) := by
        unfold historyMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_stepHistory S u (n + 1)) (Kernel.aemeasurable _)]
      rw [hstep]
      calc ∏ m ∈ Finset.range (n + 1 + 1), c m
          = c (n + 1) * ∏ m ∈ Finset.range (n + 1), c m := by
            rw [Finset.prod_range_succ]; ring
        _ ≤ c (n + 1) * historyMeasure β u n (stepHistory S u n) := by gcongr
        _ = ∫⁻ h, (stepHistory S u n).indicator (fun _ => c (n + 1)) h
              ∂(historyMeasure β u n) := by
            rw [lintegral_indicator (measurableSet_stepHistory S u n), setLIntegral_const]
        _ ≤ ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (drivingKernel β u) n (n + 1) h
              (stepHistory S u (n + 1)) ∂(historyMeasure β u n) := by
            refine lintegral_mono fun h => ?_
            by_cases hh : h ∈ stepHistory S u n
            · rw [Set.indicator_of_mem hh]
              exact le_partialTraj_succ n hh
                (hone (n + 1) (ofHistoryPath h) fun k hk => hh k (by omega))
            · rw [Set.indicator_of_notMem hh]
              exact zero_le

/-- **The iteration of Proposition 8**, for any one-step bound and any prescribed set of
pairs at each time.

The paper does it by conditioning on `Ũ_{m-1} = v` in eq. (10); here it goes along the
finite-horizon kernels of the Ionescu–Tulcea construction, Mathlib offering no decomposition
of that shape.  It is the same Markov property through the formalism that exists. -/
theorem prod_le_pathMeasure_stepEvents {S : ℕ → Pressure N M → Finset (Jump N M)}
    {c : ℕ → ℝ≥0∞} (hone : IsStepBound β S u c) (m : ℕ) :
    ∏ j ∈ Finset.range m, c j ≤ pathMeasure β u (stepEvents S u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have huniv : stepEvents S u 0 = Set.univ := by
      ext ω
      simp [stepEvents]
    rw [Finset.range_zero, Finset.prod_empty, huniv, measure_univ]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hmap : (pathMeasure β u).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n)
        = historyMeasure β u n := by
      unfold historyMeasure pathMeasure
      rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
        Kernel.traj_map_frestrictLe]
    rw [stepEvents_succ_eq_preimage, ← Measure.map_apply
      (Preorder.measurable_frestrictLe n) (measurableSet_stepHistory S u n), hmap]
    exact prod_le_historyMeasure hone n

/-- The iteration at a bound that does not depend on the step: Propositions 17 and 24. -/
theorem pow_le_pathMeasure_stepEvents {S : Pressure N M → Finset (Jump N M)} {c : ℝ}
    (hone : ∀ P : Pressure N M, ENNReal.ofReal c ≤ (jumpPMF β P).toMeasure (S P))
    (m : ℕ) :
    ENNReal.ofReal c ^ m ≤ pathMeasure β u (stepEvents (fun _ => S) u m) := by
  have := prod_le_pathMeasure_stepEvents (u := u) (S := fun _ => S)
    (c := fun _ => ENNReal.ofReal c) (fun k ω _ => hone _) m
  simpa using this

/-! #### The exact law of a cylinder

The bound above is in fact an equality, and Proposition 18 needed only the inequality.  The
equality is what the Markov property of Theorem 4 rests on, so it is proved here, by the same
induction with the one-step kernel evaluated at a singleton. -/

/-- The one-step kernel of the Ionescu-Tulcea construction, at a singleton: it is the jump
probability of the last coordinate, and zero unless the history is the one it was given. -/
theorem partialTraj_singleton (n : ℕ) (h : (i : Finset.Iic n) → Jump N M)
    (x : (i : Finset.Iic (n + 1)) → Jump N M) :
    Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h {x}
      = if Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h then
          jumpPMF β (stateAfterHistory u h (n + 1)) (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
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
        (drivingKernel β u) n (n + 1) h
        ((Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})
          ∩ ((fun y : (i : Finset.Iic (n + 1)) → Jump N M =>
              y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            {x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩}))
        = Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
            (drivingKernel β u) n (n + 1) h
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
    historyMeasure β u n {x}
      = ∏ m ∈ Finset.range (n + 1),
          jumpPMF β (stateAfterHistory u x m) (ofHistoryPath x m) := by
  induction n with
  | zero =>
      have h0 : historyMeasure β u 0
          = (jumpPMF β u).toMeasure.map toHistoryZero := by
        unfold historyMeasure
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
      have hstep : historyMeasure β u (n + 1) {x}
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (drivingKernel β u) n (n + 1) h {x}
              ∂(historyMeasure β u n) := by
        unfold historyMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _)]
      set h₀ := Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x with hh₀
      have hind : (fun h : (i : Finset.Iic n) → Jump N M =>
            Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
              (drivingKernel β u) n (n + 1) h {x})
          = Set.indicator {h₀} (fun _ =>
              jumpPMF β (stateAfterHistory u h₀ (n + 1))
                (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)) := by
        funext h
        rw [partialTraj_singleton n h x]
        by_cases hc : h = h₀
        · rw [if_pos hc.symm, Set.indicator_of_mem (Set.mem_singleton_iff.2 hc), hc]
        · rw [if_neg fun hh => hc hh.symm, Set.indicator_of_notMem (by simpa using hc)]
      have hlhs : historyMeasure β u (n + 1) {x}
          = jumpPMF β (stateAfterHistory u h₀ (n + 1))
              (x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
            * ∏ m ∈ Finset.range (n + 1),
                jumpPMF β (stateAfterHistory u h₀ m) (ofHistoryPath h₀ m) := by
        rw [hstep, hind, lintegral_indicator (measurableSet_singleton h₀), setLIntegral_const,
          ih h₀]
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

/-- **The law of a cylinder**: the probability of following a prescribed sequence of expressed
pairs for `n` steps is exactly the product of the one-step probabilities along it. -/
theorem pathMeasure_cylinder (ζ : ℕ → Jump N M) (n : ℕ) :
    pathMeasure β u {ω | ∀ k < n, ω k = ζ k}
      = ∏ m ∈ Finset.range n, jumpPMF β (skeleton u m ζ) (ζ m) := by
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
    have hmap : (pathMeasure β u).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) b)
        = historyMeasure β u b := by
      unfold historyMeasure pathMeasure
      rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe b),
        Kernel.traj_map_frestrictLe]
    rw [hset, ← Measure.map_apply (Preorder.measurable_frestrictLe b)
      (measurableSet_singleton _), hmap, historyMeasure_singleton]
    refine Finset.prod_congr rfl fun m hm => ?_
    have hmb : m ≤ b := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have hpath : ∀ j ≤ b, ofHistoryPath (fun i : Finset.Iic b => ζ (i : ℕ)) j = ζ j :=
      fun j hj => by rw [ofHistoryPath_apply _ hj]
    have hstate : stateAfterHistory u (fun i : Finset.Iic b => ζ (i : ℕ)) m = skeleton u m ζ :=
      skeleton_congr u m fun j hj => hpath j (by omega)
    rw [hstate, hpath m hmb]


section Markov


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
theorem skeleton_add (u : Pressure N M) (ω : ℕ → Jump N M) (n i : ℕ) :
    skeleton u (n + i) ω = skeleton (skeleton u n ω) i (shiftPath n ω) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [show n + (i + 1) = n + i + 1 by ring, skeleton_succ, ih, skeleton_succ]
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
theorem skeleton_concatPath (u : Pressure N M) (n : ℕ) (ζ w : ℕ → Jump N M) :
    skeleton u n (concatPath n ζ w) = skeleton u n ζ :=
  skeleton_congr u n fun _ hj => concatPath_of_lt ζ w hj

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
theorem pathMeasure_cylinder_restart (u : Pressure N M) (ζ w : ℕ → Jump N M) (n c : ℕ) :
    pathMeasure β u ({ω | ∀ k < n, ω k = ζ k} ∩
        shiftPath n ⁻¹' {ω | ∀ k < c, ω k = w k})
      = pathMeasure β u {ω | ∀ k < n, ω k = ζ k}
        * pathMeasure β (skeleton u n ζ) {ω | ∀ k < c, ω k = w k} := by
  rw [cylinder_inter_shift, pathMeasure_cylinder, pathMeasure_cylinder, pathMeasure_cylinder,
    Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl fun m hm => ?_
    have hmn : m < n := Finset.mem_range.1 hm
    rw [skeleton_congr u m fun _ hj => concatPath_of_lt ζ w (by omega),
      concatPath_of_lt ζ w hmn]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [skeleton_add, shiftPath_concatPath, skeleton_concatPath, concatPath_add]

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
theorem pathMeasure_restart (u : Pressure N M) (ζ : ℕ → Jump N M) (n : ℕ)
    {E : Set (ℕ → Jump N M)} (hE : MeasurableSet E) :
    pathMeasure β u ({ω | ∀ k < n, ω k = ζ k} ∩ shiftPath n ⁻¹' E)
      = pathMeasure β u {ω | ∀ k < n, ω k = ζ k}
        * pathMeasure β (skeleton u n ζ) E := by
  classical
  set A : Set (ℕ → Jump N M) := {ω | ∀ k < n, ω k = ζ k} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_cylinderPath ζ n
  set μ₁ : Measure (ℕ → Jump N M) :=
    ((pathMeasure β u).restrict A).map (shiftPath n) with hμ₁def
  set μ₂ : Measure (ℕ → Jump N M) :=
    (pathMeasure β u A) • pathMeasure β (skeleton u n ζ) with hμ₂def
  have hμ₁apply : ∀ F : Set (ℕ → Jump N M), MeasurableSet F →
      μ₁ F = pathMeasure β u (A ∩ shiftPath n ⁻¹' F) := by
    intro F hF
    rw [hμ₁def, Measure.map_apply (measurable_shiftPath n) hF,
      Measure.restrict_apply (measurable_shiftPath n hF), Set.inter_comm]
  have hμ₂apply : ∀ F : Set (ℕ → Jump N M),
      μ₂ F = pathMeasure β u A * pathMeasure β (skeleton u n ζ) F := by
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

/-! ### The avoidance probabilities of Kac's lemma, read on realisations

`SocialNetwork.kacAvoid` is defined by a recursion on the transition kernel, because that is
all Kac's inequality needs.  Proposition 9 bounds it below by Proposition 7 and Remark 5,
which are statements about realisations, so the two have to be identified.  That
identification is one application of the Markov property at time `1`, iterated. -/

section Avoid

/-- The event that the skeleton started at `v` misses the matrix `u` at each of the times
`0, 1, …, m-1`.  At `k = 0` this is the condition `v ≠ u`. -/
def avoidSet (v u : Pressure N M) (m : ℕ) : Set (ℕ → Jump N M) :=
  {ω | ∀ k < m, skeleton v k ω ≠ u}

omit [NeZero N] [NeZero M] in
theorem measurableSet_avoidSet (v u : Pressure N M) (m : ℕ) :
    MeasurableSet (avoidSet v u m) := by
  have h : avoidSet v u m = ⋂ k ∈ (Finset.range m : Finset ℕ), (skeleton v k) ⁻¹' {u}ᶜ := by
    ext ω
    simp [avoidSet]
  rw [h]
  exact MeasurableSet.biInter (Finset.range m).countable_toSet fun k _ =>
    (measurable_skeleton v k) MeasurableSet.of_discrete

/-- One step of the skeleton kernel, written as a sum over the pair that is expressed. -/
theorem lintegral_skeletonKernel (β : ℝ) (v : Pressure N M) (f : Pressure N M → ℝ≥0∞) :
    ∫⁻ w, f w ∂(skeletonKernel β v)
      = ∑ z : Jump N M, jumpPMF β v z * f (express z.1 z.2 v) := by
  rw [skeletonKernel_apply, ← PMF.toMeasure_map _ _ Measurable.of_discrete,
    lintegral_map Measurable.of_discrete Measurable.of_discrete, lintegral_fintype]
  exact Finset.sum_congr rfl fun z _ => by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z), mul_comm]

/-- **The first expressed pair decomposes the event.**  Avoiding `u` at each of the times
`1, …, m` is, conditionally on the first expressed pair, avoiding `u` at each of the times
`0, …, m-1` from the matrix that pair reaches.  This is the Markov property at time `1`. -/
theorem lintegral_pathMeasure_avoidSet (β : ℝ) (v u : Pressure N M) (m : ℕ) :
    ∫⁻ w, pathMeasure β w (avoidSet w u m) ∂(skeletonKernel β v)
      = pathMeasure β v {ω : ℕ → Jump N M | ∀ k < m, skeleton v (k + 1) ω ≠ u} := by
  rw [lintegral_skeletonKernel]
  have hunion : {ω : ℕ → Jump N M | ∀ k < m, skeleton v (k + 1) ω ≠ u}
      = ⋃ z ∈ (Finset.univ : Finset (Jump N M)),
          ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
            ∩ shiftPath 1 ⁻¹' avoidSet (express z.1 z.2 v) u m) := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, Set.mem_inter_iff,
      Set.mem_preimage, avoidSet, Set.mem_ofPred_eq]
    constructor
    · intro hω
      refine ⟨ω 0, fun k hk => by rw [Nat.lt_one_iff.1 hk], fun j hj => ?_⟩
      have hk := hω j hj
      rwa [show j + 1 = 1 + j by omega, skeleton_add, skeleton_succ, skeleton_zero] at hk
    · rintro ⟨z, hz0, hz1⟩ k hk
      rw [show k + 1 = 1 + k by omega, skeleton_add, skeleton_succ, skeleton_zero,
        hz0 0 (by omega)]
      exact hz1 k hk
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Jump N M)))
      fun z : Jump N M => ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
        ∩ shiftPath 1 ⁻¹' avoidSet (express z.1 z.2 v) u m) := by
    intro z _ z' _ hne
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    rw [← hω.1 0 (by omega), ← hω'.1 0 (by omega)]
  have hmeas : ∀ z ∈ (Finset.univ : Finset (Jump N M)),
      MeasurableSet ({ω : ℕ → Jump N M | ∀ k < 1, ω k = z}
        ∩ shiftPath 1 ⁻¹' avoidSet (express z.1 z.2 v) u m) := fun z _ =>
    (measurableSet_cylinderPath (fun _ => z) 1).inter
      (measurable_shiftPath 1 (measurableSet_avoidSet _ _ _))
  rw [hunion, measure_biUnion_finset hdisj hmeas]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hstep := pathMeasure_restart (β := β) v (fun _ => z) 1
    (measurableSet_avoidSet (express z.1 z.2 v) u m)
  have hone : skeleton v 1 (fun _ => z) = express z.1 z.2 v := by
    rw [skeleton_succ, skeleton_zero]
  have hcyl : pathMeasure β v {ω : ℕ → Jump N M | ∀ k < 1, ω k = z} = jumpPMF β v z := by
    have := pathMeasure_cylinder (u := v) (β := β) (fun _ => z) 1
    simpa using this
  rw [hstep, hone, hcyl]

/-- **The bridge.**  The avoidance probability that Kac's inequality is stated with is the
probability, under `P^{β,v}`, that the skeleton misses `u` throughout the first `m` times. -/
theorem kacAvoid_skeletonKernel (β : ℝ) (u : Pressure N M) :
    ∀ (m : ℕ) (v : Pressure N M),
      kacAvoid (skeletonKernel β) u m v = pathMeasure β v (avoidSet v u m) := by
  intro m
  induction m with
  | zero =>
      intro v
      have huniv : avoidSet v u 0 = Set.univ := by
        ext ω
        simp [avoidSet]
      rw [huniv, kacAvoid_zero, measure_univ]
  | succ m ih =>
      intro v
      by_cases hv : v = u
      · subst hv
        have hempty : avoidSet v v (m + 1) = ∅ := by
          ext ω
          simp only [avoidSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
          exact ⟨0, by omega, by simp⟩
        rw [hempty, measure_empty, kacAvoid_succ, Set.indicator_of_notMem (by simp)]
      · rw [kacAvoid_succ_of_ne _ hv, lintegral_congr fun w => ih w,
          lintegral_pathMeasure_avoidSet]
        congr 1
        ext ω
        simp only [avoidSet, Set.mem_ofPred_eq]
        constructor
        · intro h k hk
          rcases Nat.eq_zero_or_pos k with rfl | hk0
          · simpa using hv
          · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
            exact h j (by omega)
        · intro h k hk
          exact h (k + 1) (by omega)

/-- The quantity Kac's inequality sums, read on realisations: the probability that the
skeleton started at `u` does not come back to `u` within `m` steps. -/
theorem lintegral_kacAvoid_skeletonKernel (β : ℝ) (u : Pressure N M) (m : ℕ) :
    ∫⁻ w, kacAvoid (skeletonKernel β) u m w ∂(skeletonKernel β u)
      = pathMeasure β u {ω : ℕ → Jump N M | ∀ k < m, skeleton u (k + 1) ω ≠ u} := by
  rw [lintegral_congr fun w => kacAvoid_skeletonKernel β u m w,
    lintegral_pathMeasure_avoidSet]

end Avoid

end Markov

end SocialNetwork
