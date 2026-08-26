/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Skeleton

/-!
# Proposition 8

Proposition 8 of arXiv:2607.19651 bounds below the probability that the first `m` expressions
are all greedy:

```
P (⋂_{j=1}^{m} ξⱼ^u) ≥ (ζ_β)^m,        ζ_β = e^{β/(M-1)} / (e^{β/(M-1)} + M N).
```

The one-step bound `P (ξ₁^v) ≥ ζ_β`, uniform in the matrix `v`, is
`SocialNetwork.zeta_le_jumpPMF_argmaxFinset`, proved in `SocialNetwork.Skeleton` from the gap
estimate.  This file iterates it, which is the paper's conditioning on `U_{T_{m-1}}^{β,u} = v`.

## How the iteration goes

The iteration is an induction along the finite-horizon kernels
`ProbabilityTheory.Kernel.partialTraj` of the Ionescu-Tulcea construction.  Write `G n` for the
greedy event read on histories of the first `n + 1` expressed pairs.  The step needs, for a
history `h ∈ G n`,

```
partialTraj κ n (n+1) h (G (n+1)) ≥ ζ_β,
```

and this comes from two marginals of `partialTraj κ n (n + 1) h`, without ever unfolding its
construction:

* `partialTraj_map_frestrictLe₂_apply` says the first `n + 1` coordinates are almost surely
  `h` itself, so the event "the past is `h`" has probability one;
* `map_partialTraj_succ_self` says the last coordinate has law `κ n h`, the Gibbs law of
  equation (3) at the matrix `Ũ_{n+1}` that replaying `h` reaches.

On the intersection of those two events a history lies in `G (n+1)` exactly when its last
coordinate maximises the pressure, and the one-step bound applies there.

## Main results

* `SocialNetwork.zeta_le_partialTraj_succ` — the induction step.
* `SocialNetwork.zeta_pow_le_pathMeasure_greedyEvents` — **Proposition 8**.
* `SocialNetwork.one_sub_le_pathMeasure_greedyEvents` — Proposition 8 together with Remark 4,
  in the linear form `P (⋂_{j≤m} ξⱼ^u) ≥ 1 - m M N e^{-β/(M-1)}` that Theorem 2 uses.
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The greedy event on finite histories -/

/-- The event `⋂_{j=1}^{n+1} ξⱼ^u`, read on histories of the first `n + 1` expressed pairs. -/
def greedyHistory (u : Pressure N M) (n : ℕ) : Set ((i : Finset.Iic n) → Jump N M) :=
  {h | ∀ k ≤ n, IsGreedyAt (Trajectory.ofHistory h) u k}

theorem measurableSet_greedyHistory (u : Pressure N M) (n : ℕ) :
    MeasurableSet (greedyHistory u n) := MeasurableSet.of_discrete

/-- `⋂_{j=1}^{n+1} ξⱼ^u` is the cylinder over `greedyHistory u n`. -/
theorem greedyEvents_eq_preimage (u : Pressure N M) (n : ℕ) :
    greedyEvents u (n + 1)
      = Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n ⁻¹' greedyHistory u n := by
  ext ω
  constructor
  · exact fun hω k hk => (isGreedyAt_ofHistory_frestrictLe u ω hk).2 (hω k (by omega))
  · exact fun hω k hk =>
      (isGreedyAt_ofHistory_frestrictLe u ω (show k ≤ n by omega)).1 (hω k (by omega))

/-- If an event has full measure, intersecting with it changes nothing. -/
theorem measure_inter_of_compl_null {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {A B : Set α} (hA : μ Aᶜ = 0) : μ (A ∩ B) = μ B := by
  refine le_antisymm (measure_mono Set.inter_subset_right) ?_
  have hsub : B ⊆ (A ∩ B) ∪ Aᶜ := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl ⟨hyA, hy⟩
    · exact Or.inr hyA
  calc μ B ≤ μ ((A ∩ B) ∪ Aᶜ) := measure_mono hsub
    _ ≤ μ (A ∩ B) + μ Aᶜ := measure_union_le _ _
    _ = μ (A ∩ B) := by rw [hA, add_zero]

/-- A lower bound transported from an event of full measure. -/
theorem le_measure_of_inter {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {A B C : Set α} {c : ℝ≥0∞} (hA : μ Aᶜ = 0) (hB : c ≤ μ B) (hsub : A ∩ B ⊆ C) :
    c ≤ μ C :=
  hB.trans ((measure_inter_of_compl_null hA).symm.le.trans (measure_mono hsub))

/-! ### Histories that agree below the last coordinate -/

section Agree

variable {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M} {h : (i : Finset.Iic n) → Jump N M}

theorem ofHistory_actor_eq
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h) {j : ℕ}
    (hj : j ≤ n) : (Trajectory.ofHistory x).actor j = (Trajectory.ofHistory h).actor j := by
  rw [Trajectory.ofHistory_actor _ (show j ≤ n + 1 by omega),
    Trajectory.ofHistory_actor _ hj, ← hx, Preorder.frestrictLe₂_apply]

theorem ofHistory_opinion_eq
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h) {j : ℕ}
    (hj : j ≤ n) : (Trajectory.ofHistory x).opinion j = (Trajectory.ofHistory h).opinion j := by
  rw [Trajectory.ofHistory_opinion _ (show j ≤ n + 1 by omega),
    Trajectory.ofHistory_opinion _ hj, ← hx, Preorder.frestrictLe₂_apply]

theorem ofHistory_state_eq
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (u : Pressure N M) {k : ℕ} (hk : k ≤ n + 1) :
    (Trajectory.ofHistory x).state u k = (Trajectory.ofHistory h).state u k :=
  Trajectory.state_congr u k (fun j hj => ofHistory_actor_eq hx (by omega))
    (fun j hj => ofHistory_opinion_eq hx (by omega))

end Agree

variable [NeZero N] [NeZero M] {β : ℝ} {u : Pressure N M}

/-- If a history of length `n + 2` restricts to a greedy history `h` and its last coordinate
maximises the pressure at the matrix that replaying `h` reaches, then it is greedy. -/
theorem mem_greedyHistory_succ {n : ℕ} {x : (i : Finset.Iic (n + 1)) → Jump N M}
    {h : (i : Finset.Iic n) → Jump N M}
    (hx : Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) x = h)
    (hh : h ∈ greedyHistory u n)
    (hlast : x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩
      ∈ argmaxFinset ((Trajectory.ofHistory h).state u (n + 1))) :
    x ∈ greedyHistory u (n + 1) := by
  intro k hk
  rcases Nat.lt_or_ge k (n + 1) with hlt | hge
  · have hkn : k ≤ n := by omega
    have hprev := hh k hkn
    rw [isGreedyAt_iff_entrySup] at hprev ⊢
    rw [ofHistory_state_eq hx u (k := k) (by omega), ofHistory_actor_eq hx hkn,
      ofHistory_opinion_eq hx hkn]
    exact hprev
  · have hkeq : k = n + 1 := le_antisymm hk hge
    subst hkeq
    rw [isGreedyAt_iff_entrySup, ofHistory_state_eq hx u (k := n + 1) le_rfl,
      Trajectory.ofHistory_actor _ (le_refl (n + 1)),
      Trajectory.ofHistory_opinion _ (le_refl (n + 1))]
    exact mem_argmaxFinset.1 hlast

/-! ### The induction step -/

/-- **The induction step of Proposition 8.**  Given a greedy history of the first `n + 1`
expressions, the next expression is greedy too with probability at least `ζ_β`. -/
theorem zeta_le_partialTraj_succ (hM : 2 ≤ M) (hβ : 0 ≤ β) (n : ℕ)
    {h : (i : Finset.Iic n) → Jump N M} (hh : h ∈ greedyHistory u n) :
    ENNReal.ofReal (zeta N M β)
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
          (greedyHistory u (n + 1)) := by
  -- the past is almost surely `h`
  have hmapA : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (drivingKernel β u) n (n + 1) h).map
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      = Measure.dirac h := by
    rw [Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ : ℕ => Jump N M) h
      (Nat.le_succ n), Kernel.partialTraj_self, Kernel.id_apply]
  have hAone : Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h}) = 1 := by
    have hm := Measure.map_apply
      (μ := Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h)
      (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Jump N M) (Nat.le_succ n))
      (measurableSet_singleton h)
    rw [hmapA] at hm
    rw [← hm]
    exact Measure.dirac_apply_of_mem rfl
  have hAcompl : Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => Jump N M) (Nat.le_succ n) ⁻¹' {h})ᶜ = 0 :=
    (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hAone
  -- the last coordinate follows the Gibbs law of equation (3) at the matrix `h` reaches
  have hmapB : (Kernel.partialTraj (X := fun _ : ℕ => Jump N M)
        (drivingKernel β u) n (n + 1) h).map
      (fun x : (i : Finset.Iic (n + 1)) → Jump N M => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      = drivingKernel β u n h := by
    rw [← Kernel.map_apply _ Measurable.of_discrete, Kernel.map_partialTraj_succ_self]
  have hB : ENNReal.ofReal (zeta N M β)
      ≤ Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
          ((fun x : (i : Finset.Iic (n + 1)) → Jump N M =>
              x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) ⁻¹'
            (argmaxFinset ((Trajectory.ofHistory h).state u (n + 1)))) := by
    rw [← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete, hmapB,
      drivingKernel_apply]
    exact zeta_le_jumpPMF_argmaxFinset hM hβ _
  exact le_measure_of_inter hAcompl hB fun x hx => mem_greedyHistory_succ hx.1 hh hx.2

/-! ### Proposition 8 -/

/-- The law of the first `n + 1` expressed pairs. -/
noncomputable def historyMeasure (β : ℝ) (u : Pressure N M) (n : ℕ) :
    Measure ((i : Finset.Iic n) → Jump N M) :=
  Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) 0 n ∘ₘ
    ((jumpPMF β u).toMeasure.map toHistoryZero)

theorem zeta_le_historyMeasure_zero (hM : 2 ≤ M) (hβ : 0 ≤ β) :
    ENNReal.ofReal (zeta N M β) ≤ historyMeasure β u 0 (greedyHistory u 0) := by
  have hpre : toHistoryZero ⁻¹' greedyHistory u 0 = (argmaxFinset u : Set (Jump N M)) := by
    ext z
    have hact : (Trajectory.ofHistory (toHistoryZero z)).actor 0 = z.1 :=
      Trajectory.ofHistory_actor _ (le_refl 0)
    have hopi : (Trajectory.ofHistory (toHistoryZero z)).opinion 0 = z.2 :=
      Trajectory.ofHistory_opinion _ (le_refl 0)
    constructor
    · intro hz
      have h0 := (isGreedyAt_iff_entrySup (Trajectory.ofHistory (toHistoryZero z)) u 0).1
        (hz 0 le_rfl)
      rw [Trajectory.state_zero, hact, hopi] at h0
      exact mem_argmaxFinset.2 h0
    · intro hz k hk
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      rw [isGreedyAt_iff_entrySup, Trajectory.state_zero, hact, hopi]
      exact mem_argmaxFinset.1 hz
  unfold historyMeasure
  rw [Kernel.partialTraj_self, Measure.id_comp,
    Measure.map_apply measurable_toHistoryZero MeasurableSet.of_discrete, hpre]
  exact zeta_le_jumpPMF_argmaxFinset hM hβ u

theorem zeta_pow_le_historyMeasure (hM : 2 ≤ M) (hβ : 0 ≤ β) (n : ℕ) :
    ENNReal.ofReal (zeta N M β) ^ (n + 1) ≤ historyMeasure β u n (greedyHistory u n) := by
  induction n with
  | zero => simpa using zeta_le_historyMeasure_zero hM hβ
  | succ n ih =>
      have hstep : historyMeasure β u (n + 1) (greedyHistory u (n + 1))
          = ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
              (greedyHistory u (n + 1)) ∂(historyMeasure β u n) := by
        unfold historyMeasure
        rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
          Measure.bind_apply (measurableSet_greedyHistory u (n + 1)) (Kernel.aemeasurable _)]
      rw [hstep]
      calc ENNReal.ofReal (zeta N M β) ^ (n + 1 + 1)
          = ENNReal.ofReal (zeta N M β) * ENNReal.ofReal (zeta N M β) ^ (n + 1) := by ring
        _ ≤ ENNReal.ofReal (zeta N M β) * historyMeasure β u n (greedyHistory u n) :=
            by gcongr
        _ = ∫⁻ h, (greedyHistory u n).indicator
              (fun _ => ENNReal.ofReal (zeta N M β)) h ∂(historyMeasure β u n) := by
            rw [lintegral_indicator (measurableSet_greedyHistory u n), setLIntegral_const]
        _ ≤ ∫⁻ h, Kernel.partialTraj (X := fun _ : ℕ => Jump N M) (drivingKernel β u) n (n + 1) h
              (greedyHistory u (n + 1)) ∂(historyMeasure β u n) := by
            refine lintegral_mono fun h => ?_
            by_cases hh : h ∈ greedyHistory u n
            · rw [Set.indicator_of_mem hh]
              exact zeta_le_partialTraj_succ hM hβ n hh
            · rw [Set.indicator_of_notMem hh]
              exact zero_le

/-- **Proposition 8.**  For every `m` and every starting matrix `u`,

```
P (⋂_{j=1}^{m} ξⱼ^u) ≥ (ζ_β)^m.
```

The proof is the paper's: the one-step bound `P (ξ₁^v) ≥ ζ_β` holds uniformly in the current
matrix `v`, and one conditions on the first `m - 1` expressions.

**Follows the paper's proof of Proposition 8** for the bound itself.  Two departures, both
forced: the paper's separate treatment of `v = 0` is unnecessary here, the bound holding
uniformly; and the iteration over `m`, which the paper does by conditioning on
`Ũ_{m-1} = v` in eq. (10), goes through the finite-horizon kernels of the Ionescu–Tulcea
construction, Mathlib offering no decomposition of that shape.  It is the same Markov
property, taken through the formalism that exists. -/
theorem zeta_pow_le_pathMeasure_greedyEvents (hM : 2 ≤ M) (hβ : 0 ≤ β) (m : ℕ) :
    ENNReal.ofReal (zeta N M β) ^ m ≤ pathMeasure β u (greedyEvents u m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have huniv : greedyEvents u 0 = Set.univ := by
      ext ω
      simp [greedyEvents]
    rw [pow_zero, huniv, measure_univ]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hmap : (pathMeasure β u).map
        (Preorder.frestrictLe (π := fun _ : ℕ => Jump N M) n) = historyMeasure β u n := by
      unfold historyMeasure
      rw [pathMeasure_def, Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
        Kernel.traj_map_frestrictLe]
    rw [greedyEvents_eq_preimage, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
      (measurableSet_greedyHistory u n), hmap]
    exact zeta_pow_le_historyMeasure hM hβ n

/-- **Proposition 8 and Remark 4 together**, in the linear form used by Theorem 2:

```
P (⋂_{j=1}^{m} ξⱼ^u) ≥ 1 - m M N e^{-β/(M-1)}.
```
-/
theorem one_sub_le_pathMeasure_greedyEvents (hM : 2 ≤ M) (hβ : 0 ≤ β) (m : ℕ) :
    ENNReal.ofReal
        (1 - (m : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1)))))
      ≤ pathMeasure β u (greedyEvents u m) := by
  refine le_trans ?_ (zeta_pow_le_pathMeasure_greedyEvents hM hβ m)
  rw [← ENNReal.ofReal_pow (zeta_pos N M β).le]
  exact ENNReal.ofReal_le_ofReal (one_sub_le_zeta_pow N M β m)

end SocialNetwork
