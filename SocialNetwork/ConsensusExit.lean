/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Transfer

/-!
# Lemma 14: leaving a consensus set (Appendix B)

Both parts of Lemma 14 of arXiv:2607.19651, with the paper's constant
`2 N³ (M+1)³ e^{-β/(M-1)}`.

## Main statements

* `SocialNetwork.le_probHittingGT_consensusOther` — **Lemma 14.1**: from `L^o`, `C^{-o}` is not
  reached before `t` with probability at least `exp (-2 t N³ (M+1)³ e^{-β/(M-1)})`.
* `SocialNetwork.probHittingLE_consensusOther_le` — **Lemma 14.2**: from `C^o`, it is reached
  before `t` with probability at most `(N² M + 2 t N³ (M+1)³) e^{-β/(M-1)}`.

## The argument, and where it departs from Appendix B

Appendix B's mechanism is kept, with its ingredients and its constants.  From `L^o` the
process stays in `L̂^o` until an opinion `p ≠ o` is expressed; against a negative pressure that
is a failure, at total rate at most `N M e^{-β/(M-1)}`, and by the actor with the null row it
lands in the extended consensus set `Ĉ^o`, at rate at most `N M`.  From `Ĉ^o` a run of greedy
expressions returns to `L^o`, and it fails with probability at most `1 - ζ_β^{len}` by
Proposition 8 and Remark 4.

**The composition is not the paper's, because the written one does not compose.**  Appendix B
bounds `τ₁⁻ᵒ` and `τ₂⁻ᵒ` separately and multiplies the bounds.  The bound on `τ₂⁻ᵒ` is taken
conditionally on `τ₁⁻ᵒ ≥ t`, and is reached through
`P (T_{n_j} - T_{n_{j-1}} > t | τ₁⁻ᵒ ≥ T_{n_j}) ≥ P (E_j ≥ t)` and a geometric number of such
exponentials taken independent of them.  The conditioning event depends on the interval it
bounds — no negative expression before `T_{n_j}` favours short intervals — and neither step
is argued.  Here the same rates are composed by a first-step comparison with an exponential
clock, by induction on the number of jumps (`SocialNetwork.le_ctsPathMeasure_avoidBefore`):
from a state of phase `j` (`SocialNetwork.ExitInv`) the target is avoided before
`min (t, T_n)` with probability at least `ζ_β^j e^{-Λ t}`, and one step of the induction is
`SocialNetwork.le_ctsPathMeasure_avoidBefore_of_score`.  This is recorded in
`FOR-THE-AUTHORS.md`.

Two smaller changes, neither of which costs anything.

* **The block** is the `N` expressions of the last stage of Proposition 7
  (`SocialNetwork.IsSweepable`), not the `(M+1) N` of all of it: the last stage is all a block
  uses, it does not rest on Lemmas 19 and 20, and it only shortens the constant.  Remark 6
  makes the same choice.
* **Theorem 1.1 is not used.**  The event "not reached before `min (t, T_n)`" decreases to "not
  reached before `t`" whether or not the jump times accumulate
  (`SocialNetwork.le_ctsPathMeasure_lt_hittingTimeCts`).

**Supplies a step the paper asserts**: that the expression of `p ≠ o` by the null row "leads the
process to `Ĉ^o`" (`SocialNetwork.IsSteepLadder.express_isExtendedConsensus`).
-/

namespace SocialNetwork

open Finset MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {N M : ℕ}

/-! ### The extended consensus set of Appendix B

Appendix B leaves `L̂^o` only through an expression of an opinion `p ≠ o` by the actor with the
null row, and that expression lands in

```
Ĉ^o = {u ∈ S : max_b u(b, o) ≥ 1, min_b u(b, o) = 0, max_{b, p ≠ o} u(b, p) < 1},
```

which is not contained in `C^o`: the other actors gain `1` towards `p`, which can leave their
pressure for `p` positive.  What the proof needs of `Ĉ^o` is that it avoids `C^{-o}`, that a
greedy expression from it expresses `o` and stays in it, and that `N` greedy expressions from
it reach `L^o`.  The last is the final stage of Proposition 7, which the repository proves for
any set with the first two properties (`SocialNetwork.IsSweepable`). -/

section Extended

variable {o : Opinion M}

/-- The extended consensus set `Ĉ^o` of Appendix B, in scaled coordinates: the `o`-column is
non-negative, some actor carries at least `1` (that is `M - 1`) for `o`, and every pressure for
another opinion is below `1`.

The paper's `min_b u(b, o) = 0` is written here as non-negativity of the column: in `S` some
row vanishes, so the two say the same thing. -/
structure IsExtendedConsensus (o : Opinion M) (u : Pressure N M) : Prop where
  isState : IsState u
  nonneg : ∀ a, 0 ≤ u a o
  exists_ge : ∃ b, (M : ℤ) - 1 ≤ u b o
  lt : ∀ a, ∀ p ≠ o, u a p < (M : ℤ) - 1

/-- In `Ĉ^o` a maximising pair lies in column `o`: some `o`-entry reaches `1`, and every other
entry stays below it. -/
theorem IsExtendedConsensus.opinion_eq_of_isMax {u : Pressure N M}
    (hu : IsExtendedConsensus o u) {b : Actor N} {p : Opinion M}
    (hmax : ∀ a q, u a q ≤ u b p) : p = o := by
  by_contra hp
  obtain ⟨c, hc⟩ := hu.exists_ge
  have h1 := hu.lt b p hp
  have h2 := hmax c o
  omega

/-- Expressing `o` keeps a state in `Ĉ^o`. -/
theorem IsExtendedConsensus.express (hM : 2 ≤ M) (hN : 2 ≤ N) {u : Pressure N M}
    (hu : IsExtendedConsensus o u) (a : Actor N) :
    IsExtendedConsensus o (SocialNetwork.express a o u) := by
  have hM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  refine ⟨hu.isState.express a o, fun b => ?_, ?_, fun b q hq => ?_⟩
  · by_cases hb : b = a
    · subst hb; simp
    · rw [express_of_ne_of_eq hb]
      have := hu.nonneg b
      omega
  · obtain ⟨b, hb⟩ : ∃ b : Actor N, b ≠ a := by
      have hcard : 1 < Fintype.card (Actor N) := by simp only [Fintype.card_fin]; omega
      exact Fintype.exists_ne_of_one_lt_card hcard a
    refine ⟨b, ?_⟩
    rw [express_of_ne_of_eq hb]
    have := hu.nonneg b
    omega
  · by_cases hb : b = a
    · subst hb; simp; omega
    · rw [express_of_ne_of_ne hb hq]
      have := hu.lt b q hq
      omega

/-- `Ĉ^o` is sweepable, so the last stage of Proposition 7 applies to it. -/
theorem isSweepable_extendedConsensus (hM : 2 ≤ M) (hN : 2 ≤ N) (o : Opinion M) :
    IsSweepable (IsExtendedConsensus (N := N) o) o :=
  ⟨fun _ hu => hu.isState, fun _ hu => hu.nonneg, fun _ hu _ _ h => hu.opinion_eq_of_isMax h,
    fun _ hu a => hu.express hM hN a⟩

/-- `Ĉ^o` avoids `C^{-o}`: a consensus for `p ≠ o` has a non-positive `o`-column. -/
theorem IsExtendedConsensus.notMem_consensusSetOther (hM : 2 ≤ M) {u : Pressure N M}
    (hu : IsExtendedConsensus o u) : u ∉ consensusSetOther N o := by
  rintro ⟨p, hpo, hp⟩
  obtain ⟨b, hb⟩ := hu.exists_ge
  have h1 := hp.nonpos b o (Ne.symm hpo)
  have hM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  omega

/-- A steep ladder avoids `C^{-o}`: its `o`-column has a positive entry. -/
theorem IsSteepLadder.notMem_consensusSetOther (hN : 2 ≤ N) {u : Pressure N M}
    (hu : IsSteepLadder o u) : u ∉ consensusSetOther N o := by
  rintro ⟨p, hpo, hp⟩
  obtain ⟨b, hb⟩ := hu.exists_pos hN
  have h1 := hp.nonpos b o (Ne.symm hpo)
  omega

/-- In a steep ladder only the null row carries a non-negative pressure for another
opinion. -/
theorem IsSteepLadder.eq_zero_of_nonneg (hM : 2 ≤ M) {u : Pressure N M}
    (hu : IsSteepLadder o u) {a : Actor N} {p : Opinion M} (hp : p ≠ o) (h : 0 ≤ u a p) :
    u a o = 0 := by
  have h1 := hu.other a p hp
  have h2 := hu.nonneg a
  have hM' : (0 : ℤ) < (M : ℤ) - 1 := one_lt_of_two_le hM
  nlinarith

/-- In a steep ladder every pressure for another opinion is non-positive. -/
theorem IsSteepLadder.nonpos (hM : 2 ≤ M) {u : Pressure N M} (hu : IsSteepLadder o u)
    (a : Actor N) {p : Opinion M} (hp : p ≠ o) : u a p ≤ 0 := by
  have h1 := hu.other a p hp
  have h2 := hu.nonneg a
  have hM' : (0 : ℤ) < (M : ℤ) - 1 := one_lt_of_two_le hM
  nlinarith

/-- **Leaving `L̂^o` without a negative expression lands in `Ĉ^o`.**  From a steep ladder the
actor with the null row expresses `p ≠ o`: it is reset, the others lose `1/(M-1)` towards `o`,
which keeps them non-negative since their pressure for `o` was a positive integer, and gain
`1` towards `p`, which keeps them below `1` since their pressure for `p` was at most `-1/(M-1)`.
With `N ≥ 3` two other actors carry distinct positive integers for `o`, so one of them still
carries at least `1`.

**Supplies a step the paper asserts**: Appendix B says the expression "leads the process to
`Ĉ^o`" and stops there. -/
theorem IsSteepLadder.express_isExtendedConsensus (hM : 2 ≤ M) (hN : 3 ≤ N)
    {u : Pressure N M} (hu : IsSteepLadder o u) {a : Actor N} (ha : u a o = 0) {p : Opinion M}
    (hp : p ≠ o) : IsExtendedConsensus o (SocialNetwork.express a p u) := by
  have hM2 : (2 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hop : o ≠ p := Ne.symm hp
  -- every other actor carries a positive multiple of `M - 1` for `o`
  have hge : ∀ b, b ≠ a → (M : ℤ) - 1 ≤ u b o := by
    intro b hb
    have hpos : 0 < u b o := by
      rcases lt_or_eq_of_le (hu.nonneg b) with h | h
      · exact h
      · exact absurd (hu.injective (show u b o = u a o by rw [← h, ha])) hb
    obtain ⟨c, hc⟩ := hu.dvd b
    rw [hc] at hpos ⊢
    have hM1 : (0 : ℤ) < (M : ℤ) - 1 := by omega
    have hc1 : 0 < c := pos_of_mul_pos_right hpos hM1.le
    nlinarith
  refine ⟨hu.isState.express a p, fun b => ?_, ?_, fun b q hq => ?_⟩
  · by_cases hb : b = a
    · subst hb; simp
    · rw [express_of_ne_of_ne hb hop]
      have := hge b hb
      omega
  · -- two other actors, with distinct pressures for `o`
    obtain ⟨b, hb, c, hc, hbc⟩ : ∃ b, b ≠ a ∧ ∃ c, c ≠ a ∧ b ≠ c := by
      have hcard : 1 < (Finset.univ.erase a).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨b, hbm, c, hcm, hbc⟩ := Finset.one_lt_card.1 hcard
      exact ⟨b, Finset.ne_of_mem_erase hbm, c, Finset.ne_of_mem_erase hcm, hbc⟩
    have hne : u b o ≠ u c o := fun h => hbc (hu.injective h)
    obtain ⟨kb, hkb⟩ := hu.dvd b
    obtain ⟨kc, hkc⟩ := hu.dvd c
    have hb1 := hge b hb
    have hc1 := hge c hc
    have hM1 : (0 : ℤ) < (M : ℤ) - 1 := by omega
    -- one of them carries at least `2 (M - 1) ≥ M`
    have hbig : (M : ℤ) ≤ u b o ∨ (M : ℤ) ≤ u c o := by
      rw [hkb] at hb1 hne ⊢
      rw [hkc] at hc1 hne ⊢
      have hkb1 : 1 ≤ kb := by nlinarith
      have hkc1 : 1 ≤ kc := by nlinarith
      have hkne : kb ≠ kc := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hkne with h | h
      · right; nlinarith
      · left; nlinarith
    rcases hbig with h | h
    · exact ⟨b, by rw [express_of_ne_of_ne hb hop]; omega⟩
    · exact ⟨c, by rw [express_of_ne_of_ne hc hop]; omega⟩
  · by_cases hb : b = a
    · subst hb; simp; omega
    · by_cases hqp : q = p
      · subst hqp
        rw [express_of_ne_of_eq hb]
        have h1 := hu.other b q hq
        have h2 := hge b hb
        have hM1 : (0 : ℤ) < (M : ℤ) - 1 := by omega
        nlinarith
      · rw [express_of_ne_of_ne hb hqp]
        have := hu.nonpos hM b hq
        omega

end Extended

/-! ### Prepending an expression to a realisation -/

section Cons

/-- The realisation that expresses `(a, p)` first and then runs `T`. -/
def Trajectory.cons (a : Actor N) (p : Opinion M) (T : Trajectory N M) : Trajectory N M where
  actor k := match k with
    | 0 => a
    | k + 1 => T.actor k
  opinion k := match k with
    | 0 => p
    | k + 1 => T.opinion k

theorem Trajectory.cons_state_succ (a : Actor N) (p : Opinion M) (T : Trajectory N M)
    (v : Pressure N M) (k : ℕ) :
    (Trajectory.cons a p T).state v (k + 1) = T.state (express a p v) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Trajectory.state_succ, ih, Trajectory.state_succ]
      rfl

theorem Trajectory.isGreedyAt_cons_zero (a : Actor N) (p : Opinion M) (T : Trajectory N M)
    (v : Pressure N M) :
    IsGreedyAt (Trajectory.cons a p T) v 0 ↔ ∀ b q, v b q ≤ v a p :=
  Iff.rfl

theorem Trajectory.isGreedyAt_cons_succ (a : Actor N) (p : Opinion M) (T : Trajectory N M)
    (v : Pressure N M) (k : ℕ) :
    IsGreedyAt (Trajectory.cons a p T) v (k + 1) ↔ IsGreedyAt T (express a p v) k := by
  unfold IsGreedyAt
  rw [Trajectory.cons_state_succ]
  rfl

end Cons

/-! ### The invariant carried along the comparison

The comparison runs in *phases*.  In phase `0` the state is a steep ladder, and the process is
free: it fails only through an expression against a negative pressure.  An expression of
`p ≠ o` by the null row opens a *block* of `N` expressions, phases `N, N - 1, …, 1`, through
which every expression has to be greedy; a block that succeeds lands on `L^o`, back in phase
`0`.  The paper's block has `(M + 1) N` expressions, the length of Proposition 7; `N` is the
length of its last stage, which is all a block uses, and it only shortens the paper's
constant. -/

section Invariant

variable {o : Opinion M}

/-- The invariant of the phase-`j` states. -/
def ExitInv (o : Opinion M) (v : Pressure N M) : ℕ → Prop
  | 0 => IsSteepLadder o v
  | j + 1 => (IsExtendedConsensus o v ∨ IsConsensus o v) ∧
      ∀ T : Trajectory N M, (∀ k, k < j + 1 → IsGreedyAt T v k) →
        IsSteepLadder o (T.state v (j + 1))

theorem ExitInv.isState {v : Pressure N M} {j : ℕ} (h : ExitInv o v j) : IsState v := by
  cases j with
  | zero => exact IsSteepLadder.isState h
  | succ j => exact h.1.elim (fun h => h.isState) fun h => h.isState

theorem ExitInv.notMem (hM : 2 ≤ M) (hN : 2 ≤ N) {v : Pressure N M} {j : ℕ}
    (h : ExitInv o v j) : v ∉ consensusSetOther N o := by
  cases j with
  | zero => exact IsSteepLadder.notMem_consensusSetOther hN h
  | succ j =>
      exact h.1.elim (fun h => h.notMem_consensusSetOther hM)
        fun h => h.notMem_consensusSetOther

/-- The block phases, for a phase given as a variable. -/
theorem exitInv_of_pos {v : Pressure N M} {k : ℕ} (hk : 0 < k)
    (hset : IsExtendedConsensus o v ∨ IsConsensus o v)
    (hrun : ∀ T : Trajectory N M, (∀ i, i < k → IsGreedyAt T v i) →
      IsSteepLadder o (T.state v k)) : ExitInv o v k := by
  cases k with
  | zero => omega
  | succ j => exact ⟨hset, hrun⟩

/-- A ladder is in phase `0`. -/
theorem exitInv_zero_of_isLadder [NeZero N] (hM : 2 ≤ M) {v : Pressure N M} (hv : IsLadder o v) :
    ExitInv o v 0 :=
  hv.isSteepLadder hM

/-- A consensus state is in phase `N`: the last stage of Proposition 7. -/
theorem exitInv_of_isConsensus (hM : 2 ≤ M) (hN : 2 ≤ N) {v : Pressure N M}
    (hv : IsConsensus o v) : ExitInv o v N := by
  have : NeZero N := ⟨by omega⟩
  exact exitInv_of_pos (by omega) (Or.inr hv) fun T hT =>
    (isLadder_state T hM hN hv hT).isSteepLadder hM

/-- In phase `0`, an expression of `o` stays in phase `0`. -/
theorem ExitInv.express_self (hM : 2 ≤ M) {v : Pressure N M} (hv : ExitInv o v 0)
    (a : Actor N) : ExitInv o (express a o v) 0 :=
  IsSteepLadder.express hM hv a

/-- In phase `0`, an expression of `p ≠ o` against a non-negative pressure opens a block. -/
theorem ExitInv.express_other [NeZero N] (hM : 2 ≤ M) (hN : 3 ≤ N) {v : Pressure N M}
    (hv : ExitInv o v 0) {a : Actor N} {p : Opinion M} (hp : p ≠ o) (h : 0 ≤ v a p) :
    ExitInv o (express a p v) N := by
  have hv' : IsSteepLadder o v := hv
  have hext := hv'.express_isExtendedConsensus hM hN (hv'.eq_zero_of_nonneg hM hp h) hp
  exact exitInv_of_pos (by omega) (Or.inl hext) fun T hT =>
    ((isSweepable_extendedConsensus hM (by omega) o).isLadder_state T hM hext hT).isSteepLadder hM

/-- In a block, a greedy expression moves one phase down. -/
theorem ExitInv.express_greedy (hM : 2 ≤ M) (hN : 2 ≤ N) {v : Pressure N M} {j : ℕ}
    (hv : ExitInv o v (j + 1)) {a : Actor N} {p : Opinion M} (hg : ∀ b q, v b q ≤ v a p) :
    ExitInv o (express a p v) j := by
  obtain ⟨hset, hrun⟩ := hv
  have hpo : p = o := hset.elim (fun h => h.opinion_eq_of_isMax hg)
    fun h => opinion_eq_of_isMax h hg
  subst hpo
  cases j with
  | zero =>
      have h := hrun (Trajectory.cons a p ⟨fun _ => a, fun _ => p⟩) fun k hk => by
        obtain rfl : k = 0 := by omega
        exact (Trajectory.isGreedyAt_cons_zero _ _ _ _).2 hg
      rw [Trajectory.cons_state_succ, Trajectory.state_zero] at h
      exact h
  | succ j =>
      refine ⟨hset.elim (fun h => Or.inl (h.express hM hN a))
        fun h => Or.inr (h.express hM hN a), fun T hT => ?_⟩
      have h := hrun (Trajectory.cons a p T) fun k hk => by
        cases k with
        | zero => exact (Trajectory.isGreedyAt_cons_zero _ _ _ _).2 hg
        | succ k => exact (Trajectory.isGreedyAt_cons_succ _ _ _ _ _).2 (hT k (by omega))
      rwa [Trajectory.cons_state_succ] at h

end Invariant

/-! ### Restarting the hitting time at the first jump

`SocialNetwork.hittingTimeCts_le_shift` bounds the hitting time above by the first holding time
plus the hitting time of the rest; the comparison needs the bound below, which holds as soon as
the starting matrix is outside the target.  On the explosion event the process returns to its
starting matrix after the explosion time, by the convention of `SocialNetwork.jumpCount`, so
the bound holds there too. -/

section Shift

/-- **The hitting time after the first jump, from below.** -/
theorem le_hittingTimeCts_shift (u : Pressure N M) {θ : Set (Pressure N M)} (hu : u ∉ θ)
    {ω : ℕ → Step N M} (hpos : ∀ n, 0 < holdingTime n ω) :
    ENNReal.ofReal (holdingTime 0 ω)
        + hittingTimeCts (express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
      ≤ hittingTimeCts u θ ω := by
  set S₀ := holdingTime 0 ω with hS₀
  have hS₀pos : 0 < S₀ := hpos 0
  conv_rhs => unfold hittingTimeCts
  refine le_sInf ?_
  rintro _ ⟨s, ⟨hs0, hsθ⟩, rfl⟩
  -- the process is still at `u` before the first jump
  have hS₀s : S₀ ≤ s := by
    by_contra hlt
    exact hu (by rwa [process_eq_of_lt_holdingTime u hpos hs0 (not_le.1 hlt)] at hsθ)
  by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ s}
  · -- the shifted realisation is at the same matrix at time `s - S₀`
    have hb' : BddAbove {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s - S₀} := by
      obtain ⟨B, hB⟩ := hb
      refine ⟨B, fun m hm => ?_⟩
      have : jumpTime (m + 1) ω ≤ s := by
        rw [jumpTime_succ_shiftStepPath]
        have : jumpTime m (shiftStepPath ω) ≤ s - S₀ := hm
        linarith
      have := hB this
      omega
    have hne : {m : ℕ | jumpTime m (shiftStepPath ω) ≤ s - S₀}.Nonempty :=
      ⟨0, by simp; linarith⟩
    set m := jumpCount (shiftStepPath ω) (s - S₀) with hm
    have hmem : jumpTime m (shiftStepPath ω) ≤ s - S₀ := Nat.sSup_mem hne hb'
    have hcount : jumpCount ω s = m + 1 := by
      refine (jumpCount_eq_iff s ω (Nat.succ_ne_zero m)).2 ⟨?_, fun k hk => ?_⟩
      · rw [jumpTime_succ_shiftStepPath]; linarith
      · cases k with
        | zero => omega
        | succ j =>
            rw [jumpTime_succ_shiftStepPath] at hk
            have hj : jumpTime j (shiftStepPath ω) ≤ s - S₀ := by linarith
            have h' : j ≤ jumpCount (shiftStepPath ω) (s - S₀) := le_csSup hb' hj
            omega
    have hproc : process (express (ω 0).1.1 (ω 0).1.2 u) (s - S₀) (shiftStepPath ω)
        = process u s ω := by
      show (Trajectory.ofStepPath (shiftStepPath ω)).state _ (jumpCount (shiftStepPath ω) (s - S₀))
        = (Trajectory.ofStepPath ω).state u (jumpCount ω s)
      rw [hcount, ← hm, ofStepPath_shiftStepPath, ← state_one_ofStepPath u ω,
        ← Trajectory.state_add, Nat.add_comm]
    calc ENNReal.ofReal S₀ + hittingTimeCts (express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
        ≤ ENNReal.ofReal S₀ + ENNReal.ofReal (s - S₀) := by
          refine add_le_add le_rfl (sInf_le ⟨s - S₀, ⟨by linarith, ?_⟩, rfl⟩)
          rw [hproc]; exact hsθ
      _ = ENNReal.ofReal s := by
          rw [← ENNReal.ofReal_add hS₀pos.le (by linarith)]
          congr 1; ring
  · -- past an explosion the process sits at `u` again
    exfalso
    have h0 : jumpCount ω s = 0 := Nat.sSup_of_not_bddAbove hb
    apply hu
    have : process u s ω = u := by
      show (Trajectory.ofStepPath ω).state u (jumpCount ω s) = u
      rw [h0, Trajectory.state_zero]
    rwa [this] at hsθ

end Shift

/-! ### Not reaching the target before `min (t, T_n)` -/

section Avoid

/-- The realisations on which `θ` has not been reached before `min (t, T_n)`: either not by
time `t`, or not before the `n`-th jump.  At `n = 0` this is everything, and as `n` grows it
decreases to "not by time `t`" --- whether or not the jump times accumulate, which is why the
comparison below does not need Theorem 1.1. -/
def avoidBefore (u : Pressure N M) (θ : Set (Pressure N M)) (n : ℕ) (t : ℝ) :
    Set (ℕ → Step N M) :=
  {ω | ENNReal.ofReal t < hittingTimeCts u θ ω ∨
    ENNReal.ofReal (jumpTime n ω) ≤ hittingTimeCts u θ ω}

/-- The same events, at all times at once. -/
def avoidBeforeGraph (u : Pressure N M) (θ : Set (Pressure N M)) (n : ℕ) :
    Set (ℝ × (ℕ → Step N M)) :=
  {x | x.2 ∈ avoidBefore u θ n x.1}

theorem measurableSet_avoidBeforeGraph (u : Pressure N M) (θ : Set (Pressure N M)) (n : ℕ) :
    MeasurableSet (avoidBeforeGraph u θ n) := by
  have h1 : Measurable fun x : ℝ × (ℕ → Step N M) => hittingTimeCts u θ x.2 :=
    (measurable_hittingTimeCts u θ).comp measurable_snd
  have h2 : Measurable fun x : ℝ × (ℕ → Step N M) => ENNReal.ofReal x.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have h3 : Measurable fun x : ℝ × (ℕ → Step N M) => ENNReal.ofReal (jumpTime n x.2) :=
    ENNReal.measurable_ofReal.comp ((measurable_jumpTime n).comp measurable_snd)
  have hset : avoidBeforeGraph u θ n
      = {x : ℝ × (ℕ → Step N M) | ENNReal.ofReal x.1 < hittingTimeCts u θ x.2}
        ∪ {x | ENNReal.ofReal (jumpTime n x.2) ≤ hittingTimeCts u θ x.2} := rfl
  rw [hset]
  exact (measurableSet_lt h2 h1).union (measurableSet_le h3 h1)

theorem measurableSet_avoidBefore (u : Pressure N M) (θ : Set (Pressure N M)) (n : ℕ) (t : ℝ) :
    MeasurableSet (avoidBefore u θ n t) := by
  show MeasurableSet (Prod.mk t ⁻¹' avoidBeforeGraph u θ n)
  exact measurable_prodMk_left (measurableSet_avoidBeforeGraph u θ n)

theorem avoidBefore_zero (u : Pressure N M) (θ : Set (Pressure N M)) (t : ℝ) :
    avoidBefore u θ 0 t = Set.univ := by
  ext ω
  simp [avoidBefore]

variable [NeZero N] [NeZero M]

/-- The realisations whose holding times are all positive carry all the mass. -/
theorem ctsPathMeasure_holdingTime_pos_compl (β : ℝ) (u : Pressure N M) :
    ctsPathMeasure β u {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}ᶜ = 0 := by
  rw [show {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}ᶜ
      = {ω : ℕ → Step N M | ∃ n, holdingTime n ω ≤ 0} from by
    ext ω; simp [not_forall, not_lt]]
  exact ctsPathMeasure_exists_holdingTime_nonpos β u

omit [NeZero N] [NeZero M] in
theorem measurableSet_holdingTime_pos :
    MeasurableSet {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} := by
  rw [show {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω}
      = ⋂ n, {ω | 0 < holdingTime n ω} from by ext ω; simp]
  exact MeasurableSet.iInter fun n => (measurable_holdingTime n) measurableSet_Ioi

/-- **The first-step inequality.**  From `u ∉ θ`, the target is avoided before `min (t, T_{n+1})`
if no jump occurs by `t`, or if the first jump occurs at `s ≤ t` and the rest of the realisation
avoids it before `min (t - s, T_n)`. -/
theorem le_ctsPathMeasure_avoidBefore_succ (β : ℝ) {u : Pressure N M} {θ : Set (Pressure N M)}
    (hu : u ∉ θ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-(totalRate β u * t)))
        + ∫⁻ z, ctsPathMeasure β (express z.1.1 z.1.2 u)
            {ω' | z.2 ≤ t ∧ ω' ∈ avoidBefore (express z.1.1 z.1.2 u) θ n (t - z.2)}
            ∂(stepLaw β u)
      ≤ ctsPathMeasure β u (avoidBefore u θ (n + 1) t) := by
  set G := {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} with hGdef
  set S : Set (Step N M × (ℕ → Step N M)) :=
    {x | x.1.2 ≤ t ∧ x.2 ∈ avoidBefore (express x.1.1.1 x.1.1.2 u) θ n (t - x.1.2)} with hSdef
  have hSmeas : MeasurableSet S := by
    have hset : S = ⋃ p : Jump N M,
        ((fun x : Step N M × (ℕ → Step N M) => x.1.1) ⁻¹' {p})
          ∩ (((fun x : Step N M × (ℕ → Step N M) => x.1.2) ⁻¹' Set.Iic t)
            ∩ ((fun x : Step N M × (ℕ → Step N M) => (t - x.1.2, x.2)) ⁻¹'
              avoidBeforeGraph (express p.1 p.2 u) θ n)) := by
      ext x
      simp only [hSdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_Iic, avoidBeforeGraph, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨x.1.1, rfl, h1, h2⟩
      · rintro ⟨p, rfl, h1, h2⟩
        exact ⟨h1, h2⟩
    rw [hset]
    refine MeasurableSet.iUnion fun p => ?_
    refine ((measurable_fst.comp measurable_fst) (measurableSet_singleton p)).inter
      (((measurable_snd.comp measurable_fst) measurableSet_Iic).inter ?_)
    exact ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
      (measurableSet_avoidBeforeGraph _ θ n)
  set A : Set (ℕ → Step N M) := {ω | t < holdingTime 0 ω} with hAdef
  set B : Set (ℕ → Step N M) := {ω | (ω 0, shiftStepPath ω) ∈ S} with hBdef
  have hBmeas : MeasurableSet B :=
    ((measurable_pi_apply 0).prodMk measurable_shiftStepPath) hSmeas
  have hA : ctsPathMeasure β u A = ENNReal.ofReal (Real.exp (-(totalRate β u * t))) :=
    ctsPathMeasure_lt_holdingTime β u ht
  have hB : ctsPathMeasure β u B
      = ∫⁻ z, ctsPathMeasure β (express z.1.1 z.1.2 u)
          {ω' | z.2 ≤ t ∧ ω' ∈ avoidBefore (express z.1.1 z.1.2 u) θ n (t - z.2)}
          ∂(stepLaw β u) :=
    ctsPathMeasure_firstStep_apply β u hSmeas
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ω hA ⟨hB, -⟩
    exact absurd hB (not_le.2 hA)
  have hsub : (A ∪ B) ∩ G ⊆ avoidBefore u θ (n + 1) t := by
    rintro ω ⟨hAB, hG⟩
    have hG' : ∀ n, 0 < holdingTime n ω := hG
    have hkey := le_hittingTimeCts_shift u hu hG'
    set R' := hittingTimeCts (express (ω 0).1.1 (ω 0).1.2 u) θ (shiftStepPath ω)
    have hS₀ : 0 < holdingTime 0 ω := hG' 0
    rcases hAB with hω | ⟨hle, hω⟩
    · change t < holdingTime 0 ω at hω
      left
      calc ENNReal.ofReal t < ENNReal.ofReal (holdingTime 0 ω) :=
            (ENNReal.ofReal_lt_ofReal_iff hS₀).2 hω
        _ ≤ ENNReal.ofReal (holdingTime 0 ω) + R' := le_self_add
        _ ≤ hittingTimeCts u θ ω := hkey
    · change holdingTime 0 ω ≤ t at hle
      change ENNReal.ofReal (t - holdingTime 0 ω) < R'
        ∨ ENNReal.ofReal (jumpTime n (shiftStepPath ω)) ≤ R' at hω
      rcases hω with hω | hω
      · left
        calc ENNReal.ofReal t
            = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal (t - holdingTime 0 ω) := by
              rw [← ENNReal.ofReal_add hS₀.le (by linarith)]; congr 1; ring
          _ < ENNReal.ofReal (holdingTime 0 ω) + R' :=
              ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hω
          _ ≤ hittingTimeCts u θ ω := hkey
      · right
        have hTn : 0 ≤ jumpTime n (shiftStepPath ω) :=
          Finset.sum_nonneg fun k _ => by
            rw [holdingTime_shiftStepPath]; exact (hG' (k + 1)).le
        calc ENNReal.ofReal (jumpTime (n + 1) ω)
            = ENNReal.ofReal (holdingTime 0 ω) + ENNReal.ofReal (jumpTime n (shiftStepPath ω)) := by
              rw [jumpTime_succ_shiftStepPath, ENNReal.ofReal_add hS₀.le hTn]
          _ ≤ ENNReal.ofReal (holdingTime 0 ω) + R' := add_le_add le_rfl hω
          _ ≤ hittingTimeCts u θ ω := hkey
  have hGnull := ctsPathMeasure_holdingTime_pos_compl β u
  have hconull : ctsPathMeasure β u ((A ∪ B) ∩ G) = ctsPathMeasure β u (A ∪ B) := by
    have h := measure_inter_add_sdiff (μ := ctsPathMeasure β u) (A ∪ B) measurableSet_holdingTime_pos
    rwa [measure_mono_null (Set.sdiff_subset_compl _ _) hGnull, add_zero] at h
  rw [← hA, ← hB, ← measure_union hdisj hBmeas, ← hconull]
  exact measure_mono hsub

/-- **Passing to the limit.**  A lower bound on every `avoidBefore u θ n t` is a lower bound on
"not by time `t`": the events decrease, and their intersection lies in it. -/
theorem le_ctsPathMeasure_lt_hittingTimeCts (β : ℝ) {u : Pressure N M}
    {θ : Set (Pressure N M)} (hu : u ∉ θ) {t : ℝ} {c : ℝ≥0∞}
    (h : ∀ n, c ≤ ctsPathMeasure β u (avoidBefore u θ n t)) :
    c ≤ ctsPathMeasure β u {ω | ENNReal.ofReal t < hittingTimeCts u θ ω} := by
  set G := {ω : ℕ → Step N M | ∀ n, 0 < holdingTime n ω} with hGdef
  set s : ℕ → Set (ℕ → Step N M) := fun n => avoidBefore u θ n t ∩ G with hsdef
  have hGnull := ctsPathMeasure_holdingTime_pos_compl β u
  have hconull : ∀ n, ctsPathMeasure β u (s n) = ctsPathMeasure β u (avoidBefore u θ n t) := by
    intro n
    have h := measure_inter_add_sdiff (μ := ctsPathMeasure β u) (avoidBefore u θ n t)
      measurableSet_holdingTime_pos
    rwa [measure_mono_null (Set.sdiff_subset_compl _ _) hGnull, add_zero] at h
  have hanti : Antitone s := by
    refine antitone_nat_of_succ_le fun n => ?_
    rintro ω ⟨hω, hG⟩
    refine ⟨?_, hG⟩
    rcases hω with hω | hω
    · exact Or.inl hω
    · right
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hω
      rw [jumpTime_succ]
      linarith [(hG : ∀ n, 0 < holdingTime n ω) n]
  have hinter : (⋂ n, s n) ⊆ {ω | ENNReal.ofReal t < hittingTimeCts u θ ω} := by
    intro ω hω
    rw [Set.mem_iInter] at hω
    have hG : ∀ n, 0 < holdingTime n ω := (hω 0).2
    by_contra hnot
    have hall : ∀ n, ENNReal.ofReal (jumpTime n ω) ≤ hittingTimeCts u θ ω := fun n =>
      (hω n).1.resolve_left hnot
    -- then `θ` is never reached at all
    apply hnot
    show ENNReal.ofReal t < hittingTimeCts u θ ω
    suffices htop : hittingTimeCts u θ ω = ⊤ by rw [htop]; exact ENNReal.ofReal_lt_top
    unfold hittingTimeCts
    rw [sInf_eq_top]
    rintro _ ⟨r, ⟨hr0, hrθ⟩, rfl⟩
    exfalso
    by_cases hb : BddAbove {n : ℕ | jumpTime n ω ≤ r}
    · have hne : {n : ℕ | jumpTime n ω ≤ r}.Nonempty := ⟨0, by simpa using hr0⟩
      set k := jumpCount ω r with hk
      have hkmem : jumpTime k ω ≤ r := Nat.sSup_mem hne hb
      have hmono := jumpTime_mono hG
      -- the process is in `θ` from the `k`-th jump on, so `R ≤ T_k`
      have hk0 : 0 ≤ jumpTime k ω := Finset.sum_nonneg fun i _ => (hG i).le
      have hcountk : jumpCount ω (jumpTime k ω) = k := by
        have hbk : BddAbove {n : ℕ | jumpTime n ω ≤ jumpTime k ω} :=
          hb.mono fun n hn => le_trans hn hkmem
        have hkk : k ∈ {n : ℕ | jumpTime n ω ≤ jumpTime k ω} := le_refl (jumpTime k ω)
        refine le_antisymm (csSup_le ⟨k, hkk⟩ fun n hn => ?_) (le_csSup hbk hkk)
        by_contra hlt
        have hstep : jumpTime (k + 1) ω ≤ jumpTime n ω := hmono (by omega)
        rw [jumpTime_succ] at hstep
        have : jumpTime n ω ≤ jumpTime k ω := hn
        linarith [hG k]
      have hR : hittingTimeCts u θ ω ≤ ENNReal.ofReal (jumpTime k ω) := by
        unfold hittingTimeCts
        refine sInf_le ⟨jumpTime k ω, ⟨hk0, ?_⟩, rfl⟩
        show (Trajectory.ofStepPath ω).state u (jumpCount ω (jumpTime k ω)) ∈ θ
        rw [hcountk]
        exact hrθ
      have h1 := le_trans (hall (k + 1)) hR
      rw [ENNReal.ofReal_le_ofReal_iff hk0, jumpTime_succ] at h1
      linarith [hG k]
    · have h0 : jumpCount ω r = 0 := Nat.sSup_of_not_bddAbove hb
      apply hu
      have : process u r ω = u := by
        show (Trajectory.ofStepPath ω).state u (jumpCount ω r) = u
        rw [h0, Trajectory.state_zero]
      rwa [this] at hrθ
  have hsmeas : ∀ n, MeasurableSet (s n) := fun n =>
    (measurableSet_avoidBefore u θ n t).inter measurableSet_holdingTime_pos
  have hlim : ctsPathMeasure β u (⋂ n, s n) = ⨅ n, ctsPathMeasure β u (s n) :=
    hanti.measure_iInter (fun n => (hsmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  calc c ≤ ⨅ n, ctsPathMeasure β u (s n) := le_iInf fun n => by rw [hconull]; exact h n
    _ = ctsPathMeasure β u (⋂ n, s n) := hlim.symm
    _ ≤ _ := measure_mono hinter

end Avoid

/-! ### Comparing with an exponential clock

One step of the comparison: from a state with total rate `q`, the mass that survives to time `t`
is at least the chance that the clock has not rung, plus the chance that it rang at `s ≤ t` on a
pair of score `sc`, weighted by what survives from there.  If every pair's score is backed by
`e^{-Λ(t-s)}` and the scores carry rate `W ≥ (q - Λ) φ`, this is at least `φ e^{-Λ t}`. -/

section Comparison

/-- The holding-time integral of the comparison, for `Λ < q`: a change of rate turns it into
the law of an exponential clock of rate `q - Λ`. -/
theorem lintegral_expMeasure_Iic_exp {q Λ : ℝ} (hΛq : Λ < q) (hΛ : 0 ≤ Λ) (t : ℝ) :
    ∫⁻ s, (Set.Iic t).indicator (fun s => ENNReal.ofReal (Real.exp (-(Λ * (t - s))))) s
        ∂(expMeasure q)
      = ENNReal.ofReal (q / (q - Λ) * Real.exp (-(Λ * t))) * expMeasure (q - Λ) (Set.Iic t) := by
  have hq : 0 < q := lt_of_le_of_lt hΛ hΛq
  have hqΛ : 0 < q - Λ := by linarith
  have hd : Measurable (exponentialPDF q) := (measurable_exponentialPDFReal q).ennreal_ofReal
  have hd' : Measurable (exponentialPDF (q - Λ)) :=
    (measurable_exponentialPDFReal (q - Λ)).ennreal_ofReal
  have hf : Measurable ((Set.Iic t).indicator
      (fun s : ℝ => ENNReal.ofReal (Real.exp (-(Λ * (t - s)))))) :=
    Measurable.indicator (by fun_prop) measurableSet_Iic
  rw [show expMeasure q = volume.withDensity (exponentialPDF q) from rfl,
    lintegral_withDensity_eq_lintegral_mul _ hd hf,
    show expMeasure (q - Λ) = volume.withDensity (exponentialPDF (q - Λ)) from rfl,
    withDensity_apply _ measurableSet_Iic, ← lintegral_indicator measurableSet_Iic,
    ← lintegral_const_mul _ (hd'.indicator measurableSet_Iic)]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  by_cases hst : s ≤ t
  · have hmem : s ∈ Set.Iic t := hst
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, exponentialPDF_eq,
      exponentialPDF_eq]
    by_cases hs0 : 0 ≤ s
    · rw [if_pos hs0, if_pos hs0, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have e1 : Real.exp (-(q * s)) * Real.exp (-(Λ * (t - s)))
          = Real.exp (-(Λ * t)) * Real.exp (-((q - Λ) * s)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc q * Real.exp (-(q * s)) * Real.exp (-(Λ * (t - s)))
          = q * (Real.exp (-(Λ * t)) * Real.exp (-((q - Λ) * s))) := by rw [mul_assoc, e1]
        _ = q / (q - Λ) * Real.exp (-(Λ * t)) * ((q - Λ) * Real.exp (-((q - Λ) * s))) := by
          field_simp
    · rw [if_neg hs0, if_neg hs0]
      simp
  · have hmem : s ∉ Set.Iic t := hst
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    simp

/-- **One step of the comparison, as a statement about numbers.** -/
theorem le_exp_add_mul_lintegral {q Λ φ W t : ℝ} (hq : 0 < q) (hΛ : 0 ≤ Λ) (hφ1 : φ ≤ 1) (hW : 0 ≤ W) (hcomp : (q - Λ) * φ ≤ W) (ht : 0 ≤ t) :
    ENNReal.ofReal (φ * Real.exp (-(Λ * t)))
      ≤ ENNReal.ofReal (Real.exp (-(q * t)))
        + ENNReal.ofReal (W / q)
          * ∫⁻ s, (Set.Iic t).indicator (fun s => ENNReal.ofReal (Real.exp (-(Λ * (t - s))))) s
            ∂(expMeasure q) := by
  rcases le_or_gt q Λ with hqΛ | hΛq
  · -- the clock at `u` is already slower than `Λ`
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
    have h1 : Real.exp (-(Λ * t)) ≤ Real.exp (-(q * t)) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : 0 ≤ Real.exp (-(Λ * t)) := (Real.exp_pos _).le
    nlinarith
  · have hqΛ : 0 < q - Λ := by linarith
    rw [lintegral_expMeasure_Iic_exp hΛq hΛ t, expMeasure_Iic_of_nonneg hqΛ ht, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hW hq.le) (by positivity)),
      ← ENNReal.ofReal_add (Real.exp_pos _).le]
    · refine ENNReal.ofReal_le_ofReal ?_
      set a := Real.exp (-(Λ * t)) with ha
      set b := Real.exp (-((q - Λ) * t)) with hb
      have ha0 : 0 ≤ a := (Real.exp_pos _).le
      have hb0 : 0 ≤ b := (Real.exp_pos _).le
      have hb1 : b ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hab : Real.exp (-(q * t)) = a * b := by
        rw [ha, hb, ← Real.exp_add]; congr 1; ring
      have hφW : φ ≤ W / q * (q / (q - Λ)) := by
        rw [div_mul_div_comm, mul_comm W q, mul_div_mul_left W (q - Λ) hq.ne']
        rw [le_div_iff₀ hqΛ]
        linarith
      rw [hab]
      have h3 : φ * (a * (1 - b)) ≤ W / q * (q / (q - Λ)) * (a * (1 - b)) :=
        mul_le_mul_of_nonneg_right hφW (mul_nonneg ha0 (by linarith))
      have h4 : φ * (a * b) ≤ a * b := mul_le_of_le_one_left (mul_nonneg ha0 hb0) hφ1
      calc φ * a = φ * (a * (1 - b)) + φ * (a * b) := by ring
        _ ≤ W / q * (q / (q - Λ)) * (a * (1 - b)) + a * b := add_le_add h3 h4
        _ = a * b + W / q * (q / (q - Λ) * a) * (1 - b) := by ring
    · refine mul_nonneg (mul_nonneg (div_nonneg hW hq.le) (by positivity)) ?_
      have : Real.exp (-((q - Λ) * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      linarith

variable [NeZero N] [NeZero M]

/-- The jump law, written with the rates. -/
theorem jumpPMF_eq_ofReal (β : ℝ) (v : Pressure N M) (p : Jump N M) :
    jumpPMF β v p = ENNReal.ofReal (jumpRate β v p.1 p.2 / totalRate β v) := by
  have hpos := totalRate_pos β v
  have hsum : ∑' q : Jump N M, jumpWeight β v q = ENNReal.ofReal (totalRate β v) := by
    rw [tsum_fintype, totalRate]
    exact (ENNReal.ofReal_sum_of_nonneg fun q _ => (jumpRate_pos β v q.1 q.2).le).symm
  rw [jumpPMF_apply, hsum, jumpWeight, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hpos]

/-- Integrating a score against the jump law. -/
theorem lintegral_jumpPMF_ofReal (β : ℝ) (v : Pressure N M) {sc : Jump N M → ℝ}
    (hsc : ∀ p, 0 ≤ sc p) :
    ∫⁻ p, ENNReal.ofReal (sc p) ∂(jumpPMF β v).toMeasure
      = ENNReal.ofReal ((∑ p, sc p * jumpRate β v p.1 p.2) / totalRate β v) := by
  have hpos := totalRate_pos β v
  rw [lintegral_countable', tsum_fintype]
  have hterm : ∀ p : Jump N M, ENNReal.ofReal (sc p) * (jumpPMF β v).toMeasure {p}
      = ENNReal.ofReal (sc p * jumpRate β v p.1 p.2 / totalRate β v) := by
    intro p
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), jumpPMF_eq_ofReal,
      ← ENNReal.ofReal_mul (hsc p), mul_div_assoc]
  rw [Finset.sum_congr rfl fun p _ => hterm p,
    ← ENNReal.ofReal_sum_of_nonneg fun p _ =>
      div_nonneg (mul_nonneg (hsc p) (jumpRate_pos β v p.1 p.2).le) hpos.le,
    Finset.sum_div]

/-- **One step of the comparison.**  If every pair `p` carries a score `sc p` backed, from the
matrix it leads to, by `sc p · e^{-Λ(t-s)}` for every first-jump time `s ≤ t`, and the scores
carry rate at least `(q - Λ) φ`, then `φ e^{-Λ t}` is avoided before `min (t, T_{n+1})`. -/
theorem le_ctsPathMeasure_avoidBefore_of_score (β : ℝ) {u : Pressure N M}
    {θ : Set (Pressure N M)} (hu : u ∉ θ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {Λ φ : ℝ}
    (hΛ : 0 ≤ Λ) (hφ1 : φ ≤ 1) (sc : Jump N M → ℝ) (hsc : ∀ p, 0 ≤ sc p)
    (hcomp : (totalRate β u - Λ) * φ ≤ ∑ p, sc p * jumpRate β u p.1 p.2)
    (hIH : ∀ p : Jump N M, ∀ s : ℝ, s ≤ t →
      ENNReal.ofReal (sc p * Real.exp (-(Λ * (t - s))))
        ≤ ctsPathMeasure β (express p.1 p.2 u) (avoidBefore (express p.1 p.2 u) θ n (t - s))) :
    ENNReal.ofReal (φ * Real.exp (-(Λ * t))) ≤ ctsPathMeasure β u (avoidBefore u θ (n + 1) t) := by
  have hq := totalRate_pos β u
  have hE : IsProbabilityMeasure (expMeasure (totalRate β u)) := isProbabilityMeasure_expMeasure hq
  set W := ∑ p, sc p * jumpRate β u p.1 p.2 with hWdef
  have hW : 0 ≤ W := Finset.sum_nonneg fun p _ => mul_nonneg (hsc p) (jumpRate_pos β u p.1 p.2).le
  set g : ℝ → ℝ≥0∞ :=
    (Set.Iic t).indicator (fun s => ENNReal.ofReal (Real.exp (-(Λ * (t - s))))) with hgdef
  have hg : Measurable g := Measurable.indicator (by fun_prop) measurableSet_Iic
  have hprod : ∫⁻ z, ENNReal.ofReal (sc z.1) * g z.2 ∂(stepLaw β u)
      = ENNReal.ofReal (W / totalRate β u) * ∫⁻ s, g s ∂(expMeasure (totalRate β u)) := by
    rw [stepLaw, lintegral_prod_mul (f := fun p => ENNReal.ofReal (sc p)) (g := g)
      (measurable_of_countable _).aemeasurable hg.aemeasurable, lintegral_jumpPMF_ofReal β u hsc]
  have hpt : ∀ z : Step N M, ENNReal.ofReal (sc z.1) * g z.2
      ≤ ctsPathMeasure β (express z.1.1 z.1.2 u)
          {ω' | z.2 ≤ t ∧ ω' ∈ avoidBefore (express z.1.1 z.1.2 u) θ n (t - z.2)} := by
    rintro ⟨p, s⟩
    by_cases hs : s ≤ t
    · have hmem : s ∈ Set.Iic t := hs
      simp only [hgdef, Set.indicator_of_mem hmem]
      rw [← ENNReal.ofReal_mul (hsc p)]
      have hset : {ω' | s ≤ t ∧ ω' ∈ avoidBefore (express p.1 p.2 u) θ n (t - s)}
          = avoidBefore (express p.1 p.2 u) θ n (t - s) := by
        ext ω'; simp [hs]
      rw [hset]
      exact hIH p s hs
    · have hmem : s ∉ Set.Iic t := hs
      simp [hgdef, Set.indicator_of_notMem hmem]
  calc ENNReal.ofReal (φ * Real.exp (-(Λ * t)))
      ≤ ENNReal.ofReal (Real.exp (-(totalRate β u * t)))
        + ENNReal.ofReal (W / totalRate β u) * ∫⁻ s, g s ∂(expMeasure (totalRate β u)) :=
        le_exp_add_mul_lintegral hq hΛ hφ1 hW hcomp ht
    _ = ENNReal.ofReal (Real.exp (-(totalRate β u * t)))
        + ∫⁻ z, ENNReal.ofReal (sc z.1) * g z.2 ∂(stepLaw β u) := by rw [hprod]
    _ ≤ ENNReal.ofReal (Real.exp (-(totalRate β u * t)))
        + ∫⁻ z, ctsPathMeasure β (express z.1.1 z.1.2 u)
            {ω' | z.2 ≤ t ∧ ω' ∈ avoidBefore (express z.1.1 z.1.2 u) θ n (t - z.2)}
            ∂(stepLaw β u) := add_le_add le_rfl (lintegral_mono hpt)
    _ ≤ ctsPathMeasure β u (avoidBefore u θ (n + 1) t) :=
        le_ctsPathMeasure_avoidBefore_succ β hu n ht

end Comparison

/-! ### Lemma 14

The rate of failure is `Λ = 2 N³ (M+1)³ e^{-β/(M-1)}`, the paper's.  In phase `0` the pairs
expressing against a negative pressure fail, at total rate at most `N M e^{-β/(M-1)}`, and the
pairs expressing `p ≠ o` against a non-negative pressure open a block, at total rate at most
`N M`, which fails with probability at most `1 - ζ_β^N ≤ N · M N e^{-β/(M-1)}` by Proposition 8
and Remark 4.  Inside a block every expression has to be greedy, which it is with probability at
least `ζ_β` whatever the matrix. -/

section Rates

variable [NeZero N] [NeZero M]

/-- The rate of failure, `2 N³ (M+1)³ e^{-β/(M-1)}`. -/
noncomputable def exitRate (N M : ℕ) (β : ℝ) : ℝ :=
  2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))

theorem exitRate_nonneg (N M : ℕ) (β : ℝ) : 0 ≤ exitRate N M β := by
  unfold exitRate; positivity

omit [NeZero N] [NeZero M] in
/-- An expression against a negative pressure has rate at most `e^{-β/(M-1)}`. -/
theorem jumpRate_le_of_neg (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M}
    {a : Actor N} {p : Opinion M} (h : v a p < 0) :
    jumpRate β v a p ≤ Real.exp (-β / ((M : ℝ) - 1)) := by
  unfold jumpRate
  refine Real.exp_le_exp.2 ?_
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hv : (v a p : ℝ) ≤ -1 := by exact_mod_cast (show v a p ≤ -1 by omega)
  rw [div_le_div_iff_of_pos_right hM1]
  nlinarith

omit [NeZero N] [NeZero M] in
/-- An expression against a non-positive pressure has rate at most `1`. -/
theorem jumpRate_le_one (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {v : Pressure N M} {a : Actor N}
    {p : Opinion M} (h : v a p ≤ 0) : jumpRate β v a p ≤ 1 := by
  unfold jumpRate
  refine Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg ?_ ?_)
  · have : (v a p : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith
  · have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith

omit [NeZero N] [NeZero M] in
theorem card_jump (N M : ℕ) : Fintype.card (Jump N M) = N * M := by
  simp [Jump, Fintype.card_prod, Fintype.card_fin]

omit [NeZero N] [NeZero M] in
/-- `N M + N³ M² ≤ 2 N³ (M+1)³`: the paper's constant absorbs both rates. -/
theorem rates_le_exitRate_const (N M : ℕ) :
    (N : ℝ) * M + (N : ℝ) * ((M : ℝ) * N * N * M) ≤ 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) := by
  push_cast
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hpos
    have h1 : (N : ℝ) * M ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by
      have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
      have hNN : (N : ℝ) ≤ (N : ℝ) ^ 3 := by
        calc (N : ℝ) = N * 1 := by ring
          _ ≤ N * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hN2 hN
          _ = (N : ℝ) ^ 3 := by ring
      have hM2 : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
      have hMM : (M : ℝ) ≤ ((M : ℝ) + 1) ^ 3 := by
        calc (M : ℝ) ≤ ((M : ℝ) + 1) * 1 := by linarith
          _ ≤ ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left hM2 (by linarith)
          _ = ((M : ℝ) + 1) ^ 3 := by ring
      calc (N : ℝ) * M ≤ (N : ℝ) ^ 3 * M := mul_le_mul_of_nonneg_right hNN hM
        _ ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left hMM (by positivity)
    have h2 : (N : ℝ) * ((M : ℝ) * N * N * M) ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := by
      have hMM : (M : ℝ) * M ≤ ((M : ℝ) + 1) ^ 3 := by
        calc (M : ℝ) * M ≤ ((M : ℝ) + 1) ^ 2 * 1 := by nlinarith
          _ ≤ ((M : ℝ) + 1) ^ 2 * ((M : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = ((M : ℝ) + 1) ^ 3 := by ring
      calc (N : ℝ) * ((M : ℝ) * N * N * M) = (N : ℝ) ^ 3 * ((M : ℝ) * M) := by ring
        _ ≤ (N : ℝ) ^ 3 * ((M : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left hMM (by positivity)
    linarith

omit [NeZero N] [NeZero M] in
/-- **Phase `0`.**  The rate of the pairs that fail, plus the rate of those that open a block
times the chance the block fails, is at most `Λ`. -/
theorem rate_phase_zero (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) {o : Opinion M} {v : Pressure N M}
    (hv : IsSteepLadder o v) :
    (totalRate β v - exitRate N M β) * zeta N M β ^ 0
      ≤ ∑ p : Jump N M, (if v p.1 p.2 < 0 then 0 else if p.2 = o then 1 else zeta N M β ^ N)
          * jumpRate β v p.1 p.2 := by
  set e := Real.exp (-β / ((M : ℝ) - 1)) with he
  set z := zeta N M β ^ N with hz
  have hz1 : z ≤ 1 := pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β)
  have hz0 : 0 ≤ z := pow_nonneg (zeta_pos N M β).le N
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  -- each pair loses at most `e + (1 - ζ^N)` of its rate
  have hterm : ∀ p : Jump N M,
      jumpRate β v p.1 p.2
        - (if v p.1 p.2 < 0 then 0 else if p.2 = o then 1 else z) * jumpRate β v p.1 p.2
        ≤ e + (1 - z) := by
    intro p
    have hr := (jumpRate_pos β v p.1 p.2).le
    by_cases hneg : v p.1 p.2 < 0
    · rw [if_pos hneg]
      have := jumpRate_le_of_neg hM hβ hneg
      linarith
    · rw [if_neg hneg]
      by_cases ho : p.2 = o
      · rw [if_pos ho]; linarith
      · rw [if_neg ho]
        have h1 := jumpRate_le_one hM hβ (hv.nonpos hM p.1 ho)
        nlinarith
  have hsum : totalRate β v
      - ∑ p : Jump N M, (if v p.1 p.2 < 0 then 0 else if p.2 = o then 1 else z)
          * jumpRate β v p.1 p.2
      ≤ (N * M : ℕ) * (e + (1 - z)) := by
    rw [totalRate, ← Finset.sum_sub_distrib]
    calc ∑ p : Jump N M, (jumpRate β v p.1 p.2
            - (if v p.1 p.2 < 0 then 0 else if p.2 = o then 1 else z) * jumpRate β v p.1 p.2)
        ≤ ∑ _p : Jump N M, (e + (1 - z)) := Finset.sum_le_sum fun p _ => hterm p
      _ = (N * M : ℕ) * (e + (1 - z)) := by
          rw [Finset.sum_const, Finset.card_univ, card_jump, nsmul_eq_mul]
  -- Remark 4 bounds the chance a block fails
  have hrem := one_sub_le_zeta_pow N M β N
  rw [← neg_div, ← he, ← hz] at hrem
  have hconst := rates_le_exitRate_const N M
  have hΛ : (N * M : ℕ) * (e + (1 - z)) ≤ exitRate N M β := by
    have h1 : (1 - z) ≤ (N : ℝ) * ((M : ℝ) * N * e) := by linarith
    have hNM : (0 : ℝ) ≤ ((N * M : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((N * M : ℕ) : ℝ) * (e + (1 - z))
        ≤ ((N * M : ℕ) : ℝ) * (e + (N : ℝ) * ((M : ℝ) * N * e)) :=
          mul_le_mul_of_nonneg_left (by linarith) hNM
      _ = ((N : ℝ) * M + (N : ℝ) * ((M : ℝ) * N * N * M)) * e := by push_cast; ring
      _ ≤ 2 * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * e := mul_le_mul_of_nonneg_right hconst he0
      _ = exitRate N M β := rfl
  rw [pow_zero, mul_one]
  linarith

/-- **In a block.**  The greedy pairs carry rate at least `ζ_β q`. -/
theorem rate_phase_succ (hM : 2 ≤ M) {β : ℝ} (hβ : 0 ≤ β) (v : Pressure N M) (j : ℕ) :
    (totalRate β v - exitRate N M β) * zeta N M β ^ (j + 1)
      ≤ ∑ p : Jump N M, (if p ∈ argmaxFinset v then zeta N M β ^ j else 0)
          * jumpRate β v p.1 p.2 := by
  have hq := totalRate_pos β v
  have hζ := zeta_pos N M β
  -- Proposition 8: the greedy pairs carry probability at least `ζ_β`
  have h8 := zeta_le_jumpPMF_argmaxFinset hM hβ v
  rw [PMF.toMeasure_apply_finset] at h8
  have hsum : ∑ p ∈ argmaxFinset v, jumpPMF β v p
      = ENNReal.ofReal ((∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2) / totalRate β v) := by
    rw [Finset.sum_congr rfl fun p _ => jumpPMF_eq_ofReal β v p,
      ← ENNReal.ofReal_sum_of_nonneg fun p _ => div_nonneg (jumpRate_pos β v p.1 p.2).le hq.le,
      Finset.sum_div]
  rw [hsum, ENNReal.ofReal_le_ofReal_iff (div_nonneg
    (Finset.sum_nonneg fun p _ => (jumpRate_pos β v p.1 p.2).le) hq.le), le_div_iff₀ hq] at h8
  have hrhs : ∑ p : Jump N M, (if p ∈ argmaxFinset v then zeta N M β ^ j else 0)
        * jumpRate β v p.1 p.2
      = zeta N M β ^ j * ∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2 := by
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ argmaxFinset v)]
    have h1 : Finset.univ.filter (· ∈ argmaxFinset v) = argmaxFinset v := by
      ext p; simp
    rw [h1]
    have h2 : ∑ p ∈ Finset.univ.filter (fun p => p ∉ argmaxFinset v),
        (if p ∈ argmaxFinset v then zeta N M β ^ j else 0) * jumpRate β v p.1 p.2 = 0 :=
      Finset.sum_eq_zero fun p hp => by
        rw [if_neg (Finset.mem_filter.1 hp).2, zero_mul]
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun p hp => by rw [if_pos hp]
  rw [hrhs, pow_succ]
  have hΛ := exitRate_nonneg N M β
  have hzj : 0 ≤ zeta N M β ^ j := pow_nonneg hζ.le j
  calc (totalRate β v - exitRate N M β) * (zeta N M β ^ j * zeta N M β)
      ≤ totalRate β v * (zeta N M β ^ j * zeta N M β) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = zeta N M β ^ j * (zeta N M β * totalRate β v) := by ring
    _ ≤ zeta N M β ^ j * ∑ p ∈ argmaxFinset v, jumpRate β v p.1 p.2 :=
        mul_le_mul_of_nonneg_left h8 hzj

end Rates

section Lemma14

variable [NeZero N] [NeZero M]

/-- **The comparison, by induction on the number of jumps.**  From a phase-`j` state the
consensus for another opinion is avoided before `min (t, T_n)` with probability at least
`ζ_β^j e^{-Λ t}`. -/
theorem le_ctsPathMeasure_avoidBefore (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (o : Opinion M) (n : ℕ) :
    ∀ (j : ℕ) (v : Pressure N M), ExitInv o v j → ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal (zeta N M β ^ j * Real.exp (-(exitRate N M β * t)))
        ≤ ctsPathMeasure β v (avoidBefore v (consensusSetOther N o) n t) := by
  have hζ0 := (zeta_pos N M β).le
  have hζ1 := zeta_le_one N M β
  have hΛ := exitRate_nonneg N M β
  induction n with
  | zero =>
      intro j v _ t ht
      rw [avoidBefore_zero, measure_univ]
      refine ENNReal.ofReal_le_one.2 (mul_le_one₀ (pow_le_one₀ hζ0 hζ1) (Real.exp_pos _).le ?_)
      exact Real.exp_le_one_iff.2 (by nlinarith)
  | succ n ih =>
      intro j v hv t ht
      have hnot := hv.notMem hM (by omega)
      cases j with
      | zero =>
          have hv' : IsSteepLadder o v := hv
          refine le_ctsPathMeasure_avoidBefore_of_score β hnot n ht hΛ (pow_le_one₀ hζ0 hζ1)
            (fun p => if v p.1 p.2 < 0 then 0 else if p.2 = o then 1 else zeta N M β ^ N)
            (fun p => by split_ifs <;> positivity) (rate_phase_zero hM hβ hv') ?_
          rintro ⟨a, p⟩ s hs
          by_cases hneg : v a p < 0
          · simp [hneg]
          · by_cases ho : p = o
            · subst ho
              have h := ih 0 (express a p v) (hv.express_self hM a) (t - s) (by linarith)
              simpa [hneg] using h
            · have h := ih N (express a p v) (hv.express_other hM hN ho (le_of_not_gt hneg))
                (t - s) (by linarith)
              simpa [hneg, ho] using h
      | succ j =>
          refine le_ctsPathMeasure_avoidBefore_of_score β hnot n ht hΛ (pow_le_one₀ hζ0 hζ1)
            (fun p => if p ∈ argmaxFinset v then zeta N M β ^ j else 0)
            (fun p => by split_ifs <;> positivity) (rate_phase_succ hM hβ v j) ?_
          rintro ⟨a, p⟩ s hs
          by_cases hg : (a, p) ∈ argmaxFinset v
          · have hgreedy : ∀ b q, v b q ≤ v a p := fun b q => by
              rw [mem_argmaxFinset.1 hg]; exact le_entrySup v b q
            have h := ih j (express a p v) (hv.express_greedy hM (by omega) hgreedy) (t - s)
              (by linarith)
            simpa [hg] using h
          · simp [hg]

/-- **Lemma 14.1.** From a ladder supporting `o`, the consensus for another opinion is not
reached before time `t` with probability at least `exp (-2 t N³ (M+1)³ e^{-β/(M-1)})`.

**Supplies a step the paper asserts, and takes a different route through one of them.**  The
mechanism, the rates and the constant are Appendix B's; the composition is a first-step
comparison with an exponential clock in place of the paper's conditioning on `τ₁⁻ᵒ`, which does
not compose as written.  See the module docstring. -/
theorem le_probHittingGT_consensusOther (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {l : Pressure N M} (hl : IsLadder o l) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (Real.exp
        (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))))
      ≤ probHittingGT β l (consensusSetOther N o) (ENNReal.ofReal t) := by
  have hinv : ExitInv o l 0 := exitInv_zero_of_isLadder hM hl
  have key := le_ctsPathMeasure_lt_hittingTimeCts β (hinv.notMem hM (by omega))
    fun n => le_ctsPathMeasure_avoidBefore hM hN hβ o n 0 l hinv t ht.le
  have heq : zeta N M β ^ 0 * Real.exp (-(exitRate N M β * t))
      = Real.exp (-2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ) * Real.exp (-β / ((M : ℝ) - 1))) := by
    rw [pow_zero, one_mul, exitRate]
    congr 1
    ring
  rw [← heq]
  exact key

/-- **Lemma 14.2.** From a consensus state for `o`, the consensus for another opinion is
reached before time `t` with probability at most `(N²M + 2 t N³ (M+1)³) e^{-β/(M-1)}`.

**Follows the paper's proof**, through part 1's comparison: from `C^o` the first `N`
expressions are a block, which returns to `L^o` with probability at least `ζ_β^N`, and the rest
is Remark 4 and `1 - e^{-x} ≤ x`. -/
theorem probHittingLE_consensusOther_le (hM : 2 ≤ M) (hN : 3 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {o : Opinion M} {u : Pressure N M} (hu : IsConsensus o u) {t : ℝ} (ht : 0 < t) :
    ctsPathMeasure β u {ω | hittingTimeCts u (consensusSetOther N o) ω ≤ ENNReal.ofReal t}
      ≤ ENNReal.ofReal ((((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
          Real.exp (-β / ((M : ℝ) - 1))) := by
  set θ := consensusSetOther N o
  have hinv : ExitInv o u N := exitInv_of_isConsensus hM (by omega) hu
  have key := le_ctsPathMeasure_lt_hittingTimeCts β (hinv.notMem hM (by omega))
    fun n => le_ctsPathMeasure_avoidBefore hM hN hβ o n N u hinv t ht.le
  have hcompl : {ω | hittingTimeCts u θ ω ≤ ENNReal.ofReal t}
      = {ω | ENNReal.ofReal t < hittingTimeCts u θ ω}ᶜ := by
    ext ω; simp [not_lt]
  have hmeas : MeasurableSet {ω | ENNReal.ofReal t < hittingTimeCts u θ ω} :=
    measurableSet_lt measurable_const (measurable_hittingTimeCts u θ)
  set z := zeta N M β ^ N with hz
  set E := Real.exp (-(exitRate N M β * t)) with hE
  have hz0 : 0 ≤ z := pow_nonneg (zeta_pos N M β).le N
  have hz1 : z ≤ 1 := pow_le_one₀ (zeta_pos N M β).le (zeta_le_one N M β)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [exitRate_nonneg N M β])
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  calc 1 - ctsPathMeasure β u {ω | ENNReal.ofReal t < hittingTimeCts u θ ω}
      ≤ 1 - ENNReal.ofReal (z * E) := tsub_le_tsub_left key 1
    _ = ENNReal.ofReal (1 - z * E) := by
        rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (mul_nonneg hz0 hE0)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        -- Remark 4 for the run to the ladder, and `1 - e^{-x} ≤ x` for the rest
        have hrem := one_sub_le_zeta_pow N M β N
        rw [← hz] at hrem
        have hexp := one_sub_exp_neg_le (exitRate N M β * t)
        rw [← hE] at hexp
        have hzE : z * (1 - E) ≤ 1 - E := mul_le_of_le_one_left (by linarith) hz1
        have hgoal : (N : ℝ) * ((M : ℝ) * (N : ℝ) * Real.exp (-(β / ((M : ℝ) - 1))))
            + exitRate N M β * t
            = (((N ^ 2 * M : ℕ) : ℝ) + 2 * t * ((N ^ 3 * (M + 1) ^ 3 : ℕ) : ℝ)) *
                Real.exp (-β / ((M : ℝ) - 1)) := by
          rw [exitRate, neg_div]
          push_cast
          ring
        nlinarith

end Lemma14

end SocialNetwork
