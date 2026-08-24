/-
Copyright (c) 2026 Felipe Penafiel, Kádmo Laxa. All rights reserved.
Released under the Apache 2.0 license.
-/
import SocialNetwork.Ladder
import SocialNetwork.Trajectory

/-!
# From consensus to a ladder

The last step of the proof of Proposition 7 in arXiv:2607.19651 reads, in full:

> To conclude, we consider that by definition, if `v ∈ C^o` and event `⋂_{j=1}^N ξⱼ^u`
> occurs, then `Ũ_N^{β,u} ∈ L^o`.

This file proves that step. It is the mechanism behind the paper's "fast consensus
formation": once the network agrees on which opinion dominates, `N` greedy expressions
sort the actors into the exact staircase of Definition 1.

The argument has three stages, all deterministic.

1. **Greedy expressions in a consensus state express the consensus opinion.** In `C^o` the
   columns other than `o` are non-positive while column `o` carries a strictly positive
   entry, so a maximising pair sits in column `o` (`opinion_eq_of_isMax`). Expressing `o`
   keeps the state in `C^o` (`IsConsensus.express`), so this propagates: every one of the
   first `N` expressions is an expression of `o` (`opinion_eq_of_greedy`).

2. **No actor expresses twice.** This is the argument of Proposition 5 again. An actor that
   expressed at step `j` has a row bounded by `k - j - 1` at step `k`, whereas an actor
   that has not expressed at all has heard `k` expressions of `o` and so carries at least
   `k` — and greediness makes the expressing actor the maximum, a contradiction
   (`actor_ne_actor_of_greedy`).

3. **The resulting configuration is the staircase.** Each actor therefore expresses exactly
   once, at some step `i`, after which it only listens to expressions of `o`; its row at
   time `N` is then exactly `N - 1 - i` on column `o` and `-(N - 1 - i)/(M - 1)` elsewhere
   (`state_add_of_hearing`). As `i` runs over all of `0, …, N - 1`, so does `N - 1 - i`,
   which is precisely Definition 1.

## Main results

* `SocialNetwork.state_add_of_hearing` — the row of an actor that only listens, while every
  expression is of the same opinion `o`.
* `SocialNetwork.isLadder_state` — `N` greedy expressions from a consensus state for `o`
  produce a ladder supporting `o`.
-/

namespace SocialNetwork

open Finset

variable {N M : ℕ}

/-- The row of an actor that does not express between steps `m` and `m + k`, while every
expression in that window is of opinion `o`: the `o`-entry gains `M - 1` per step (i.e. `1`
in the paper's coordinates) and every other entry loses `1` per step (i.e. `1/(M-1)`). -/
theorem state_add_of_hearing (T : Trajectory N M) (u : Pressure N M) (a : Actor N)
    {o : Opinion M} (m k : ℕ)
    (hne : ∀ i, m ≤ i → i < m + k → T.actor i ≠ a)
    (ho : ∀ i, m ≤ i → i < m + k → T.opinion i = o) :
    T.state u (m + k) a o = T.state u m a o + (k : ℤ) * ((M : ℤ) - 1) ∧
      ∀ p, p ≠ o → T.state u (m + k) a p = T.state u m a p - (k : ℤ) := by
  induction k with
  | zero => exact ⟨by simp, fun p _ => by simp⟩
  | succ k ih =>
      obtain ⟨ihO, ihP⟩ :=
        ih (fun i h1 h2 => hne i h1 (by omega)) (fun i h1 h2 => ho i h1 (by omega))
      have hactor : T.actor (m + k) ≠ a := hne (m + k) (by omega) (by omega)
      have hopin : T.opinion (m + k) = o := ho (m + k) (by omega) (by omega)
      have hidx : m + (k + 1) = m + k + 1 := by omega
      refine ⟨?_, fun p hp => ?_⟩
      · rw [hidx, T.state_succ, hopin, express_of_ne_of_eq hactor.symm, ihO]
        push_cast; ring
      · rw [hidx, T.state_succ, hopin, express_of_ne_of_ne hactor.symm hp, ihP p hp]
        push_cast; ring

section ConsensusToLadder

variable (T : Trajectory N M) {o : Opinion M} {v : Pressure N M}

/-- In a consensus state for `o`, every maximising entry lies in column `o`. -/
theorem opinion_eq_of_isMax (hv : IsConsensus o v) {b : Actor N} {p : Opinion M}
    (hmax : ∀ a q, v a q ≤ v b p) : p = o := by
  obtain ⟨a, ha⟩ := hv.exists_pos
  by_contra hp
  have h1 := hv.nonpos b p hp
  have h2 := hmax a o
  omega

/-- Consensus is preserved along a greedy trajectory. -/
theorem isConsensus_state (hM : 2 ≤ M) (hN : 2 ≤ N) (hv : IsConsensus o v)
    (hg : ∀ k, k < N → IsGreedyAt T v k) :
    ∀ k, k ≤ N → IsConsensus o (T.state v k) := by
  intro k
  induction k with
  | zero => intro _; rw [T.state_zero]; exact hv
  | succ k ih =>
      intro hk
      have hck := ih (by omega)
      have hop : T.opinion k = o := opinion_eq_of_isMax hck (hg k (by omega))
      rw [T.state_succ, hop]
      exact hck.express hM hN _

/-- Every one of the first `N` greedy expressions expresses the consensus opinion. -/
theorem opinion_eq_of_greedy (hM : 2 ≤ M) (hN : 2 ≤ N) (hv : IsConsensus o v)
    (hg : ∀ k, k < N → IsGreedyAt T v k) {k : ℕ} (hk : k < N) : T.opinion k = o :=
  opinion_eq_of_isMax (isConsensus_state T hM hN hv hg k (le_of_lt hk)) (hg k hk)

/-- No actor expresses twice among the first `N` greedy expressions from a consensus state.

This is the argument of Proposition 5: an actor that already expressed carries too little
pressure to be the maximum, because some actor has not expressed at all and has been
accumulating pressure for the consensus opinion the whole time. -/
theorem actor_ne_actor_of_greedy (hM : 2 ≤ M) (hN : 2 ≤ N) (hv : IsConsensus o v)
    (hg : ∀ k, k < N → IsGreedyAt T v k) {j k : ℕ} (hjk : j < k) (hk : k < N) :
    T.actor j ≠ T.actor k := by
  intro hEq
  have hMpos : (0 : ℤ) < (M : ℤ) - 1 := one_lt_of_two_le hM
  have hop : ∀ l, l < N → T.opinion l = o := fun l hl =>
    opinion_eq_of_greedy T hM hN hv hg hl
  -- an actor that has not expressed before step `k`
  obtain ⟨b, hb⟩ : ∃ b : Actor N, ∀ i, i < k → T.actor i ≠ b := by
    have hex : ∃ b : Actor N, b ∉ (Finset.range k).image fun i => T.actor i := by
      by_contra hno
      have hsub : (Finset.univ : Finset (Actor N))
          ⊆ (Finset.range k).image fun i => T.actor i := by
        intro c _
        by_contra hc
        exact hno ⟨c, hc⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := Finset.range k) (f := fun i => T.actor i)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      rw [Finset.card_range] at h2
      omega
    obtain ⟨b, hbmem⟩ := hex
    exact ⟨b, fun i hi hEq' => hbmem (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, hEq'⟩)⟩
  -- `b` has heard `k` expressions of `o`, so its pressure for `o` is at least `k`
  obtain ⟨hb1, -⟩ := state_add_of_hearing T v b 0 k
    (fun i _ h2 => hb i (by omega)) (fun i _ h2 => hop i (by omega))
  rw [Nat.zero_add, T.state_zero] at hb1
  have hbge : (k : ℤ) * ((M : ℤ) - 1) ≤ T.state v k b o := by
    rw [hb1]
    have := hv.nonneg b
    linarith
  -- the actor expressing at step `k` expressed already at step `j`, so its row is small
  have hzero : rowSup (T.state v (j + 1)) (T.actor j) = 0 :=
    rowSup_eq_zero_iff.2 fun q => T.state_succ_actor v j q
  have hsmall := entry_le_of_state T hM (T.actor j) (j + 1) hzero (k - j - 1) o
  rw [show j + 1 + (k - j - 1) = k from by omega, hEq] at hsmall
  -- greediness at step `k` puts these in contradiction
  have hgk := hg k hk b o
  rw [hop k hk] at hgk
  have hcast : ((k - j - 1 : ℕ) : ℤ) < (k : ℤ) := by
    have : (k - j - 1 : ℕ) < k := by omega
    exact_mod_cast this
  have hmul := mul_lt_mul_of_pos_right hcast hMpos
  linarith

/-- **The last step of Proposition 7.** Starting from a consensus state for `o`, `N` greedy
expressions land the process exactly on a ladder supporting `o`. -/
theorem isLadder_state (hM : 2 ≤ M) (hN : 2 ≤ N) (hv : IsConsensus o v)
    (hg : ∀ k, k < N → IsGreedyAt T v k) : IsLadder o (T.state v N) := by
  have hop : ∀ l, l < N → T.opinion l = o := fun l hl =>
    opinion_eq_of_greedy T hM hN hv hg hl
  have hdist : ∀ j k, j < k → k < N → T.actor j ≠ T.actor k := fun _ _ hjk hk =>
    actor_ne_actor_of_greedy T hM hN hv hg hjk hk
  have hfinj : Function.Injective fun i : Fin N => T.actor (i : ℕ) := by
    intro i j hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact absurd hij (hdist _ _ h j.isLt)
    · exact Fin.val_injective h
    · exact absurd hij.symm (hdist _ _ h i.isLt)
  -- the row of the actor that expressed at step `i`, read at time `N`
  have hval : ∀ i : Fin N,
      T.state v N (T.actor (i : ℕ)) o = ((N - 1 - (i : ℕ) : ℕ) : ℤ) * ((M : ℤ) - 1) ∧
        ∀ p, p ≠ o →
          T.state v N (T.actor (i : ℕ)) p = -((N - 1 - (i : ℕ) : ℕ) : ℤ) := by
    intro i
    have hiN := i.isLt
    have hzero : ∀ p, T.state v ((i : ℕ) + 1) (T.actor (i : ℕ)) p = 0 :=
      fun p => T.state_succ_actor v _ p
    have hidx : (i : ℕ) + 1 + (N - 1 - (i : ℕ)) = N := by omega
    obtain ⟨h1, h2⟩ := state_add_of_hearing T v (T.actor (i : ℕ)) ((i : ℕ) + 1)
      (N - 1 - (i : ℕ))
      (fun l hl1 hl2 => (hdist (i : ℕ) l (by omega) (by omega)).symm)
      (fun l hl1 hl2 => hop l (by omega))
    rw [hidx] at h1 h2
    refine ⟨by rw [h1, hzero o]; ring, fun p hp => by rw [h2 p hp, hzero p]; ring⟩
  have hsurj : ∀ a : Actor N, ∃ i : Fin N, T.actor (i : ℕ) = a := fun a =>
    Finite.surjective_of_injective hfinj a
  refine ⟨T.isState_state hv.isState N, ?_, ?_⟩
  · -- the `o`-column takes exactly the `N` ladder values
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_ladderValues_iff]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨i, hi⟩ := hsurj a
      obtain ⟨h1, -⟩ := hval i
      have hiN := i.isLt
      refine ⟨⟨N - 1 - (i : ℕ), by omega⟩, ?_⟩
      rw [← ha, ← hi, h1, mul_comm]
    · rintro ⟨j, hj⟩
      have hjN := j.isLt
      have hlt : N - 1 - (j : ℕ) < N := by omega
      obtain ⟨h1, -⟩ := hval ⟨N - 1 - (j : ℕ), hlt⟩
      simp only at h1
      have hback : (N - 1 - (N - 1 - (j : ℕ)) : ℕ) = (j : ℕ) := by omega
      refine ⟨T.actor (N - 1 - (j : ℕ)), ?_⟩
      rw [h1, hback, hj]
      ring
  · -- the other columns are the corresponding negative multiples
    intro a p hp
    obtain ⟨i, hi⟩ := hsurj a
    obtain ⟨h1, h2⟩ := hval i
    rw [← hi, h1, h2 p hp]
    ring

end ConsensusToLadder

end SocialNetwork
