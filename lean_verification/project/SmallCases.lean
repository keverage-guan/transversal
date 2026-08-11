import project.Convert
import project.Game

/-!
# The small cases `n = 1` and `n = 2` (§1 of `aristotle.tex`)

"For `n = 1` the first player wins with their first stone. For `n = 2` the two winning sets are
the diagonals `A = {(1,1),(2,2)}` and `B = {(1,2),(2,1)}`. O can draw with the strategy of
answering X's first stone with its partner in the same diagonal. That diagonal is then split
one–one, and the remaining two cells are exactly the other diagonal, which X and O take one
each. Neither owns a diagonal, so O's strategy prevents an X win."

The paper deduces "O cannot win" from the strategy-stealing remark; for `n = 2` we prove it
directly, by the mirror-image pairing strategy for X (X opens in a corner and then takes the
partner of O's reply). Together, `no_win_two_X` and `no_win_two_O` say that `n = 2` is a draw.
-/

namespace Transversal

open Finset

/-- **Theorem A** of `aristotle.tex`, case `n = 1`: the first player wins with their first
stone. -/
theorem win_one : XCanWin 1 (⟨∅, ∅⟩ : Position 1) := by
  refine xCanWin_one (c := (0, 0)) (by simp [Position.occupied]) ?_
  have hM : IsMatching (insert ((0, 0) : Cell 1) ∅) := by
    intro p hp q hq _
    simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hp hq
    rw [hp, hq]
  rw [HasTransversal, nu_of_isMatching hM]
  simp

/-- On the `2 × 2` board the two transversals are the two diagonals `A = {(1,1),(2,2)}` and
`B = {(1,2),(2,1)}` of §1 of `aristotle.tex`. -/
theorem hasTransversal_two_iff {S : Finset (Cell 2)} :
    HasTransversal S ↔
      ((((0 : Fin 2), (0 : Fin 2)) ∈ S ∧ ((1 : Fin 2), (1 : Fin 2)) ∈ S) ∨
        (((0 : Fin 2), (1 : Fin 2)) ∈ S ∧ ((1 : Fin 2), (0 : Fin 2)) ∈ S)) := by
  rw [hasTransversal_iff_exists_perm]
  constructor
  · rintro ⟨σ, hσ⟩
    have h0 := hσ 0
    have h1 := hσ 1
    have hc : σ 0 = 0 ∨ σ 0 = 1 := by omega
    rcases hc with hc | hc
    · have hc1 : σ 1 = 1 := by
        have : σ 1 ≠ σ 0 := fun h => by simpa using σ.injective h
        rw [hc] at this
        omega
      rw [hc] at h0
      rw [hc1] at h1
      exact Or.inl ⟨h0, h1⟩
    · have hc1 : σ 1 = 0 := by
        have : σ 1 ≠ σ 0 := fun h => by simpa using σ.injective h
        rw [hc] at this
        omega
      rw [hc] at h0
      rw [hc1] at h1
      exact Or.inr ⟨h0, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Equiv.refl _, by intro i; fin_cases i <;> simpa using ‹_›⟩
    · exact ⟨Equiv.swap 0 1, by
        intro i
        fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right, h1, h2]⟩

/-- On a full board a player who does not already own a transversal can no longer win. -/
theorem not_xCanWin_of_full {p : Position 2} (hfull : ∀ c : Cell 2, c ∈ p.occupied)
    (hX : ¬ HasTransversal p.X) : ∀ k, ¬ XCanWin k p := by
  intro k
  cases k with
  | zero => exact hX
  | succ k =>
    rintro (h1 | ⟨c, hc, -⟩)
    · exact hX h1
    · exact hc (hfull c)

/-- One step of O's defence: if X does not already own a transversal and O has a reply to every
X move after which X can never win, then X cannot win. -/
theorem not_xCanWin_step {p : Position 2} (hX : ¬ HasTransversal p.X)
    (h : ∀ c, c ∉ p.occupied → ¬ HasTransversal (insert c p.X) ∧
      ∃ c', c' ∉ (p.playX c).occupied ∧ ∀ k, ¬ XCanWin k ((p.playX c).playO c')) :
    ∀ k, ¬ XCanWin k p := by
  intro k
  cases k with
  | zero => exact hX
  | succ k =>
    rintro (h1 | ⟨c, hc, hcase⟩)
    · exact hX h1
    · rcases hcase with hwin | ⟨-, hall⟩
      · exact (h c hc).1 hwin
      · obtain ⟨c', hc', hk⟩ := (h c hc).2
        exact hk k (hall c' hc').2

theorem not_oCanWin_of_full {p : Position 2} (hfull : ∀ c : Cell 2, c ∈ p.occupied)
    (hO : ¬ HasTransversal p.O) : ∀ k, ¬ OCanWin k p := by
  intro k
  cases k with
  | zero => exact hO
  | succ k =>
    rintro (h1 | ⟨⟨c, hc⟩, -⟩)
    · exact hO h1
    · exact hc (hfull c)

/-- One step of X's defence: if O does not already own a transversal and X has a move after
which no O reply lets O win, then O cannot win. -/
theorem not_oCanWin_step {p : Position 2} (hO : ¬ HasTransversal p.O)
    (c : Cell 2) (hc : c ∉ p.occupied)
    (h : ∀ c', c' ∉ (p.playX c).occupied → ¬ HasTransversal (insert c' p.O) ∧
      ∀ k, ¬ OCanWin k ((p.playX c).playO c')) :
    ∀ k, ¬ OCanWin k p := by
  intro k
  cases k with
  | zero => exact hO
  | succ k =>
    rintro (h1 | ⟨-, h2⟩)
    · exact hO h1
    · obtain ⟨-, c', hc', hcase⟩ := h2 c hc
      rcases hcase with hwin | hrec
      · exact (h c' hc').1 hwin
      · exact (h c' hc').2 k hrec

/-- **Theorem A** of `aristotle.tex`, case `n = 2`, first half: Player 1 cannot force a win on
the `2 × 2` board. O answers X's first stone with its partner in the same diagonal; the
remaining two cells are the other diagonal, which the players take one each, so X never owns a
diagonal. -/
theorem no_win_two_X : ∀ k, ¬ XCanWin k (⟨∅, ∅⟩ : Position 2) := by
  refine not_xCanWin_step (by simp [hasTransversal_two_iff]) ?_
  intro c hc
  obtain ⟨i, j⟩ := c
  fin_cases i <;> fin_cases j
  · -- X opens at `(1,1)`; O answers at `(2,2)`
    refine ⟨by simp [hasTransversal_two_iff], (1, 1),
      by simp [Position.occupied, Position.playX], ?_⟩
    refine not_xCanWin_step (by simp [hasTransversal_two_iff]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff], (1, 0),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact ⟨by simp [hasTransversal_two_iff], (0, 1),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
  · -- X opens at `(1,2)`; O answers at `(2,1)`
    refine ⟨by simp [hasTransversal_two_iff], (1, 0),
      by simp [Position.occupied, Position.playX], ?_⟩
    refine not_xCanWin_step (by simp [hasTransversal_two_iff]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact ⟨by simp [hasTransversal_two_iff], (1, 1),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff], (0, 0),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
  · -- X opens at `(2,1)`; O answers at `(1,2)`
    refine ⟨by simp [hasTransversal_two_iff], (0, 1),
      by simp [Position.occupied, Position.playX], ?_⟩
    refine not_xCanWin_step (by simp [hasTransversal_two_iff]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact ⟨by simp [hasTransversal_two_iff], (1, 1),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff], (0, 0),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
  · -- X opens at `(2,2)`; O answers at `(1,1)`
    refine ⟨by simp [hasTransversal_two_iff], (0, 0),
      by simp [Position.occupied, Position.playX], ?_⟩
    refine not_xCanWin_step (by simp [hasTransversal_two_iff]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff], (1, 0),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact ⟨by simp [hasTransversal_two_iff], (0, 1),
        by simp [Position.occupied, Position.playX, Position.playO],
        not_xCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])

/-- **Theorem A** of `aristotle.tex`, case `n = 2`, second half: Player 2 cannot force a win on
the `2 × 2` board either (in the paper this is the strategy-stealing remark). Hence `n = 2` is a
draw. -/
theorem no_win_two_O : ∀ k, ¬ OCanWin k (⟨∅, ∅⟩ : Position 2) := by
  refine not_oCanWin_step (by simp [hasTransversal_two_iff]) (0, 0)
    (by simp [Position.occupied]) ?_
  intro c' hc'
  obtain ⟨i, j⟩ := c'
  fin_cases i <;> fin_cases j
  · exact absurd hc' (by simp [Position.occupied, Position.playX])
  · -- O answers `(1,2)`; X blocks at `(2,1)`
    refine ⟨by simp [hasTransversal_two_iff], ?_⟩
    refine not_oCanWin_step (by simp [hasTransversal_two_iff]) (1, 0)
      (by simp [Position.occupied, Position.playX, Position.playO]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff],
        not_oCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
  · -- O answers `(2,1)`; X blocks at `(1,2)`
    refine ⟨by simp [hasTransversal_two_iff], ?_⟩
    refine not_oCanWin_step (by simp [hasTransversal_two_iff]) (0, 1)
      (by simp [Position.occupied, Position.playX, Position.playO]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff],
        not_oCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
  · -- O answers `(2,2)`; X blocks at `(1,2)`
    refine ⟨by simp [hasTransversal_two_iff], ?_⟩
    refine not_oCanWin_step (by simp [hasTransversal_two_iff]) (0, 1)
      (by simp [Position.occupied, Position.playX, Position.playO]) ?_
    intro c hc
    obtain ⟨i, j⟩ := c
    fin_cases i <;> fin_cases j
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])
    · exact ⟨by simp [hasTransversal_two_iff],
        not_oCanWin_of_full (by decide) (by simp [hasTransversal_two_iff])⟩
    · exact absurd hc (by simp [Position.occupied, Position.playX, Position.playO])

end Transversal
