import project.Game

/-!
# Player 2 never wins (§1 of `main.tex`)

> **Player 2 never wins (any `n`).** The winning family is monotone, as a superset of a
> transversal contains a transversal, and the board is finite, so a strategy-stealing argument
> applies. Assume O has a winning strategy `Σ`. X could adopt `Σ` after an arbitrary first move,
> treating their extra stone as unplayed and playing an arbitrary cell when `Σ` names an
> occupied one. […] This yields a win for X, contradicting the fact that both cannot win.

`steal_aux` is the formal version of the simulation: `p` is the real position (X to move) and
`q` the *imagined* position, in which the real O plays the role of the first player and X's
simulated stones `q.O` are a subset of X's real stones; `c` is the real O-stone that has just
been played, which is the imagined first player's move. `hasTransversal_of_oCanWin_of_free`
covers the degenerate case in which the real board is already full: every cell still free in the
imagined game is then one of X's extra stones, so the imagined game can be finished without any
real move and X already owns a transversal.

Combined with `not_xCanWin_and_oCanWin` ("both cannot win"), this gives
`player_two_never_wins`: for every `n ≥ 1`, Player 2 has no winning strategy, so the value of
the game is always "X win" or "draw".
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- The winning family is monotone: a superset of a set containing a transversal contains a
transversal (§1 of `main.tex`). -/
theorem hasTransversal_mono {S T : Finset (Cell n)} (hST : S ⊆ T) (h : HasTransversal S) :
    HasTransversal T := by
  have h1 := nu_mono hST
  have h2 := nu_le T
  simp only [HasTransversal] at h ⊢
  omega

/-- If O can force a win from the imagined position `q` while every cell still free in `q`
already belongs to `A`, and `A` contains O's imagined stones, then `A` contains a transversal:
the imagined game can be played out entirely inside `A`. -/
theorem hasTransversal_of_oCanWin_of_free : ∀ (l : ℕ) (q : Position n) (A : Finset (Cell n)),
    OCanWin l q → q.O ⊆ A → (∀ z, z ∉ q.occupied → z ∈ A) → HasTransversal A := by
  intro l
  induction l with
  | zero => intro q A h hsub _; exact hasTransversal_mono hsub h
  | succ l ih =>
    intro q A h hsub hfree
    rcases h with hwin | ⟨⟨c, hc⟩, hall⟩
    · exact hasTransversal_mono hsub hwin
    obtain ⟨-, c', hc', hcase⟩ := hall c hc
    have hc'q : c' ∉ q.occupied := fun hmem =>
      hc' (Position.mem_occupied.2 (by
        rcases Position.mem_occupied.1 hmem with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr h))
    have hsub' : insert c' q.O ⊆ A := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz'
      · exact hfree _ hc'q
      · exact hsub hz'
    rcases hcase with hwin | hrec
    · exact hasTransversal_mono hsub' hwin
    refine ih ((q.playX c).playO c') A hrec hsub' ?_
    intro z hz
    refine hfree z ?_
    intro hmem
    refine hz (Position.mem_occupied.2 ?_)
    rcases Position.mem_occupied.1 hmem with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

/-- **Strategy stealing** (§1 of `main.tex`), the inductive step. `p` is the real position
with X to move, `q` the imagined position with the imagined first player (the real O) to move,
`c` is the real O-stone just played, `p.O = insert c q.X` says that the real O-stones are the
imagined first player's stones, and `q.O ⊆ p.X` says that X's simulated stones are among X's
real stones (the difference being X's extra, "unplayed", stones). If O can force a win in the
imagined game, then X can force a win in the real game. -/
theorem steal_aux : ∀ (l : ℕ) (p q : Position n) (c : Cell n),
    OCanWin l q → c ∉ q.occupied → p.O = insert c q.X → q.O ⊆ p.X →
    XCanWin (l + 1) p := by
  intro l
  induction l with
  | zero =>
    intro p q _ hq _ _ hsub
    exact xCanWin_of_hasTransversal (hasTransversal_mono hsub hq)
  | succ l ih =>
    intro p q c hq hc hpO hsub
    rcases hq with hwin | ⟨-, hall⟩
    · exact xCanWin_of_hasTransversal (hasTransversal_mono hsub hwin)
    obtain ⟨-, c', hc', hcase⟩ := hall c hc
    have hqX : (q.playX c).X = p.O := by rw [Position.playX_X, hpO]
    have hc'notO : c' ∉ p.O := by
      rw [← hqX]
      exact fun h => hc' (Position.mem_occupied.2 (Or.inl h))
    rcases hcase with hOwin | hnext
    · -- the imagined second player wins at once; its stones are X's (up to the cell `c'`)
      by_cases hc'X : c' ∈ p.X
      · refine xCanWin_of_hasTransversal (hasTransversal_mono ?_ hOwin)
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz'
        · exact hc'X
        · exact hsub hz'
      · refine xCanWin_one (c := c') ?_ (hasTransversal_mono ?_ hOwin)
        · rw [Position.mem_occupied]
          exact fun h => h.elim hc'X hc'notO
        · intro z hz
          rcases Finset.mem_insert.1 hz with rfl | hz'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hsub hz')
    -- X plays `c'`, or an arbitrary free cell if X already owns `c'`
    have key : (∃ a, a ∉ p.occupied ∧ insert c' q.O ⊆ insert a p.X) ∨ HasTransversal p.X := by
      by_cases hc'X : c' ∈ p.X
      · by_cases hfree : ∃ a, a ∉ p.occupied
        · obtain ⟨a, ha⟩ := hfree
          refine Or.inl ⟨a, ha, ?_⟩
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | hz'
          · exact Finset.mem_insert_of_mem hc'X
          · exact Finset.mem_insert_of_mem (hsub hz')
        · push_neg at hfree
          refine Or.inr (hasTransversal_of_oCanWin_of_free l ((q.playX c).playO c') p.X hnext
            ?_ ?_)
          · intro z hz
            rcases Finset.mem_insert.1 hz with rfl | hz'
            · exact hc'X
            · exact hsub hz'
          · intro z hz
            rcases Position.mem_occupied.1 (hfree z) with h | h
            · exact h
            · exact absurd (Position.mem_occupied.2
                (Or.inl (by rw [Position.playO_X, hqX]; exact h))) hz
      · refine Or.inl ⟨c', ?_, ?_⟩
        · rw [Position.mem_occupied]
          exact fun h => h.elim hc'X hc'notO
        · intro z hz
          rcases Finset.mem_insert.1 hz with rfl | hz'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hsub hz')
    rcases key with ⟨a, hafree, hsub'⟩ | hwin
    · by_cases hroom : ∃ z, z ∉ (p.playX a).occupied
      swap
      · -- the real board is full after X plays `a`: the imagined game can be finished inside
        -- X's own stones, so X already owns a transversal
        push_neg at hroom
        refine xCanWin_one hafree (hasTransversal_of_oCanWin_of_free l
          ((q.playX c).playO c') (insert a p.X) hnext hsub' ?_)
        intro z hz
        rcases Position.mem_occupied.1 (hroom z) with h | h
        · exact h
        · exact absurd (Position.mem_occupied.2
            (Or.inl (by rw [Position.playO_X, hqX]; exact h))) hz
      refine Or.inr ⟨a, hafree, ?_⟩
      cases l with
      | zero => exact Or.inl (hasTransversal_mono hsub' hnext)
      | succ l₀ =>
        have hnextO := hnext
        rcases hnext with hwin' | ⟨-, hall'⟩
        · exact Or.inl (hasTransversal_mono hsub' hwin')
        refine Or.inr ⟨hroom, ?_⟩
        intro c₂ hc₂
        have hc₂q : c₂ ∉ ((q.playX c).playO c').occupied := by
          intro hmem
          refine hc₂ (Position.mem_occupied.2 ?_)
          rcases Position.mem_occupied.1 hmem with h | h
          · rw [Position.playO_X, hqX] at h
            exact Or.inr h
          · exact Or.inl (hsub' h)
        refine ⟨?_, ?_⟩
        · have := (hall' c₂ hc₂q).1
          rw [Position.playX_X, Position.playO_X, hqX] at this
          exact this
        · exact ih ((p.playX a).playO c₂) ((q.playX c).playO c') c₂ hnextO hc₂q
            (by rw [Position.playO_O, Position.playX_O, Position.playO_X, hqX]) hsub'
    · exact xCanWin_of_hasTransversal hwin

/-- **Strategy stealing** (§1 of `main.tex`): if Player 2 could force a win on the `n × n`
board with `n ≥ 2`, then Player 1 could too, by adopting Player 2's strategy after an arbitrary
first move. -/
theorem xCanWin_of_oCanWin (hn : 2 ≤ n) {l : ℕ} (h : OCanWin l (⟨∅, ∅⟩ : Position n)) :
    XCanWin (l + 2) (⟨∅, ∅⟩ : Position n) := by
  have hpos : 0 < n := by omega
  have hone : (1 : ℕ) < n := by omega
  refine Or.inr ⟨(⟨0, hpos⟩, ⟨0, hpos⟩), by simp [Position.occupied],
    Or.inr ⟨⟨(⟨0, hpos⟩, ⟨1, hone⟩), ?_⟩, ?_⟩⟩
  · simp [Position.occupied, Position.playX, Prod.ext_iff, Fin.ext_iff]
  intro c hc
  refine ⟨?_, ?_⟩
  · have hcard : nu (insert c (∅ : Finset (Cell n))) ≤ 1 := by
      simpa using nu_le_card (insert c (∅ : Finset (Cell n)))
    simp only [Position.playO_O, Position.playX_O]
    intro hT
    simp only [HasTransversal] at hT
    omega
  · refine steal_aux l _ (⟨∅, ∅⟩ : Position n) c h (by simp [Position.occupied]) rfl ?_
    simp

/-- **Player 2 never wins** (§1 of `main.tex`): for every `n ≥ 2` Player 2 has no strategy
forcing a win, so the value of the game is "X win" or "draw". -/
theorem player_two_never_wins (hn : 2 ≤ n) (l : ℕ) : ¬ OCanWin l (⟨∅, ∅⟩ : Position n) := by
  intro h
  have hX : ¬ HasTransversal (∅ : Finset (Cell n)) := by
    rw [HasTransversal]
    have : nu (∅ : Finset (Cell n)) ≤ 0 := nu_le_card ∅
    omega
  exact not_xCanWin_and_oCanWin (l + 2) l (⟨∅, ∅⟩ : Position n) hX hX
    (xCanWin_of_oCanWin hn h) h

end Transversal
