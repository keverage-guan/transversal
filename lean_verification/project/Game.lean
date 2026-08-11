import project.Basic

/-!
# The transversal achievement game (§1 of `aristotle.tex`)

Two players alternately claim unoccupied cells of the `n × n` grid; Player 1 (X) moves first.
A player wins upon owning a transversal, i.e. `n` cells no two of which share a row or a column.
X's `k`-th stone is placed at ply `2k-1` and O's `k`-th stone at ply `2k`.

A **position** records the two players' sets of stones. `XCanWin k p` is the usual
backward-induction description of "X, to move at `p`, has a strategy that completes a transversal
using at most `k` further stones, O never completing one first". Since X's `k`-th stone is placed
at ply `2k - 1`, `XCanWin (n+2) ⟨∅, ∅⟩` says exactly that X wins no later than ply `2n+3`, i.e.
with their `(n+2)`-nd stone.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- A position of the game: the sets of cells owned by X and by O. -/
structure Position (n : ℕ) where
  /-- The cells owned by Player 1 (X). -/
  X : Finset (Cell n)
  /-- The cells owned by Player 2 (O). -/
  O : Finset (Cell n)

namespace Position

/-- The occupied cells of a position. -/
def occupied (p : Position n) : Finset (Cell n) := p.X ∪ p.O

/-- The position obtained when X claims the cell `c`. -/
def playX (p : Position n) (c : Cell n) : Position n := ⟨insert c p.X, p.O⟩

/-- The position obtained when O claims the cell `c`. -/
def playO (p : Position n) (c : Cell n) : Position n := ⟨p.X, insert c p.O⟩

@[simp] theorem playX_X (p : Position n) (c : Cell n) : (p.playX c).X = insert c p.X := rfl
@[simp] theorem playX_O (p : Position n) (c : Cell n) : (p.playX c).O = p.O := rfl
@[simp] theorem playO_X (p : Position n) (c : Cell n) : (p.playO c).X = p.X := rfl
@[simp] theorem playO_O (p : Position n) (c : Cell n) : (p.playO c).O = insert c p.O := rfl

theorem mem_occupied {p : Position n} {c : Cell n} :
    c ∈ p.occupied ↔ c ∈ p.X ∨ c ∈ p.O := Finset.mem_union

end Position

/-- `XCanWin k p`: with X to move at the position `p`, X can complete a transversal using at
most `k` further stones, while O never completes a transversal first. This is the standard
backward-induction reading of "X has a winning strategy, winning within `k` moves".

As in `OCanWin`, the clause `∃ c', c' ∉ (p.playX c).occupied` records that the game only
continues while a free cell remains: without it, a move of X filling the board would count as
a win for X, because the condition on O's replies would hold vacuously. -/
def XCanWin : ℕ → Position n → Prop
  | 0, p => HasTransversal p.X
  | (k + 1), p =>
      HasTransversal p.X ∨
        ∃ c, c ∉ p.occupied ∧
          (HasTransversal (p.playX c).X ∨
            ((∃ c', c' ∉ (p.playX c).occupied) ∧
              ∀ c', c' ∉ (p.playX c).occupied →
                ¬ HasTransversal ((p.playX c).playO c').O ∧ XCanWin k ((p.playX c).playO c')))

/-- `OCanWin k p`: with X to move at the position `p`, O (Player 2) can force completing a
transversal using at most `k` further stones of their own, while X never completes one first.
This is the mirror image of `XCanWin`, used to state that a position is a draw; the clause
`∃ c, c ∉ p.occupied` records that O can only win by actually placing a further stone, so that
a full board with `¬ HasTransversal p.O` is not counted as a win for O. -/
def OCanWin : ℕ → Position n → Prop
  | 0, p => HasTransversal p.O
  | (k + 1), p =>
      HasTransversal p.O ∨
        ((∃ c, c ∉ p.occupied) ∧
          ∀ c, c ∉ p.occupied →
            ¬ HasTransversal (p.playX c).X ∧
              ∃ c', c' ∉ (p.playX c).occupied ∧
                (HasTransversal ((p.playX c).playO c').O ∨ OCanWin k ((p.playX c).playO c')))

theorem xCanWin_of_hasTransversal {k : ℕ} {p : Position n} (h : HasTransversal p.X) :
    XCanWin k p := by
  cases k with
  | zero => exact h
  | succ k => exact Or.inl h

/-- X can win in one move by playing a free cell that completes their set. -/
theorem xCanWin_one {k : ℕ} {p : Position n} {c : Cell n} (hc : c ∉ p.occupied)
    (h : HasTransversal (insert c p.X)) : XCanWin (k + 1) p :=
  Or.inr ⟨c, hc, Or.inl h⟩

/-- Having more moves available cannot hurt. -/
theorem XCanWin.mono {k : ℕ} {p : Position n} (h : XCanWin k p) : XCanWin (k + 1) p := by
  induction k generalizing p with
  | zero => exact Or.inl h
  | succ k ih =>
    rcases h with h | ⟨c, hc, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨c, hc, ?_⟩
      rcases h with h | ⟨hne, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hne, fun c' hc' => ⟨(h c' hc').1, ih (h c' hc').2⟩⟩

theorem XCanWin.mono_le {k l : ℕ} {p : Position n} (h : XCanWin k p) (hkl : k ≤ l) :
    XCanWin l p := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih.mono

/-- "Both cannot win": the fact invoked by the strategy-stealing remark of §1 of
`aristotle.tex`. From a position in which neither player already owns a transversal, the two
players cannot both have a strategy forcing a win. -/
theorem not_xCanWin_and_oCanWin : ∀ (k l : ℕ) (p : Position n), ¬ HasTransversal p.X →
    ¬ HasTransversal p.O → XCanWin k p → OCanWin l p → False := by
  intro k
  induction k with
  | zero => intro l p hX _ hx _; exact hX hx
  | succ k ih =>
    intro l p hX hO hx ho
    cases l with
    | zero => exact hO ho
    | succ l =>
      rcases hx with h | ⟨c, hc, hcase⟩
      · exact hX h
      rcases ho with h | ⟨-, hall⟩
      · exact hO h
      obtain ⟨hXc, c', hc', hcase'⟩ := hall c hc
      rcases hcase with hwin | ⟨-, hnext⟩
      · exact hXc hwin
      obtain ⟨hOc', hrec⟩ := hnext c' hc'
      rcases hcase' with hwin' | hrec'
      · exact hOc' hwin'
      exact ih l ((p.playX c).playO c') hXc hOc' hrec hrec'

end Transversal
