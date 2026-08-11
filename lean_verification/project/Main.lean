import project.TheoremA
import project.SmallCases
import project.ThreeByThree
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


/-!
# Theorem A of `aristotle.tex`

> **Theorem A.** Player 1 wins for `n = 1` and for every `n ≥ 4`; `n = 2` is a draw.

This file states Theorem A in the form proved in the rest of the development:

* `n = 1`: `XCanWin 1 ⟨∅, ∅⟩` — X wins with their first stone (§1 of `aristotle.tex`);
* `n ≥ 4`: `XCanWin (n + 2) ⟨∅, ∅⟩` — X wins with their `(n+2)`-nd stone, i.e. by ply `2n+3`,
  which is the strategy of §3 and the proof of §4;
* `n = 2`: neither player can force a win, i.e. the game is a draw (§1).

The strategy-stealing remark of §1 ("Player 2 never wins", for every `n`) is
`Transversal.player_two_never_wins`; its ingredient that both players cannot force a win is
`Transversal.not_xCanWin_and_oCanWin`. For `n = 2`, the case Theorem A needs, the conclusion is
also proved directly by a pairing strategy for X in `Transversal.no_win_two_O`.

The remaining case `n = 3` of §1, which the paper quotes from Ranđelović, is proved here by an
exhaustive kernel-checked search: `Transversal.three_is_a_draw`.

One statement of `aristotle.tex` is not formalised here: the exhaustive computer search showing
that the bound `2n+3` is optimal for `n = 4, 5, 6` (the section of the paper it refers to is not
part of the source file).
-/

namespace Transversal

/-- **Theorem A** of `aristotle.tex`: "Player 1 wins for `n = 1` and for every `n ≥ 4`;
`n = 2` is a draw."

The three conjuncts are, in order: X wins the `1 × 1` game with their first stone; for every
`n ≥ 4`, X wins the `n × n` game with their `(n+2)`-nd stone (ply `2n+3`); and on the `2 × 2`
board neither X nor O has a strategy forcing a win, i.e. the game is a draw. -/
theorem theoremA :
    XCanWin 1 (⟨∅, ∅⟩ : Position 1) ∧
      (∀ n : ℕ, 4 ≤ n → XCanWin (n + 2) (⟨∅, ∅⟩ : Position n)) ∧
      (∀ k, ¬ XCanWin k (⟨∅, ∅⟩ : Position 2)) ∧
      (∀ k, ¬ OCanWin k (⟨∅, ∅⟩ : Position 2)) :=
  ⟨win_one, fun _ hn => theoremA_ge_four hn, no_win_two_X, no_win_two_O⟩

/-- The `3 × 3` case of §1 of `aristotle.tex` ("The `3 × 3` game is likewise a draw"): on the
`3 × 3` board neither player can force a win. -/
theorem three_is_a_draw :
    (∀ k, ¬ XCanWin k (⟨∅, ∅⟩ : Position 3)) ∧ (∀ k, ¬ OCanWin k (⟨∅, ∅⟩ : Position 3)) :=
  ⟨no_win_three_X, no_win_three_O⟩

end Transversal
