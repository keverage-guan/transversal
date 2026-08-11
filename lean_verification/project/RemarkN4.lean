import project.Convert
import project.Game

/-!
# The `n = 4` remark of §4 of `aristotle.tex`

> **Remark (why a stronger statement is false).** Take `n = 4`, X `= {(1,1),(2,2),(3,3)}` and
> `F = {(1,2),(2,1)}` at ply `5 = 2n-3` […]. Plan (i) with `s = u_a = 3`, `r = 1` gives the line
> O(4,4), X(4,1), O(1,4), X(3,4), O(1,3), X(4,3) and X wins at ply `11 = 2n+3`. But after O's
> last block, their set `{(1,2),(2,1),(4,4),(1,4),(1,3)}` […] O *does* threaten the free cell
> `(3,2)` at ply `2n+3` — harmlessly, because X completes first.

Rows and columns are numbered `0, …, 3` here, so the paper's cell `(i,j)` is `(i-1, j-1)`.
-/

namespace Transversal

open Finset

/-- **The remark after Lemma 4.7** of `aristotle.tex`: in the stated `n = 4` line, after O's
block at ply `2n+2 = 10` O threatens the free cell `(3,2)` of the paper — so no claim about O's
threats after ply `2n+2` can be made — and this is harmless because X completes a transversal
first, at ply `2n+3 = 11`, by playing the paper's cell `(4,3)`. -/
theorem remark_threat_after_last_block :
    Threatens
      (({(0, 0), (1, 1), (2, 2), (3, 0), (2, 3)} : Finset (Cell 4)) ∪
        ({(0, 1), (1, 0), (3, 3), (0, 3), (0, 2)} : Finset (Cell 4)))
      ({(0, 1), (1, 0), (3, 3), (0, 3), (0, 2)} : Finset (Cell 4)) (2, 1) ∧
    ((3, 2) : Cell 4) ∉
      (({(0, 0), (1, 1), (2, 2), (3, 0), (2, 3)} : Finset (Cell 4)) ∪
        ({(0, 1), (1, 0), (3, 3), (0, 3), (0, 2)} : Finset (Cell 4))) ∧
    HasTransversal (insert ((3, 2) : Cell 4) {(0, 0), (1, 1), (2, 2), (3, 0), (2, 3)}) := by
  refine ⟨⟨by decide, ?_⟩, by decide, ?_⟩
  · -- O's set together with `(3,2)` contains the transversal `(0,2),(1,0),(2,1),(3,3)`
    show HasTransversal (insert ((2, 1) : Cell 4) {(0, 1), (1, 0), (3, 3), (0, 3), (0, 2)})
    rw [hasTransversal_iff_exists_perm]
    refine ⟨⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩, ?_⟩
    decide
  · -- X's set together with `(3,2)` contains the transversal `(0,0),(1,1),(2,3),(3,2)`
    rw [hasTransversal_iff_exists_perm]
    refine ⟨⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩, ?_⟩
    decide

end Transversal
