import project.Convert
import project.Game
import project.Stealing

/-!
# The `3 × 3` game is a draw (§2 of `main.tex`)

> "The `3 × 3` game is likewise a draw, proved by hand in [Ranđelović]."

The paper quotes this case from the literature. Here it is settled by an exhaustive search
carried out inside Lean and checked by the kernel: `oSafeL` is a Boolean backward induction on
positions of the `3 × 3` board (the two players' stones being given as lists of cells) which
certifies "with X to move, X cannot force a win", and `not_xCanWin_of_oSafeL` shows that such a
certificate really does refute `XCanWin k p` for every `k`. Evaluating `oSafeL 5 [] []` gives
`no_win_three_X`, and `no_win_three_O` follows from the strategy-stealing theorem
`player_two_never_wins` of §2. Together they say that the `3 × 3` game is a draw.
-/

namespace Transversal

open Finset

/-- The six permutations of `Fin 3`, as functions; the transversals of the `3 × 3` board are
exactly the graphs of these (§2 of `main.tex`, "The board as `K_{n,n}`"). -/
def perms3 : List (Fin 3 → Fin 3) :=
  [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

theorem perms3_bijective : ∀ g ∈ perms3, Function.Bijective g := by decide

theorem mem_perms3_of_bijective {g : Fin 3 → Fin 3} (hg : Function.Bijective g) : g ∈ perms3 := by
  revert hg
  revert g
  decide

/-- A decidable test for "the cells in the list `l` contain a transversal" on the `3 × 3`
board: by `hasTransversal_iff_exists_perm` this amounts to containing the graph of a
permutation of `Fin 3`. -/
def hasT3 (l : List (Cell 3)) : Bool :=
  perms3.any (fun g => (List.finRange 3).all (fun i => decide ((i, g i) ∈ l)))

theorem hasT3_iff {l : List (Cell 3)} : hasT3 l = true ↔ HasTransversal l.toFinset := by
  rw [hasTransversal_iff_exists_perm]
  constructor
  · intro h
    obtain ⟨g, hg, hall⟩ := List.any_eq_true.1 h
    refine ⟨Equiv.ofBijective g (perms3_bijective g hg), ?_⟩
    intro i
    have := (List.all_eq_true.1 hall) i (List.mem_finRange i)
    simpa using of_decide_eq_true this
  · rintro ⟨σ, hσ⟩
    refine List.any_eq_true.2 ⟨σ, mem_perms3_of_bijective σ.bijective, List.all_eq_true.2 ?_⟩
    intro i _
    simpa using List.mem_toFinset.1 (hσ i)

/-- The nine cells of the `3 × 3` board, as a list. -/
def allCells3 : List (Cell 3) :=
  (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => (i, j)

theorem mem_allCells3 (c : Cell 3) : c ∈ allCells3 := by
  revert c
  decide

/-- The free (unoccupied) cells of the position in which X owns `xs` and O owns `os`. -/
def freeL (xs os : List (Cell 3)) : List (Cell 3) :=
  allCells3.filter (fun c => !(decide (c ∈ xs) || decide (c ∈ os)))

theorem mem_freeL {xs os : List (Cell 3)} {c : Cell 3} :
    c ∈ freeL xs os ↔ c ∉ xs ∧ c ∉ os := by
  simp [freeL, List.mem_filter, mem_allCells3 c]

/-- The Boolean backward induction on the `3 × 3` board: `oSafeL f xs os = true` certifies
that, with X (owning `xs`) to move against O (owning `os`), X cannot force a win within `f`
further rounds of the recursion — for every move `c` of X, X's set stays short of a transversal
and either the board is full or O has a reply that wins for O outright or is again certified. -/
def oSafeL : ℕ → List (Cell 3) → List (Cell 3) → Bool
  | 0, _, _ => false
  | (f + 1), xs, os =>
      !hasT3 xs &&
        (freeL xs os).all (fun c =>
          !hasT3 (c :: xs) &&
            ((freeL (c :: xs) os).isEmpty ||
              (freeL (c :: xs) os).any (fun c' =>
                hasT3 (c' :: os) || oSafeL f (c :: xs) (c' :: os))))

/-- Soundness of the search: a position certified by `oSafeL` is one from which X cannot force
a win, whatever number of stones X is allowed. -/
theorem not_xCanWin_of_oSafeL :
    ∀ (f : ℕ) (xs os : List (Cell 3)) (p : Position 3), p.X = xs.toFinset → p.O = os.toFinset →
      oSafeL f xs os = true → ∀ k, ¬ XCanWin k p := by
  intro f
  induction f with
  | zero => intro xs os p _ _ h; simp [oSafeL] at h
  | succ f ih =>
    intro xs os p hX hO h k
    rw [oSafeL, Bool.and_eq_true] at h
    obtain ⟨hXb, hall⟩ := h
    have hXnot : ¬ HasTransversal p.X := by
      rw [hX]
      intro hT
      simp [hasT3_iff.2 hT] at hXb
    cases k with
    | zero => exact hXnot
    | succ k =>
      rintro (h1 | ⟨c, hc, hcase⟩)
      · exact hXnot h1
      -- `c` is a free cell of the board
      have hcfree : c ∈ freeL xs os := by
        refine mem_freeL.2 ⟨fun hmem => hc ?_, fun hmem => hc ?_⟩
        · exact Position.mem_occupied.2 (Or.inl (by rw [hX]; exact List.mem_toFinset.2 hmem))
        · exact Position.mem_occupied.2 (Or.inr (by rw [hO]; exact List.mem_toFinset.2 hmem))
      have hstep := (List.all_eq_true.1 hall) c hcfree
      rw [Bool.and_eq_true] at hstep
      obtain ⟨hnotwin, hrest⟩ := hstep
      have hXc : (p.playX c).X = (c :: xs).toFinset := by
        rw [Position.playX_X, hX, List.toFinset_cons]
      have hOc : (p.playX c).O = os.toFinset := by rw [Position.playX_O, hO]
      have hnotwin' : ¬ HasTransversal (p.playX c).X := by
        rw [hXc]
        intro hT
        simp [hasT3_iff.2 hT] at hnotwin
      rcases hcase with hwin | ⟨hex, hforall⟩
      · exact hnotwin' hwin
      -- since a free cell remains, O does have a reply
      obtain ⟨z, hz⟩ := hex
      have hzmem : z ∈ freeL (c :: xs) os := by
        refine mem_freeL.2 ⟨fun hmem => hz ?_, fun hmem => hz ?_⟩
        · exact Position.mem_occupied.2 (Or.inl (by rw [hXc]; exact List.mem_toFinset.2 hmem))
        · exact Position.mem_occupied.2 (Or.inr (by rw [hOc]; exact List.mem_toFinset.2 hmem))
      have hne : (freeL (c :: xs) os).isEmpty = false := by
        cases hl : freeL (c :: xs) os with
        | nil => rw [hl] at hzmem; simp at hzmem
        | cons a t => simp
      rw [hne, Bool.false_or] at hrest
      obtain ⟨c', hc'mem, hc'prop⟩ := List.any_eq_true.1 hrest
      obtain ⟨hc'X, hc'O⟩ := mem_freeL.1 hc'mem
      have hfree' : c' ∉ (p.playX c).occupied := by
        intro hmem
        rcases Position.mem_occupied.1 hmem with h' | h'
        · rw [hXc] at h'; exact hc'X (List.mem_toFinset.1 h')
        · rw [hOc] at h'; exact hc'O (List.mem_toFinset.1 h')
      obtain ⟨hOnot, hrec⟩ := hforall c' hfree'
      have hO' : ((p.playX c).playO c').O = (c' :: os).toFinset := by
        rw [Position.playO_O, hOc, List.toFinset_cons]
      rcases Bool.or_eq_true_iff.1 hc'prop with hOwin | hsafe
      · exact hOnot (hO' ▸ hasT3_iff.1 hOwin)
      · exact ih (c :: xs) (c' :: os) ((p.playX c).playO c') (by rw [Position.playO_X, hXc])
          hO' hsafe k hrec

/-- The exhaustive search: on the empty `3 × 3` board, X cannot force a win. -/
theorem oSafeL_empty_three : oSafeL 5 [] [] = true := by decide

/-- **The `3 × 3` game is a draw** (§2 of `main.tex`), first half: Player 1 cannot force a
win on the `3 × 3` board. -/
theorem no_win_three_X : ∀ k, ¬ XCanWin k (⟨∅, ∅⟩ : Position 3) :=
  not_xCanWin_of_oSafeL 5 [] [] _ rfl rfl oSafeL_empty_three

/-- **The `3 × 3` game is a draw** (§2 of `main.tex`), second half: Player 2 cannot force a
win either. This is the strategy-stealing remark of §2, i.e. `player_two_never_wins`. -/
theorem no_win_three_O : ∀ k, ¬ OCanWin k (⟨∅, ∅⟩ : Position 3) :=
  fun k => player_two_never_wins (by norm_num) k

end Transversal
