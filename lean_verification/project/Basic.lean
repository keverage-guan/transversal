import Mathlib

/-!
# The transversal achievement game: basic notions

This file formalises the basic vocabulary of §1 ("Preliminaries and Main Result") of
`aristotle.tex`, *The transversal achievement game on a square grid*:

* the board of an `n × n` grid, identified with the edge set of `K_{n,n}` (a cell `(r,c)`
  is the edge joining row `r` to column `c`);
* matchings of cells (no two cells share a row or a column);
* the matching number `ν(S)` of a set `S` of cells;
* transversals (`ν(S) = n`), *completing* cells and *threats*;
* the sets `D_R`, `D_C` of rows / columns exposed by some maximum matching.

It also proves the elementary properties of `ν` used throughout the paper, in particular
inequalities (4.1) (`ν(S) ≤ ν(S \ L) + 1` for a line `L`) and (4.2) (`ν(S ∪ T) ≤ ν(S) + |T|`)
from the proof of Lemma 4.7 ("no defensive deviation").
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- A **cell** of the `n × n` board, i.e. a pair `(r, c)` consisting of a row and a column.
Following §1 of `aristotle.tex` ("The board as `K_{n,n}`") a cell is identified with the edge
of the complete bipartite graph `K_{n,n}` joining the row vertex `r` to the column vertex `c`. -/
abbrev Cell (n : ℕ) : Type := Fin n × Fin n

/-- A set of cells is a **matching** when no two of its cells share a row or a column
(§1 of `aristotle.tex`, "Matchings, threats, and completing cells"; equivalently, a graph
matching of `K_{n,n}`). -/
def IsMatching (M : Finset (Cell n)) : Prop :=
  ∀ p ∈ M, ∀ q ∈ M, (p.1 = q.1 ∨ p.2 = q.2) → p = q

/-- `ν(S)`, the maximum size of a matching contained in the set of cells `S`
(§1 of `aristotle.tex`, "Matchings, threats, and completing cells"). -/
noncomputable def nu (S : Finset (Cell n)) : ℕ :=
  ((S.powerset).filter (fun M => IsMatching M)).sup Finset.card

/-- A set of cells **contains a transversal** when `ν(S) = n`, i.e. it contains `n` cells no two
of which share a row or a column (§1 of `aristotle.tex`). -/
def HasTransversal (S : Finset (Cell n)) : Prop := nu S = n

/-- The cell `f` **completes** `S` when `ν(S ∪ {f}) = n`
(§1 of `aristotle.tex`, "Matchings, threats, and completing cells"). -/
def Completes (f : Cell n) (S : Finset (Cell n)) : Prop := nu (insert f S) = n

/-- A player owning `S` **threatens** the cell `f` when `f` is unoccupied (`occ` is the set of
all occupied cells) and `f` completes `S` (§1 of `aristotle.tex`). -/
def Threatens (occ S : Finset (Cell n)) (f : Cell n) : Prop := f ∉ occ ∧ Completes f S

/-- `D_R`, the set of rows exposed by some maximum matching of `S`
(Lemma 2.1 of `aristotle.tex`, "threat structure"). -/
def ExposedRows (S : Finset (Cell n)) : Set (Fin n) :=
  {r | ∃ M, M ⊆ S ∧ IsMatching M ∧ M.card = nu S ∧ ∀ p ∈ M, p.1 ≠ r}

/-- `D_C`, the set of columns exposed by some maximum matching of `S`
(Lemma 2.1 of `aristotle.tex`, "threat structure"). -/
def ExposedCols (S : Finset (Cell n)) : Set (Fin n) :=
  {c | ∃ M, M ⊆ S ∧ IsMatching M ∧ M.card = nu S ∧ ∀ p ∈ M, p.2 ≠ c}

/-! ### Basic properties of matchings -/

theorem IsMatching.subset {M N : Finset (Cell n)} (h : IsMatching N) (hMN : M ⊆ N) :
    IsMatching M := fun _ hp _ hq h' => h _ (hMN hp) _ (hMN hq) h'

theorem IsMatching.injOn_fst {M : Finset (Cell n)} (h : IsMatching M) :
    Set.InjOn Prod.fst (M : Set (Cell n)) := fun _ hp _ hq h' => h _ hp _ hq (Or.inl h')

theorem IsMatching.injOn_snd {M : Finset (Cell n)} (h : IsMatching M) :
    Set.InjOn Prod.snd (M : Set (Cell n)) := fun _ hp _ hq h' => h _ hp _ hq (Or.inr h')

/-- The rows met by a matching, in bijection with its cells. -/
theorem IsMatching.card_image_fst {M : Finset (Cell n)} (h : IsMatching M) :
    (M.image Prod.fst).card = M.card :=
  Finset.card_image_of_injOn h.injOn_fst

theorem IsMatching.card_image_snd {M : Finset (Cell n)} (h : IsMatching M) :
    (M.image Prod.snd).card = M.card :=
  Finset.card_image_of_injOn h.injOn_snd

theorem IsMatching.card_le {M : Finset (Cell n)} (h : IsMatching M) : M.card ≤ n := by
  rw [← h.card_image_fst]
  simpa using Finset.card_le_univ (M.image Prod.fst)

theorem isMatching_empty : IsMatching (∅ : Finset (Cell n)) := by
  intro p hp; simp at hp

/-! ### Basic properties of `ν` -/

theorem le_nu {M S : Finset (Cell n)} (hMS : M ⊆ S) (hM : IsMatching M) : M.card ≤ nu S :=
  Finset.le_sup (f := Finset.card) (by simp [Finset.mem_filter, Finset.mem_powerset, hMS, hM])

theorem exists_max_matching (S : Finset (Cell n)) :
    ∃ M, M ⊆ S ∧ IsMatching M ∧ M.card = nu S := by
  classical
  have hne : ((S.powerset).filter (fun M => IsMatching M)).Nonempty :=
    ⟨∅, by simp [Finset.mem_filter, isMatching_empty]⟩
  obtain ⟨M, hM, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact ⟨M, hM.1, hM.2, hcard.symm⟩

theorem nu_mono {S T : Finset (Cell n)} (h : S ⊆ T) : nu S ≤ nu T := by
  obtain ⟨M, hMS, hM, hcard⟩ := exists_max_matching S
  exact hcard ▸ le_nu (hMS.trans h) hM

theorem nu_le_card (S : Finset (Cell n)) : nu S ≤ S.card := by
  obtain ⟨M, hMS, _, hcard⟩ := exists_max_matching S
  exact hcard ▸ Finset.card_le_card hMS

theorem nu_le (S : Finset (Cell n)) : nu S ≤ n := by
  obtain ⟨M, _, hM, hcard⟩ := exists_max_matching S
  exact hcard ▸ hM.card_le

/-- Inequality (4.2) of `aristotle.tex`: adding cells raises `ν` by at most their number. -/
theorem nu_union_le (S T : Finset (Cell n)) : nu (S ∪ T) ≤ nu S + T.card := by
  obtain ⟨M, hMS, hM, hcard⟩ := exists_max_matching (S ∪ T)
  have h1 : (M ∩ S).card ≤ nu S := le_nu Finset.inter_subset_right (hM.subset Finset.inter_subset_left)
  have h2 : M ⊆ (M ∩ S) ∪ T := by
    intro p hp
    rcases Finset.mem_union.1 (hMS hp) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hp, h⟩)
    · exact Finset.mem_union_right _ h
  calc nu (S ∪ T) = M.card := hcard.symm
    _ ≤ ((M ∩ S) ∪ T).card := Finset.card_le_card h2
    _ ≤ (M ∩ S).card + T.card := Finset.card_union_le _ _
    _ ≤ nu S + T.card := by omega

/-- Adding a single cell raises `ν` by at most `1` (last clause of Lemma 2.1 of
`aristotle.tex`, and inequality (4.2) with `|T| = 1`). -/
theorem nu_insert_le (f : Cell n) (S : Finset (Cell n)) : nu (insert f S) ≤ nu S + 1 := by
  have h := nu_union_le S {f}
  have hu : S ∪ {f} = insert f S := by ext x; simp [Finset.mem_insert]
  rw [hu] at h
  simpa using h

/-- Inequality (4.1) of `aristotle.tex`: a matching meets each line at most once, so deleting a
row `i` from `S` decreases `ν` by at most one. -/
theorem nu_le_filter_row_succ (S : Finset (Cell n)) (i : Fin n) :
    nu S ≤ nu (S.filter (fun p => p.1 ≠ i)) + 1 := by
  obtain ⟨M, hMS, hM, hcard⟩ := exists_max_matching S
  have hsub : M.filter (fun p => p.1 ≠ i) ⊆ S.filter (fun p => p.1 ≠ i) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hMS hp.1, hp.2⟩
  have h1 : (M.filter (fun p => p.1 ≠ i)).card ≤ nu (S.filter (fun p => p.1 ≠ i)) :=
    le_nu hsub (hM.subset (Finset.filter_subset _ _))
  have h2 : (M.filter (fun p => p.1 = i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hM _ ha.1 _ hb.1 (Or.inl (ha.2.trans hb.2.symm))
  have h3 := Finset.card_filter_add_card_filter_not (s := M) (p := fun p => p.1 = i)
  simp only [ne_eq] at h1 h3 ⊢
  omega

/-- Inequality (4.1) of `aristotle.tex` for a column. -/
theorem nu_le_filter_col_succ (S : Finset (Cell n)) (j : Fin n) :
    nu S ≤ nu (S.filter (fun p => p.2 ≠ j)) + 1 := by
  obtain ⟨M, hMS, hM, hcard⟩ := exists_max_matching S
  have hsub : M.filter (fun p => p.2 ≠ j) ⊆ S.filter (fun p => p.2 ≠ j) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hMS hp.1, hp.2⟩
  have h1 : (M.filter (fun p => p.2 ≠ j)).card ≤ nu (S.filter (fun p => p.2 ≠ j)) :=
    le_nu hsub (hM.subset (Finset.filter_subset _ _))
  have h2 : (M.filter (fun p => p.2 = j)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hM _ ha.1 _ hb.1 (Or.inr (ha.2.trans hb.2.symm))
  have h3 := Finset.card_filter_add_card_filter_not (s := M) (p := fun p => p.2 = j)
  simp only [ne_eq] at h1 h3 ⊢
  omega

end Transversal
