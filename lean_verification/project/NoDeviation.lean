import project.Pairs

/-!
# Lemma 4.7 (no defensive deviation) of `main.tex`

O never completes a transversal, and never acquires a threat, during the plies at which X
executes the plan of §3. The three cases (C-i), (C-ii), (C-iii) of the paper are covered by:

* `nodeviation_col`, for (C-i) and for the sub-case `ν(F) ≤ n-3` of (C-iii): O's set is contained
  in `F ∪ column d`, so by (4.1) `ν(O) ≤ n - 2`;
* `nodeviation_row`, the mirror statement for (C-ii);
* `nodeviation_perfect`, for the sub-case `ν(F) = n - 2` of (C-iii), where the crude bound is not
  enough and Lemma 2.1 is used instead: O's unique completing cell is X's own last Phase-1 stone
  `(u_a, v_c)`, which is occupied.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- **Lemma 4.7**, cases (C-i) and (C-iii) with `ν(F) ≤ n-3` of `main.tex`: if O's set is
contained in `F ∪ column d` and `ν(F \ column d) ≤ n - 3`, then `ν(O) ≤ n - 2`; hence O has no
threat (part (a)) and no move of O completes a transversal (part (b)). -/
theorem nodeviation_col {F O : Finset (Cell n)} {d : Fin n}
    (hO : ∀ z ∈ O, z ∈ F ∨ z.2 = d)
    (hF : nu (F.filter (fun z => z.2 ≠ d)) + 3 ≤ n) :
    nu O + 2 ≤ n ∧ (∀ f, ¬ Completes f O) ∧ (∀ g, ¬ HasTransversal (insert g O)) := by
  have hsub : O.filter (fun z => z.2 ≠ d) ⊆ F.filter (fun z => z.2 ≠ d) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    rcases hO z hz.1 with h | h
    · exact ⟨h, hz.2⟩
    · exact absurd h hz.2
  have h1 : nu O ≤ nu (O.filter (fun z => z.2 ≠ d)) + 1 := nu_le_filter_col_succ O d
  have h2 : nu (O.filter (fun z => z.2 ≠ d)) ≤ nu (F.filter (fun z => z.2 ≠ d)) := nu_mono hsub
  have hnu : nu O + 2 ≤ n := by omega
  refine ⟨hnu, not_completes_of_nu_add_two_le hnu, ?_⟩
  intro g hg
  have := nu_insert_le g O
  rw [HasTransversal] at hg
  omega

/-- **Lemma 4.7**, case (C-ii) of `main.tex`: the mirror statement of `nodeviation_col`,
with the line `row b` in place of `column d`. -/
theorem nodeviation_row {F O : Finset (Cell n)} {b : Fin n}
    (hO : ∀ z ∈ O, z ∈ F ∨ z.1 = b)
    (hF : nu (F.filter (fun z => z.1 ≠ b)) + 3 ≤ n) :
    nu O + 2 ≤ n ∧ (∀ f, ¬ Completes f O) ∧ (∀ g, ¬ HasTransversal (insert g O)) := by
  have hsub : O.filter (fun z => z.1 ≠ b) ⊆ F.filter (fun z => z.1 ≠ b) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    rcases hO z hz.1 with h | h
    · exact ⟨h, hz.2⟩
    · exact absurd h hz.2
  have h1 : nu O ≤ nu (O.filter (fun z => z.1 ≠ b)) + 1 := nu_le_filter_row_succ O b
  have h2 : nu (O.filter (fun z => z.1 ≠ b)) ≤ nu (F.filter (fun z => z.1 ≠ b)) := nu_mono hsub
  have hnu : nu O + 2 ≤ n := by omega
  refine ⟨hnu, not_completes_of_nu_add_two_le hnu, ?_⟩
  intro g hg
  have := nu_insert_le g O
  rw [HasTransversal] at hg
  omega

/-- In case (C-i) the hypothesis of `nodeviation_col` holds because `F` meets column `d`, so
`|F \ column d| ≤ n - 3`. -/
theorem nu_filter_col_le_of_meets {F : Finset (Cell n)} {d : Fin n} (hFcard : F.card + 2 = n)
    (hmeet : ∃ z ∈ F, z.2 = d) : nu (F.filter (fun z => z.2 ≠ d)) + 3 ≤ n := by
  obtain ⟨z, hzF, hzd⟩ := hmeet
  have h1 : nu (F.filter (fun z => z.2 ≠ d)) ≤ (F.filter (fun z => z.2 ≠ d)).card :=
    nu_le_card _
  have h2 : (F.filter (fun z => z.2 ≠ d)).card + 1 ≤ F.card := by
    have hz : z ∈ F.filter (fun z => z.2 = d) := Finset.mem_filter.2 ⟨hzF, hzd⟩
    have h3 : 1 ≤ (F.filter (fun z => z.2 = d)).card := Finset.card_pos.2 ⟨z, hz⟩
    have h4 := Finset.card_filter_add_card_filter_not (s := F) (p := fun z => z.2 = d)
    simp only [ne_eq] at *
    omega
  omega

/-- In case (C-ii) the hypothesis of `nodeviation_row` holds because `F` meets row `b`. -/
theorem nu_filter_row_le_of_meets {F : Finset (Cell n)} {b : Fin n} (hFcard : F.card + 2 = n)
    (hmeet : ∃ z ∈ F, z.1 = b) : nu (F.filter (fun z => z.1 ≠ b)) + 3 ≤ n := by
  obtain ⟨z, hzF, hzb⟩ := hmeet
  have h1 : nu (F.filter (fun z => z.1 ≠ b)) ≤ (F.filter (fun z => z.1 ≠ b)).card :=
    nu_le_card _
  have h2 : (F.filter (fun z => z.1 ≠ b)).card + 1 ≤ F.card := by
    have hz : z ∈ F.filter (fun z => z.1 = b) := Finset.mem_filter.2 ⟨hzF, hzb⟩
    have h3 : 1 ≤ (F.filter (fun z => z.1 = b)).card := Finset.card_pos.2 ⟨z, hz⟩
    have h4 := Finset.card_filter_add_card_filter_not (s := F) (p := fun z => z.1 = b)
    simp only [ne_eq] at *
    omega
  omega

/-- The set `F ∪ {(b,d)}` of case (C-iii) with `ν(F) = n-2`: `F` is a perfect matching of
`A × B`, so adding `(b, d)` gives a matching of size `n - 1` missing row `e = u_a` and column
`σ e = v_c`. -/
theorem isMatching_insert_of_perfect {σ : Equiv.Perm (Fin n)} {b e : Fin n} {F : Finset (Cell n)}
    (hFmatch : IsMatching F) (hFrow : ∀ z ∈ F, z.1 ≠ b ∧ z.1 ≠ e)
    (hFcol : ∀ z ∈ F, z.2 ≠ σ b ∧ z.2 ≠ σ e) : IsMatching (insert (b, σ b) F) := by
  intro p hp q hq h
  rcases Finset.mem_insert.1 hp with rfl | hp' <;> rcases Finset.mem_insert.1 hq with rfl | hq'
  · rfl
  · rcases h with h | h
    · exact absurd h.symm (hFrow q hq').1
    · exact absurd h.symm (hFcol q hq').1
  · rcases h with h | h
    · exact absurd h (hFrow p hp').1
    · exact absurd h (hFcol p hp').1
  · exact hFmatch p hp' q hq' h

/-- **Lemma 4.7**, case (C-iii) with `ν(F) = n - 2`, of `main.tex`. Here `F` is a perfect
matching of `A × B` (Lemma 4.3), `e = u_a` is X's last Phase-1 row and `σ e = v_c`. O's set at
ply `2n-1` is `F ∪ {(b,d)}` and at ply `2n+1` it is `F ∪ {(b,d),(r,d)}`; in both cases
`ν(O) = n - 1`, `D_R^O = {e}`, `D_C^O = {σ e}` and the unique completing cell `(e, σ e)` is
X's own stone. Consequently O threatens nothing and no move of O other than the occupied cell
`(e, σ e)` completes a transversal. -/
theorem nodeviation_perfect {σ : Equiv.Perm (Fin n)} {b e : Fin n} {F O : Finset (Cell n)}
    (hFmatch : IsMatching F) (hFcard : F.card + 2 = n)
    (hFrow : ∀ z ∈ F, z.1 ≠ b ∧ z.1 ≠ e) (hFcol : ∀ z ∈ F, z.2 ≠ σ b ∧ z.2 ≠ σ e)
    (hOsub : insert (b, σ b) F ⊆ O)
    (hOrow : ∀ z ∈ O, z.1 ≠ e) (hOcol : ∀ z ∈ O, z.2 ≠ σ e) :
    nu O + 1 = n ∧ ExposedRows O = {e} ∧ ExposedCols O = {σ e} ∧
      {f : Cell n | Completes f O} = {(e, σ e)} := by
  have hM : IsMatching (insert (b, σ b) F) := isMatching_insert_of_perfect hFmatch hFrow hFcol
  have hnotmem : (b, σ b) ∉ F := by
    intro h
    exact (hFrow _ h).1 rfl
  have hcard : (insert (b, σ b) F).card + 1 = n := by
    rw [Finset.card_insert_of_notMem hnotmem]
    omega
  obtain ⟨hnu, hR⟩ := nu_and_exposedRows_of_row_empty hOsub hM hcard hOrow
  obtain ⟨-, hC⟩ := nu_and_exposedCols_of_col_empty hOsub hM hcard hOcol
  refine ⟨hnu, hR, hC, ?_⟩
  rw [threat_structure hnu, hR, hC]
  ext f
  simp [Prod.ext_iff]

end Transversal
