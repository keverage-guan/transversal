import project.Phase2
import project.Convert

/-!
# Phase 1 and the proof of Theorem A for `n ≥ 4` (§4–5 of `main.tex`)

This file runs X's strategy of §4 of `main.tex` from the empty board:

* `freeRows`, `freeCols` and `openBlock` are the sets `U_R`, `U_C` and `H = U_R × U_C`;
* `Phase1Inv k p` is the state of the game with X to move after `k` moves each: X's stones form
  a matching of size `k`, O has `k` stones, and Invariant 1 holds up to O's latest stone;
* `phase1_win` is the induction over X's Phase-1 moves `1, …, n-2` (Lemma 5);
* `phase1_base` is X's move `n-1`, the tie-break of §4 (Lemmas 6 and 8), after which
  `phase2_after_tiebreak` finishes the game;
* `theoremA_ge_four` is Theorem A for `n ≥ 4`: X wins with their `(n+2)`-nd stone, i.e. by ply
  `2n+3`.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- `U_R`, the set of rows containing no X-stone (§4 of `main.tex`, Phase 1). -/
def freeRows (S : Finset (Cell n)) : Finset (Fin n) := Finset.univ \ S.image Prod.fst

/-- `U_C`, the set of columns containing no X-stone (§4 of `main.tex`, Phase 1). -/
def freeCols (S : Finset (Cell n)) : Finset (Fin n) := Finset.univ \ S.image Prod.snd

theorem mem_freeRows {S : Finset (Cell n)} {x : Fin n} :
    x ∈ freeRows S ↔ ∀ z ∈ S, z.1 ≠ x := by
  constructor
  · intro h z hz hzx
    exact (Finset.mem_sdiff.1 h).2 (Finset.mem_image.2 ⟨z, hz, hzx⟩)
  · intro h
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.1 hmem
    exact h z hz hzx

theorem mem_freeCols {S : Finset (Cell n)} {x : Fin n} :
    x ∈ freeCols S ↔ ∀ z ∈ S, z.2 ≠ x := by
  constructor
  · intro h z hz hzx
    exact (Finset.mem_sdiff.1 h).2 (Finset.mem_image.2 ⟨z, hz, hzx⟩)
  · intro h
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.1 hmem
    exact h z hz hzx

/-- After `k` X-moves forming a matching, `|U_R| = n - k` (§4 of `main.tex`). -/
theorem card_freeRows {S : Finset (Cell n)} (hS : IsMatching S) :
    (freeRows S).card + S.card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S.image Prod.fst))
  rw [hS.card_image_fst] at h
  simpa [freeRows] using h

theorem card_freeCols {S : Finset (Cell n)} (hS : IsMatching S) :
    (freeCols S).card + S.card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S.image Prod.snd))
  rw [hS.card_image_snd] at h
  simpa [freeCols] using h

/-- Playing a cell of the open block deletes its row from `U_R` (§4 of `main.tex`). -/
theorem freeRows_insert {S : Finset (Cell n)} {c : Cell n} :
    freeRows (insert c S) = (freeRows S).erase c.1 := by
  ext x
  rw [Finset.mem_erase, mem_freeRows, mem_freeRows]
  constructor
  · intro h
    exact ⟨fun hx => h c (Finset.mem_insert_self _ _) hx.symm,
      fun z hz => h z (Finset.mem_insert_of_mem hz)⟩
  · rintro ⟨hx, h⟩ z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact fun hzx => hx hzx.symm
    · exact h z hz'

theorem freeCols_insert {S : Finset (Cell n)} {c : Cell n} :
    freeCols (insert c S) = (freeCols S).erase c.2 := by
  ext x
  rw [Finset.mem_erase, mem_freeCols, mem_freeCols]
  constructor
  · intro h
    exact ⟨fun hx => h c (Finset.mem_insert_self _ _) hx.symm,
      fun z hz => h z (Finset.mem_insert_of_mem hz)⟩
  · rintro ⟨hx, h⟩ z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact fun hzx => hx hzx.symm
    · exact h z hz'

/-- The state of the game with X to move, after `k` moves by each player: X's `k` stones form a
matching, O has `k` stones, and **Invariant 1** of `main.tex` holds in the weak form that
the only O-stone possibly lying in the open block `H = U_R × U_C` is O's latest stone. -/
structure Phase1Inv (k : ℕ) (p : Position n) : Prop where
  /-- X's stones form a matching (they lie in successive open blocks). -/
  matchX : IsMatching p.X
  /-- X has played `k` stones. -/
  cardX : p.X.card = k
  /-- O has played `k` stones. -/
  cardO : p.O.card = k
  /-- Invariant 1: at most one O-stone (the latest) lies in the open block. -/
  block : ∃ x, ∀ z ∈ p.O, z ∈ openBlock (freeRows p.X) (freeCols p.X) → z = x

/-- `other x y a ∈ {x, y}`. -/
theorem other_mem_pair {x y a : Fin n} (hxy : y ≠ x) (ha : a = x ∨ a = y) :
    other x y a = x ∨ other x y a = y := by
  rcases ha with rfl | rfl
  · exact Or.inr other_left
  · exact Or.inl (other_right hxy)

/-- The opposite corner is a different corner. -/
theorem other_ne_self {x y a : Fin n} (hxy : y ≠ x) (ha : a = x ∨ a = y) : other x y a ≠ a := by
  rcases ha with rfl | rfl
  · rw [other_left]; exact hxy
  · rw [other_right hxy]; exact fun h => hxy h.symm

/-- **X's move `n-1`**: the tie-break of §4 of `main.tex` (Lemmas 6 and 8), followed by
Phase 2. With `k = n - 2` stones each and Invariant 1 in force, X wins with four more
stones, i.e. by ply `2n+3`. -/
theorem phase1_base {k : ℕ} (hn : 4 ≤ n) (hk : k + 2 = n) {p : Position n}
    (hinv : Phase1Inv k p) : XCanWin 4 p := by
  classical
  set F := p.O with hFdef
  have hFcard : F.card + 2 = n := by rw [hFdef, hinv.cardO]; exact hk
  -- just before X's move `n-1` the open block is a `2 × 2` square
  have hcardR : (freeRows p.X).card = 2 := by
    have h := card_freeRows hinv.matchX
    rw [hinv.cardX] at h
    omega
  have hcardC : (freeCols p.X).card = 2 := by
    have h := card_freeCols hinv.matchX
    rw [hinv.cardX] at h
    omega
  obtain ⟨u₁, u₂, hu12, hURset⟩ := Finset.card_eq_two.1 hcardR
  obtain ⟨v₁, v₂, hv12, hUCset⟩ := Finset.card_eq_two.1 hcardC
  have hmemR : ∀ x : Fin n, x ∈ freeRows p.X ↔ (x = u₁ ∨ x = u₂) := by
    intro x; rw [hURset]; simp
  have hmemC : ∀ x : Fin n, x ∈ freeCols p.X ↔ (x = v₁ ∨ x = v₂) := by
    intro x; rw [hUCset]; simp
  -- Invariant 1: at most one O-stone lies in the open block
  obtain ⟨xstone, hxstone⟩ := hinv.block
  have hFH : (F.filter (fun z => (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂))).card ≤ 1 := by
    have hsub : F.filter (fun z => (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂)) ⊆
        {xstone} := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rw [Finset.mem_singleton]
      refine hxstone z hz.1 ?_
      rw [openBlock, Finset.mem_product]
      exact ⟨(hmemR _).2 hz.2.1, (hmemC _).2 hz.2.2⟩
    have := Finset.card_le_card hsub
    simpa using this
  -- **X's tie-break** (§4 of `main.tex`): prefer an admissible outcome with `1 ≤ w ≤ n-3`
  obtain ⟨b, d, hb, hd, hbdF, hoppF, hw, hstruct0⟩ :
      ∃ b d, (b = u₁ ∨ b = u₂) ∧ (d = v₁ ∨ d = v₂) ∧ (b, d) ∉ F ∧
        (other u₁ u₂ b, other v₁ v₂ d) ∉ F ∧ wParam F b d + 3 ≤ n ∧
        ((∀ z ∈ F, z.1 ≠ b) → (∀ z ∈ F, z.2 ≠ d) → nu F + 2 = n →
          ∀ z ∈ F, z.1 ≠ other u₁ u₂ b ∧ z.2 ≠ other v₁ v₂ d) := by
    by_cases hgood : ∃ b d, (b = u₁ ∨ b = u₂) ∧ (d = v₁ ∨ d = v₂) ∧ (b, d) ∉ F ∧
        (other u₁ u₂ b, other v₁ v₂ d) ∉ F ∧ 1 ≤ wParam F b d ∧ wParam F b d + 3 ≤ n
    · obtain ⟨b, d, hb, hd, hbdF, hoppF, hw1, hw⟩ := hgood
      refine ⟨b, d, hb, hd, hbdF, hoppF, hw, ?_⟩
      intro hrow hcol _
      exfalso
      have hw0 : wParam F b d = 0 := by
        rw [wParam, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro z hz
        push_neg
        exact ⟨hrow z hz, hcol z hz⟩
      omega
    · -- no admissible outcome has `1 ≤ w ≤ n-3`; Lemma 6 still gives one with `w ≤ n-3`
      obtain ⟨b, d, hb, hd, hbdF, hoppF, hw⟩ :=
        tiebreak_exists (Ne.symm hu12) (Ne.symm hv12) hFcard hn hFH
      push_neg at hgood
      have hw0 : wParam F b d = 0 := by
        by_contra hne
        have := hgood b d hb hd hbdF hoppF (by omega)
        omega
      refine ⟨b, d, hb, hd, hbdF, hoppF, hw, ?_⟩
      intro _ _ hnu
      have htie : ∀ b' d', (b' = u₁ ∨ b' = u₂) → (d' = v₁ ∨ d' = v₂) → (b', d') ∉ F →
          (other u₁ u₂ b', other v₁ v₂ d') ∉ F →
          wParam F b' d' = 0 ∨ n < wParam F b' d' + 3 := by
        intro b' d' hb' hd' h1 h2
        by_cases hz : wParam F b' d' = 0
        · exact Or.inl hz
        · exact Or.inr (hgood b' d' hb' hd' h1 h2 (by omega))
      have hnoblock :=
        structF_no_stone_in_block (Ne.symm hu12) (Ne.symm hv12) hb hd hoppF hw0
      obtain ⟨-, hmiss, -, -⟩ :=
        structF_perfect_matching (Ne.symm hu12) (Ne.symm hv12) hn hFcard hb hd hw0 hnoblock
          htie hnu
      intro z hz
      rcases other_mem_pair (Ne.symm hu12) hb with h | h <;>
        rcases other_mem_pair (Ne.symm hv12) hd with h' | h' <;>
        rw [h, h'] <;>
        exact ⟨by simp [(hmiss z hz).1, (hmiss z hz).2.1], by
          simp [(hmiss z hz).2.2.1, (hmiss z hz).2.2.2]⟩
  -- X plays the corner opposite to `(b, d)`
  set e := other u₁ u₂ b with hedef
  set f := other v₁ v₂ d with hfdef
  have heb : e ≠ b := other_ne_self (Ne.symm hu12) hb
  have hfd : f ≠ d := other_ne_self (Ne.symm hv12) hd
  have heUR : e ∈ freeRows p.X := (hmemR _).2 (other_mem_pair (Ne.symm hu12) hb)
  have hfUC : f ∈ freeCols p.X := (hmemC _).2 (other_mem_pair (Ne.symm hv12) hd)
  have hbUR : b ∈ freeRows p.X := (hmemR _).2 hb
  have hdUC : d ∈ freeCols p.X := (hmemC _).2 hd
  have hcX : ((e, f) : Cell n) ∉ p.X := fun hmem => (mem_freeRows.1 heUR) _ hmem rfl
  -- X's stones are now the matching `M` of size `n-1` missing row `b` and column `d`
  have hMmatch : IsMatching (insert ((e, f) : Cell n) p.X) := by
    intro q hq r hr hqr
    rcases Finset.mem_insert.1 hq with rfl | hq' <;> rcases Finset.mem_insert.1 hr with rfl | hr'
    · rfl
    · rcases hqr with h | h
      · exact absurd h.symm ((mem_freeRows.1 heUR) r hr')
      · exact absurd h.symm ((mem_freeCols.1 hfUC) r hr')
    · rcases hqr with h | h
      · exact absurd h ((mem_freeRows.1 heUR) q hq')
      · exact absurd h ((mem_freeCols.1 hfUC) q hq')
    · exact hinv.matchX q hq' r hr' hqr
  have hMcard : (insert ((e, f) : Cell n) p.X).card + 1 = n := by
    rw [Finset.card_insert_of_notMem hcX, hinv.cardX]
    omega
  have hMb : ∀ z ∈ insert ((e, f) : Cell n) p.X, z.1 ≠ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact heb
    · exact fun h => (mem_freeRows.1 hbUR) z hz' h
  have hMd : ∀ z ∈ insert ((e, f) : Cell n) p.X, z.2 ≠ d := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact hfd
    · exact fun h => (mem_freeCols.1 hdUC) z hz' h
  obtain ⟨σ, hσb, hMeq⟩ := exists_perm_of_matching hMmatch hMcard hMb hMd
  have hσe : σ e = f := by
    have hmem : ((e, f) : Cell n) ∈ nearMatching σ b := by
      rw [← hMeq]; exact Finset.mem_insert_self _ _
    exact ((mem_nearMatching.1 hmem).2).symm
  refine Or.inr ⟨(e, f), ?_, Or.inr ?_⟩
  · rw [Position.mem_occupied]
    exact fun h => h.elim hcX (fun h' => hoppF h')
  have hpos : p.playX ((e, f) : Cell n) = (⟨nearMatching σ b, F⟩ : Position n) := by
    rw [Position.playX, hMeq]
  rw [hpos]
  refine ⟨⟨(b, σ b), ?_⟩, phase2_after_tiebreak hn hFcard (by rw [hσb]; exact hbdF)
    (by rw [hσb]; exact hw) ?_⟩
  · -- the cell `(b,d)` is still free, so the game does go on
    rw [Position.mem_occupied]
    rintro (h | h)
    · exact (mem_nearMatching.1 h).1 rfl
    · rw [hσb] at h
      exact hbdF h
  intro hrow hcol hnu
  rw [hσb] at hcol
  refine ⟨e, heb, fun z hz => (hstruct0 hrow hcol hnu z hz).1, fun z hz => ?_⟩
  rw [hσe]
  exact (hstruct0 hrow hcol hnu z hz).2

/-- **Lemma 5** (feasibility of Phase 1) of `main.tex`, run as an induction over X's
Phase-1 moves: from any position satisfying `Phase1Inv k` with `k + m + 2 = n`, X wins with
`m + 4` further stones. -/
theorem phase1_win (hn : 4 ≤ n) : ∀ (m k : ℕ), k + m + 2 = n → ∀ p : Position n,
    Phase1Inv k p → XCanWin (m + 4) p := by
  intro m
  induction m with
  | zero =>
    intro k hk p hinv
    exact phase1_base hn (by omega) hinv
  | succ m ih =>
    intro k hk p hinv
    have hcardR : (freeRows p.X).card + k = n := by
      have := card_freeRows hinv.matchX
      rw [hinv.cardX] at this
      exact this
    have hcardC : (freeCols p.X).card + k = n := by
      have := card_freeCols hinv.matchX
      rw [hinv.cardX] at this
      exact this
    have hUR : (freeRows p.X).Nonempty := by
      rw [← Finset.card_pos]
      omega
    have hUC : 2 ≤ (freeCols p.X).card := by omega
    obtain ⟨x, hx⟩ := hinv.block
    obtain ⟨c, hcH, hcF, hcnew⟩ := phase1_step hUR hUC hx
    rw [openBlock, Finset.mem_product] at hcH
    have hcX : c ∉ p.X := by
      intro hmem
      exact (mem_freeRows.1 hcH.1) c hmem rfl
    refine Or.inr ⟨c, ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [Position.mem_occupied]
      exact fun h => h.elim hcX hcF
    · -- the new open block is nonempty, so a free cell remains after X's move
      have hR : ((freeRows p.X).erase c.1).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hcH.1]
        omega
      have hC : ((freeCols p.X).erase c.2).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hcH.2]
        omega
      obtain ⟨r', hr'⟩ := hR
      obtain ⟨s', hs'⟩ := hC
      refine ⟨(r', s'), ?_⟩
      rw [Position.mem_occupied]
      rintro (h | h)
      · rcases Finset.mem_insert.1 h with heq | h'
        · exact (Finset.mem_erase.1 hr').1 (congrArg Prod.fst heq)
        · exact (mem_freeRows.1 (Finset.mem_erase.1 hr').2) _ h' rfl
      · exact hcnew _ h (by rw [openBlock, Finset.mem_product]; exact ⟨hr', hs'⟩)
    intro c' hc'
    have hc'O : c' ∉ p.O := fun h => hc' (Position.mem_occupied.2 (Or.inr h))
    constructor
    · refine not_hasTransversal_of_card_lt ?_
      have h1 : (insert c' p.O).card = k + 1 := by
        rw [Finset.card_insert_of_notMem hc'O, hinv.cardO]
      simp only [Position.playO_O, Position.playX_O]
      omega
    · refine ih (k + 1) (by omega) _ ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- X's stones are still a matching
        simp only [Position.playO_X, Position.playX_X]
        intro q hq r hr hqr
        rcases Finset.mem_insert.1 hq with rfl | hq' <;>
          rcases Finset.mem_insert.1 hr with rfl | hr'
        · rfl
        · rcases hqr with h | h
          · exact absurd h.symm ((mem_freeRows.1 hcH.1) r hr')
          · exact absurd h.symm ((mem_freeCols.1 hcH.2) r hr')
        · rcases hqr with h | h
          · exact absurd h ((mem_freeRows.1 hcH.1) q hq')
          · exact absurd h ((mem_freeCols.1 hcH.2) q hq')
        · exact hinv.matchX q hq' r hr' hqr
      · simp only [Position.playO_X, Position.playX_X]
        rw [Finset.card_insert_of_notMem hcX, hinv.cardX]
      · simp only [Position.playO_O, Position.playX_O]
        rw [Finset.card_insert_of_notMem hc'O, hinv.cardO]
      · refine ⟨c', ?_⟩
        simp only [Position.playO_O, Position.playX_O, Position.playO_X, Position.playX_X]
        intro z hz hzH
        rcases Finset.mem_insert.1 hz with rfl | hz'
        · rfl
        · exfalso
          refine hcnew z hz' ?_
          rwa [freeRows_insert, freeCols_insert] at hzH

/-- **Theorem A** of `main.tex` for `n ≥ 4`: Player 1 wins, with their `(n+2)`-nd stone,
i.e. by ply `2n+3`. -/
theorem theoremA_ge_four (hn : 4 ≤ n) : XCanWin (n + 2) (⟨∅, ∅⟩ : Position n) := by
  have hb : (0 : ℕ) < n := by omega
  have hinv : Phase1Inv 0 (⟨∅, ∅⟩ : Position n) := by
    refine ⟨isMatching_empty, by simp, by simp, ⟨(⟨0, hb⟩, ⟨0, hb⟩), ?_⟩⟩
    intro z hz
    simp at hz
  have h := phase1_win hn (n - 2) 0 (by omega) _ hinv
  have hEq : n - 2 + 4 = n + 2 := by omega
  rwa [hEq] at h

end Transversal
