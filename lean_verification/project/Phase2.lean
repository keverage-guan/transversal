import project.NoDeviation
import project.Game

/-!
# Phase 2: the two plans (§4 of `main.tex`)

At ply `2n-3` X owns exactly the matching `M = nearMatching σ b` of size `n-1` missing row `b`
and column `d = σ b`, O owns the `n-2` stones `F`, and `(b,d)` is free. X threatens `(b,d)`
(Corollary 2), so O must block it at ply `2n-2`.

This file proves that, from the resulting position, X wins with three more stones (plies
`2n-1, 2n+1, 2n+3`):

* `plan_i`: plan (i) — X plays `(b, σ r)` then `(s, d)`, creating the double threat
  `{b,r} × {d, σ s}` of Lemma 2.3(c);
* `plan_ii`: plan (ii) — the mirror plan through Lemma 2.3(b),(d).

The hypotheses `hdev₁`, `hdev₂` are exactly Lemma 4.7(b): no move of O at plies `2n` and `2n+2`
completes a transversal.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- **Plan (i)** of §4 of `main.tex` against a blocking O: X plays `(b, σ r)` at ply
`2n-1`, forcing O to take `(r,d)`, then `(s,d)` at ply `2n+1`, creating the double threat on
`(b, σ s)` and `(r, σ s)`, and wins at ply `2n+3`. Combined with Lemma 4.6 (all cells X needs
stay free) and Lemma 4.7 (no defensive deviation, supplied here as `hdev₁`, `hdev₂`). -/
theorem plan_i {σ : Equiv.Perm (Fin n)} {b r s : Fin n} {F : Finset (Cell n)}
    (hlr : Live σ b F r) (hls : Live σ b F s) (hrs : r ≠ s) (hcross : (r, σ s) ∉ F)
    (hdev₁ : ∀ g ∉ nearMatching σ b, ¬ HasTransversal (insert g (insert (b, σ b) F)))
    (hdev₂ : ∀ g ∉ nearMatching σ b,
      ¬ HasTransversal (insert g (insert (r, σ b) (insert (b, σ b) F)))) :
    XCanWin 3 (⟨nearMatching σ b, insert (b, σ b) F⟩ : Position n) := by
  obtain ⟨hrb, hrd, hbr⟩ := hlr
  obtain ⟨hsb, hsd, hbs⟩ := hls
  obtain ⟨-, -, -, hcompa⟩ := rectangle_a (σ := σ) (b := b) hrb
  obtain ⟨-, -, -, hcompc⟩ := rectangle_c (σ := σ) (b := b) hrb hsb hrs
  have hcrossM : (r, σ s) ∉ nearMatching σ b := cross_notMem_nearMatching hrs
  -- X plays `(b, σ r)` at ply `2n-1`
  refine Or.inr ⟨(b, σ r), ?_, Or.inr ⟨⟨(s, σ b), ?_⟩, ?_⟩⟩
  · simp [Position.occupied, mem_nearMatching, Prod.ext_iff, hrb, hbr]
  · simp [Position.occupied, Position.playX, mem_nearMatching, Prod.ext_iff,
      hsb, hsb.symm, hsd]
  intro c₂ hc₂
  refine ⟨hdev₁ c₂ (fun h => hc₂ (Position.mem_occupied.2 (Or.inl (Finset.mem_insert_of_mem h)))),
    ?_⟩
  by_cases hc₂r : c₂ = (r, σ b)
  · -- O blocks `(r,d)`; X plays `(s,d)` at ply `2n+1`
    subst hc₂r
    refine Or.inr ⟨(s, σ b), ?_, Or.inr ⟨⟨(b, σ s), ?_⟩, ?_⟩⟩
    · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
        hsb, hsb.symm, hrs.symm, hsd]
    · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
        hrb.symm, hrs.symm, hsb, hsb.symm, hbs]
    intro c₃ hc₃
    refine ⟨hdev₂ c₃ (fun h => hc₃ (Position.mem_occupied.2
      (Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))))), ?_⟩
    -- the double threat: `(b, σ s)` and `(r, σ s)` both complete X's set
    have hb1 : Completes (b, σ s) (insert (b, σ r) (insert (s, σ b) (nearMatching σ b))) := by
      have : ((b, σ s) : Cell n) ∈ {f : Cell n |
          Completes f (insert (b, σ r) (insert (s, σ b) (nearMatching σ b)))} := by
        rw [hcompc]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
      exact this
    have hb2 : Completes (r, σ s) (insert (b, σ r) (insert (s, σ b) (nearMatching σ b))) := by
      have : ((r, σ s) : Cell n) ∈ {f : Cell n |
          Completes f (insert (b, σ r) (insert (s, σ b) (nearMatching σ b)))} := by
        rw [hcompc]
        exact ⟨Or.inr rfl, Or.inr rfl⟩
      exact this
    by_cases hc₃b : c₃ = (b, σ s)
    · -- O blocks `(b, σ s)`; X takes `(r, σ s)`
      subst hc₃b
      refine xCanWin_one (c := (r, σ s)) ?_ ?_
      · simp [Position.occupied, Position.playX, Position.playO, Prod.ext_iff,
          hrb, hrs, hrs.symm, hsb, hcross, hcrossM]
      · simp only [Position.playO_X, Position.playX_X]
        rw [Finset.insert_comm (s, σ b) (b, σ r)]
        exact hb2
    · -- O does not block `(b, σ s)`; X takes it
      refine xCanWin_one (c := (b, σ s)) ?_ ?_
      · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
          hrb.symm, hrs.symm, hsb, hsb.symm, hbs, Ne.symm hc₃b]
      · simp only [Position.playO_X, Position.playX_X]
        rw [Finset.insert_comm (s, σ b) (b, σ r)]
        exact hb1
  · -- O does not block `(r,d)`; X takes it and wins at ply `2n+1`
    refine xCanWin_one (c := (r, σ b)) ?_ ?_
    · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
        hrb, hrb.symm, hrd, Ne.symm hc₂r]
    · simp only [Position.playO_X, Position.playX_X]
      have : ((r, σ b) : Cell n) ∈
          {f : Cell n | Completes f (insert (b, σ r) (nearMatching σ b))} := by
        rw [hcompa]
        exact ⟨Or.inr rfl, rfl⟩
      exact this

/-- **Plan (ii)** of §4 of `main.tex` against a blocking O: X plays `(r, d)` at ply
`2n-1`, forcing O to take `(b, σ r)`, then `(b, σ s)` at ply `2n+1`, creating the double threat
on `(s, d)` and `(s, σ r)`, and wins at ply `2n+3`. Combined with Lemma 4.6 and Lemma 4.7
(supplied here as `hdev₁`, `hdev₂`). -/
theorem plan_ii {σ : Equiv.Perm (Fin n)} {b r s : Fin n} {F : Finset (Cell n)}
    (hlr : Live σ b F r) (hls : Live σ b F s) (hrs : r ≠ s) (hcross : (s, σ r) ∉ F)
    (hdev₁ : ∀ g ∉ nearMatching σ b, ¬ HasTransversal (insert g (insert (b, σ b) F)))
    (hdev₂ : ∀ g ∉ nearMatching σ b,
      ¬ HasTransversal (insert g (insert (b, σ r) (insert (b, σ b) F)))) :
    XCanWin 3 (⟨nearMatching σ b, insert (b, σ b) F⟩ : Position n) := by
  obtain ⟨hrb, hrd, hbr⟩ := hlr
  obtain ⟨hsb, hsd, hbs⟩ := hls
  obtain ⟨-, -, -, hcompb⟩ := rectangle_b (σ := σ) (b := b) hrb
  obtain ⟨-, -, -, hcompd⟩ := rectangle_d (σ := σ) (b := b) hrb hsb hrs
  have hcrossM : (s, σ r) ∉ nearMatching σ b := cross_notMem_nearMatching (Ne.symm hrs)
  -- X plays `(r, d)` at ply `2n-1`
  refine Or.inr ⟨(r, σ b), ?_, Or.inr ⟨⟨(b, σ s), ?_⟩, ?_⟩⟩
  · simp [Position.occupied, mem_nearMatching, Prod.ext_iff, hrb, hrb.symm, hrd]
  · simp [Position.occupied, Position.playX, mem_nearMatching, Prod.ext_iff,
      hsb, hrb.symm, hbs]
  intro c₂ hc₂
  refine ⟨hdev₁ c₂ (fun h => hc₂ (Position.mem_occupied.2 (Or.inl (Finset.mem_insert_of_mem h)))),
    ?_⟩
  by_cases hc₂r : c₂ = (b, σ r)
  · -- O blocks `(b, σ r)`; X plays `(b, σ s)` at ply `2n+1`
    subst hc₂r
    refine Or.inr ⟨(b, σ s), ?_, Or.inr ⟨⟨(s, σ b), ?_⟩, ?_⟩⟩
    · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
        hsb, hrb.symm, hrs.symm, hbs]
    · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
        hrb.symm, hrs.symm, hsb, hsb.symm, hsd]
    intro c₃ hc₃
    refine ⟨hdev₂ c₃ (fun h => hc₃ (Position.mem_occupied.2
      (Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))))), ?_⟩
    have hb1 : Completes (s, σ b) (insert (r, σ b) (insert (b, σ s) (nearMatching σ b))) := by
      have : ((s, σ b) : Cell n) ∈ {f : Cell n |
          Completes f (insert (r, σ b) (insert (b, σ s) (nearMatching σ b)))} := by
        rw [hcompd]
        exact ⟨Or.inr rfl, Or.inl rfl⟩
      exact this
    have hb2 : Completes (s, σ r) (insert (r, σ b) (insert (b, σ s) (nearMatching σ b))) := by
      have : ((s, σ r) : Cell n) ∈ {f : Cell n |
          Completes f (insert (r, σ b) (insert (b, σ s) (nearMatching σ b)))} := by
        rw [hcompd]
        exact ⟨Or.inr rfl, Or.inr rfl⟩
      exact this
    by_cases hc₃b : c₃ = (s, σ b)
    · -- O blocks `(s,d)`; X takes `(s, σ r)`
      subst hc₃b
      refine xCanWin_one (c := (s, σ r)) ?_ ?_
      · simp [Position.occupied, Position.playX, Position.playO, Prod.ext_iff,
          hrb, hrs, hrs.symm, hsb, hcross, hcrossM]
      · simp only [Position.playO_X, Position.playX_X]
        rw [Finset.insert_comm (b, σ s) (r, σ b)]
        exact hb2
    · -- O does not block `(s,d)`; X takes it
      refine xCanWin_one (c := (s, σ b)) ?_ ?_
      · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
          hrb.symm, hrs.symm, hsb, hsb.symm, hsd, Ne.symm hc₃b]
      · simp only [Position.playO_X, Position.playX_X]
        rw [Finset.insert_comm (b, σ s) (r, σ b)]
        exact hb1
  · -- O does not block `(b, σ r)`; X takes it and wins at ply `2n+1`
    refine xCanWin_one (c := (b, σ r)) ?_ ?_
    · simp [Position.occupied, Position.playX, Position.playO, mem_nearMatching, Prod.ext_iff,
        hrb, hrb.symm, hbr, Ne.symm hc₂r]
    · simp only [Position.playO_X, Position.playX_X]
      have : ((b, σ r) : Cell n) ∈
          {f : Cell n | Completes f (insert (r, σ b) (nearMatching σ b))} := by
        rw [hcompb]
        exact ⟨rfl, Or.inr rfl⟩
      exact this

/-- X's set `M = nearMatching σ b` at ply `2n-3` is completed by the free cell `(b,d)`:
this is the threat of Corollary 2 that forces O's block at ply `2n-2` (§4 of `main.tex`). -/
theorem hasTransversal_insert_nearMatching {σ : Equiv.Perm (Fin n)} {b : Fin n} :
    HasTransversal (insert (b, σ b) (nearMatching σ b)) := by
  obtain ⟨-, -, hcomp⟩ := tempo_unique_completing (M := nearMatching σ b) (b := b) (d := σ b)
    nearMatching_isMatching card_nearMatching (fun _ hz => nearMatching_row hz)
    (fun _ hz => nearMatching_col hz)
  have hmem : ((b, σ b) : Cell n) ∈ {f : Cell n | Completes f (nearMatching σ b)} := by
    rw [hcomp]; rfl
  exact hmem

/-- **Rule 3.3** (plan and pair) of `main.tex`, together with Lemmas 4.4, 4.5 and 4.7:
after O's forced block of `(b,d)` at ply `2n-2`, X selects a plan according to whether the
`n-2` O-stones `F` meet column `d` (case C-i), row `b` (case C-ii) or neither (case C-iii),
and wins with three more stones.

The hypothesis `hstruct` is the conclusion of Lemma 4.3 (structure of `F` when `w = 0`) in the
sub-case `ν(F) = n-2`: `e` is X's last Phase-1 row `u_a`, which `F` misses in both coordinates. -/
theorem phase2_after_block {σ : Equiv.Perm (Fin n)} {b : Fin n} {F : Finset (Cell n)}
    (hn : 4 ≤ n) (hFcard : F.card + 2 = n) (hw : wParam F b (σ b) + 3 ≤ n)
    (hstruct : (∀ z ∈ F, z.1 ≠ b) → (∀ z ∈ F, z.2 ≠ σ b) → nu F + 2 = n →
      ∃ e, e ≠ b ∧ (∀ z ∈ F, z.1 ≠ e) ∧ (∀ z ∈ F, z.2 ≠ σ e)) :
    XCanWin 3 (⟨nearMatching σ b, insert (b, σ b) F⟩ : Position n) := by
  by_cases hcol : ∃ z ∈ F, z.2 = σ b
  · -- **(C-i)** `F` meets column `d`: plan (i), and O's blocks lie in column `d`
    obtain ⟨r, s, hlr, hls, hrs, hcross, -⟩ := exists_admissible_pair hFcard hw
    have hFfil := nu_filter_col_le_of_meets hFcard hcol
    have hO1 : ∀ z ∈ insert ((b, σ b) : Cell n) F, z ∈ F ∨ z.2 = σ b := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | h
      · exact Or.inr rfl
      · exact Or.inl h
    have hO2 : ∀ z ∈ insert ((r, σ b) : Cell n) (insert ((b, σ b) : Cell n) F),
        z ∈ F ∨ z.2 = σ b := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | h
      · exact Or.inr rfl
      · exact hO1 z h
    exact plan_i hlr hls hrs hcross (fun g _ => (nodeviation_col hO1 hFfil).2.2 g)
      (fun g _ => (nodeviation_col hO2 hFfil).2.2 g)
  · by_cases hrow : ∃ z ∈ F, z.1 = b
    · -- **(C-ii)** `F` meets row `b`: plan (ii), and O's blocks lie in row `b`
      obtain ⟨r, s, hlr, hls, hrs, hcross, -⟩ := exists_admissible_pair hFcard hw
      have hFfil := nu_filter_row_le_of_meets hFcard hrow
      have hO1 : ∀ z ∈ insert ((b, σ b) : Cell n) F, z ∈ F ∨ z.1 = b := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | h
        · exact Or.inr rfl
        · exact Or.inl h
      have hO2 : ∀ z ∈ insert ((b, σ s) : Cell n) (insert ((b, σ b) : Cell n) F),
          z ∈ F ∨ z.1 = b := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | h
        · exact Or.inr rfl
        · exact hO1 z h
      exact plan_ii hls hlr (Ne.symm hrs) hcross (fun g _ => (nodeviation_row hO1 hFfil).2.2 g)
        (fun g _ => (nodeviation_row hO2 hFfil).2.2 g)
    · -- **(C-iii)** `w = 0`: `F` misses both row `b` and column `d`
      push_neg at hcol hrow
      have hw0 : wParam F b (σ b) = 0 := by
        rw [wParam, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro z hz
        push_neg
        exact ⟨hrow z hz, hcol z hz⟩
      by_cases hnuF : nu F + 3 ≤ n
      · -- sub-case `ν(F) ≤ n-3`: plan (i) again, O's extra stones lie in column `d`
        obtain ⟨r, s, hlr, hls, hrs, hcross, -⟩ := exists_admissible_pair hFcard hw
        have hFfil : nu (F.filter (fun z => z.2 ≠ σ b)) + 3 ≤ n := by
          have := nu_mono (Finset.filter_subset (fun z => z.2 ≠ σ b) F)
          omega
        have hO1 : ∀ z ∈ insert ((b, σ b) : Cell n) F, z ∈ F ∨ z.2 = σ b := by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | h
          · exact Or.inr rfl
          · exact Or.inl h
        have hO2 : ∀ z ∈ insert ((r, σ b) : Cell n) (insert ((b, σ b) : Cell n) F),
            z ∈ F ∨ z.2 = σ b := by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | h
          · exact Or.inr rfl
          · exact hO1 z h
        exact plan_i hlr hls hrs hcross (fun g _ => (nodeviation_col hO1 hFfil).2.2 g)
          (fun g _ => (nodeviation_col hO2 hFfil).2.2 g)
      · -- sub-case `ν(F) = n-2`: `F` is a perfect matching of `A × B` (Lemma 4.3)
        have hnu2 : nu F + 2 = n := by
          have := nu_le_card F
          omega
        obtain ⟨e, hbe, hFrowe, hFcole⟩ := hstruct hrow hcol hnu2
        have hFmatch : IsMatching F := isMatching_of_nu_eq_card (by omega)
        have hFrow : ∀ z ∈ F, z.1 ≠ b ∧ z.1 ≠ e := fun z hz => ⟨hrow z hz, hFrowe z hz⟩
        have hFcol : ∀ z ∈ F, z.2 ≠ σ b ∧ z.2 ≠ σ e := fun z hz => ⟨hcol z hz, hFcole z hz⟩
        obtain ⟨hlive, r, hlr, hre, hcrossF, -⟩ :=
          pair_of_w_zero (σ := σ) hbe hn hFrow hFcol
        have hemem : (e, σ e) ∈ nearMatching σ b := nearMatching_mem hbe
        -- the unique completing cell of O's set is `(e, σ e)`, X's own last Phase-1 stone
        have hdev : ∀ (O : Finset (Cell n)), insert ((b, σ b) : Cell n) F ⊆ O →
            (∀ z ∈ O, z.1 ≠ e) → (∀ z ∈ O, z.2 ≠ σ e) →
            ∀ g ∉ nearMatching σ b, ¬ HasTransversal (insert g O) := by
          intro O hsub hOrow hOcol g hg hT
          obtain ⟨-, -, -, hcomp⟩ :=
            nodeviation_perfect hFmatch hFcard hFrow hFcol hsub hOrow hOcol
          have hgmem : g ∈ {f : Cell n | Completes f O} := hT
          rw [hcomp, Set.mem_singleton_iff] at hgmem
          exact hg (hgmem ▸ hemem)
        have hrowO1 : ∀ z ∈ insert ((b, σ b) : Cell n) F, z.1 ≠ e := by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | h
          · exact fun hbe' => hbe hbe'.symm
          · exact (hFrow z h).2
        have hcolO1 : ∀ z ∈ insert ((b, σ b) : Cell n) F, z.2 ≠ σ e := by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | h
          · exact fun hbe' => hbe (σ.injective hbe').symm
          · exact (hFcol z h).2
        have hrowO2 : ∀ z ∈ insert ((r, σ b) : Cell n) (insert ((b, σ b) : Cell n) F), z.1 ≠ e := by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | h
          · exact hre
          · exact hrowO1 z h
        have hcolO2 : ∀ z ∈ insert ((r, σ b) : Cell n) (insert ((b, σ b) : Cell n) F),
            z.2 ≠ σ e := by
          intro z hz
          rcases Finset.mem_insert.1 hz with rfl | h
          · exact fun hbe' => hbe (σ.injective hbe').symm
          · exact hcolO1 z h
        exact plan_i hlr hlive hre hcrossF
          (hdev _ (Finset.Subset.refl _) hrowO1 hcolO1)
          (hdev _ (Finset.subset_insert _ _) hrowO2 hcolO2)

/-- The position at ply `2n-3` of `main.tex`, after X's tie-break move: X owns exactly the
matching `M = nearMatching σ b` of size `n-1` missing row `b` and column `d = σ b`, O owns the
`n-2` stones `F`, and `(b,d)` is free. Whatever O plays at ply `2n-2`, that move does not
complete a transversal (Lemma 4.7(b)) and X still wins with three more stones: if O blocks
`(b,d)` this is `phase2_after_block`, and otherwise X plays `(b,d)` at once (Rule 3.4). -/
theorem phase2_after_tiebreak {σ : Equiv.Perm (Fin n)} {b : Fin n} {F : Finset (Cell n)}
    (hn : 4 ≤ n) (hFcard : F.card + 2 = n) (hbd : (b, σ b) ∉ F) (hw : wParam F b (σ b) + 3 ≤ n)
    (hstruct : (∀ z ∈ F, z.1 ≠ b) → (∀ z ∈ F, z.2 ≠ σ b) → nu F + 2 = n →
      ∃ e, e ≠ b ∧ (∀ z ∈ F, z.1 ≠ e) ∧ (∀ z ∈ F, z.2 ≠ σ e)) :
    ∀ c' ∉ (⟨nearMatching σ b, F⟩ : Position n).occupied,
      ¬ HasTransversal (insert c' F) ∧
        XCanWin 3 (⟨nearMatching σ b, insert c' F⟩ : Position n) := by
  intro c' hc'
  have hc'X : c' ∉ nearMatching σ b := fun h => hc' (Position.mem_occupied.2 (Or.inl h))
  have hc'O : c' ∉ F := fun h => hc' (Position.mem_occupied.2 (Or.inr h))
  refine ⟨not_hasTransversal_of_card_lt ?_, ?_⟩
  · have := Finset.card_insert_le c' F
    omega
  by_cases hblock : c' = (b, σ b)
  · subst hblock
    exact phase2_after_block hn hFcard hw hstruct
  · refine xCanWin_one (c := (b, σ b)) ?_ ?_
    · simp only [Position.mem_occupied, Finset.mem_insert, not_or]
      exact ⟨fun h => nearMatching_row h rfl, fun h => hblock h.symm, hbd⟩
    · exact hasTransversal_insert_nearMatching

end Transversal
