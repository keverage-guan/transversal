import project.Rectangle

/-!
# Phase 1 and the tie-break (§4 and Lemmas 5, 6, 8 of `main.tex`)

This file formalises:

* the **open block** `H = U_R × U_C` of §4 and Invariant 1 (`H` contains no O-stone);
* the parameter `w = |F ∩ (row b ∪ col d)|` of the tie-break of §4;
* **Lemma 5** (feasibility of Phase 1): X's Phase-1 rule is always executable and restores
  Invariant 1;
* **Lemma 6** (good tie-break): some admissible outcome has `w ≤ n - 3`;
* **Lemma 8** (structure of `F` when `w = 0`).
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- The **open block** `H = U_R × U_C` of §4 of `main.tex`, where `U_R` and `U_C` are the
rows and the columns containing no X-stone. -/
def openBlock (UR UC : Finset (Fin n)) : Finset (Cell n) := UR ×ˢ UC

/-- The other element of a two-element set `{x, y}`; used for the "opposite corner" of the
open block `H = {u₁,u₂} × {v₁,v₂}` at X's move `n - 1` (§4 of `main.tex`). -/
def other (x y a : Fin n) : Fin n := if a = x then y else x

theorem other_left {x y : Fin n} : other x y x = y := by simp [other]

theorem other_right {x y : Fin n} (h : y ≠ x) : other x y y = x := by simp [other, h]

/-- The parameter `w = |F ∩ (row b ∪ col d)|` attached to a candidate outcome `(b, d)` of the
tie-break of §4 of `main.tex`, where `F` is the set of O-stones. -/
noncomputable def wParam (F : Finset (Cell n)) (b d : Fin n) : ℕ :=
  (F.filter (fun z => z.1 = b ∨ z.2 = d)).card

/-- **Lemma 5** (feasibility of Phase 1) of `main.tex`. Before X's Phase-1 move the open
block is `H = U_R × U_C` and, by Invariant 1, the only O-stone that can lie in `H` is O's most
recent stone `x`. Then X can play a free cell `c` of `H` such that the new open block
`(U_R \ {c.1}) × (U_C \ {c.2})` again contains no O-stone, i.e. Invariant 1 is restored.
(In the paper `|U_R| = |U_C| = m ≥ 3`; the argument only needs `U_R ≠ ∅` and `|U_C| ≥ 2`.) -/
theorem phase1_step {UR UC : Finset (Fin n)} {F : Finset (Cell n)} {x : Cell n}
    (hUR : UR.Nonempty) (hUC : 2 ≤ UC.card)
    (hF : ∀ z ∈ F, z ∈ openBlock UR UC → z = x) :
    ∃ c ∈ openBlock UR UC, c ∉ F ∧
      ∀ z ∈ F, z ∉ openBlock (UR.erase c.1) (UC.erase c.2) := by
  by_cases hx : x ∈ openBlock UR UC ∧ x ∈ F
  · obtain ⟨hxH, hxF⟩ := hx
    rw [openBlock, Finset.mem_product] at hxH
    obtain ⟨q', hq', hq'ne⟩ : ∃ q' ∈ UC, q' ≠ x.2 := by
      by_contra hcon
      push_neg at hcon
      have : UC ⊆ {x.2} := by
        intro c hc
        rw [Finset.mem_singleton]
        exact hcon c hc
      have := Finset.card_le_card this
      simp at this
      omega
    refine ⟨(x.1, q'), ?_, ?_, ?_⟩
    · rw [openBlock, Finset.mem_product]
      exact ⟨hxH.1, hq'⟩
    · intro hmem
      have := hF _ hmem (by rw [openBlock, Finset.mem_product]; exact ⟨hxH.1, hq'⟩)
      exact hq'ne (congrArg Prod.snd this)
    · intro z hz hzmem
      rw [openBlock, Finset.mem_product] at hzmem
      have hzH : z ∈ openBlock UR UC := by
        rw [openBlock, Finset.mem_product]
        exact ⟨Finset.mem_of_mem_erase hzmem.1, Finset.mem_of_mem_erase hzmem.2⟩
      have := hF z hz hzH
      rw [this] at hzmem
      exact (Finset.mem_erase.1 hzmem.1).1 rfl
  · have hempty : ∀ z ∈ F, z ∉ openBlock UR UC := by
      intro z hz hzH
      have hzx := hF z hz hzH
      subst hzx
      exact hx ⟨hzH, hz⟩
    obtain ⟨p, hp⟩ := hUR
    obtain ⟨q, hq⟩ : UC.Nonempty := Finset.card_pos.1 (by omega)
    refine ⟨(p, q), ?_, ?_, ?_⟩
    · rw [openBlock, Finset.mem_product]
      exact ⟨hp, hq⟩
    · intro hmem
      exact hempty _ hmem (by rw [openBlock, Finset.mem_product]; exact ⟨hp, hq⟩)
    · intro z hz hzmem
      rw [openBlock, Finset.mem_product] at hzmem
      exact hempty z hz (by
        rw [openBlock, Finset.mem_product]
        exact ⟨Finset.mem_of_mem_erase hzmem.1, Finset.mem_of_mem_erase hzmem.2⟩)

/-- Inclusion–exclusion bound for two values of the parameter `w`. -/
theorem wParam_add_wParam_le {F : Finset (Cell n)} {b d b' d' : Fin n} :
    wParam F b d + wParam F b' d' ≤
      F.card + (F.filter (fun z => (z.1 = b ∨ z.2 = d) ∧ (z.1 = b' ∨ z.2 = d'))).card := by
  have hunion :
      (F.filter (fun z => z.1 = b ∨ z.2 = d)) ∪ (F.filter (fun z => z.1 = b' ∨ z.2 = d')) ⊆ F :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hinter :
      (F.filter (fun z => z.1 = b ∨ z.2 = d)) ∩ (F.filter (fun z => z.1 = b' ∨ z.2 = d')) =
        F.filter (fun z => (z.1 = b ∨ z.2 = d) ∧ (z.1 = b' ∨ z.2 = d')) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter]
    tauto
  have h := Finset.card_union_add_card_inter
    (F.filter (fun z => z.1 = b ∨ z.2 = d)) (F.filter (fun z => z.1 = b' ∨ z.2 = d'))
  rw [hinter] at h
  have h2 := Finset.card_le_card hunion
  rw [wParam, wParam]
  omega

/-- **Lemma 6** (good tie-break) of `main.tex`: with `H = {u₁,u₂} × {v₁,v₂}` the open
block before X's move `n - 1`, `F` the `n - 2` O-stones, of which at most one lies in `H`
(Invariant 1 together with Lemma 5), some admissible outcome `(b, d)` — i.e. one for which
both `(b,d)` and the cell `(other u₁ u₂ b, other v₁ v₂ d)` played by X are free — satisfies
`w ≤ n - 3`. -/
theorem tiebreak_exists {u₁ u₂ v₁ v₂ : Fin n} (hu : u₂ ≠ u₁) (hv : v₂ ≠ v₁)
    {F : Finset (Cell n)} (hFcard : F.card + 2 = n) (hn : 4 ≤ n)
    (hFH : (F.filter (fun z => (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂))).card ≤ 1) :
    ∃ b d, (b = u₁ ∨ b = u₂) ∧ (d = v₁ ∨ d = v₂) ∧ (b, d) ∉ F ∧
      (other u₁ u₂ b, other v₁ v₂ d) ∉ F ∧ wParam F b d + 3 ≤ n := by
  -- one of the two diagonals of `H` is free of O-stones
  have hdiag : ((u₁, v₁) ∉ F ∧ (u₂, v₂) ∉ F) ∨ ((u₁, v₂) ∉ F ∧ (u₂, v₁) ∉ F) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- both diagonals meet `F`, giving two distinct cells of `F` inside `H`
    obtain ⟨z, hzF, hz1⟩ : ∃ z ∈ F, z = (u₁, v₁) ∨ z = (u₂, v₂) := by
      by_cases hz : (u₁, v₁) ∈ F
      · exact ⟨_, hz, Or.inl rfl⟩
      · exact ⟨_, h1 hz, Or.inr rfl⟩
    obtain ⟨w, hwF, hw1⟩ : ∃ w ∈ F, w = (u₁, v₂) ∨ w = (u₂, v₁) := by
      by_cases hw : (u₁, v₂) ∈ F
      · exact ⟨_, hw, Or.inl rfl⟩
      · exact ⟨_, h2 hw, Or.inr rfl⟩
    have hne : z ≠ w := by
      rcases hz1 with rfl | rfl <;> rcases hw1 with rfl | rfl <;>
        simp [Prod.ext_iff, Ne.symm hu, Ne.symm hv, hu, hv]
    have hzH : (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂) := by
      rcases hz1 with rfl | rfl
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr rfl, Or.inr rfl⟩
    have hwH : (w.1 = u₁ ∨ w.1 = u₂) ∧ (w.2 = v₁ ∨ w.2 = v₂) := by
      rcases hw1 with rfl | rfl
      · exact ⟨Or.inl rfl, Or.inr rfl⟩
      · exact ⟨Or.inr rfl, Or.inl rfl⟩
    have h1' : z ∈ F.filter (fun z => (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂)) :=
      Finset.mem_filter.2 ⟨hzF, hzH⟩
    have h2' : w ∈ F.filter (fun z => (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂)) :=
      Finset.mem_filter.2 ⟨hwF, hwH⟩
    have := Finset.one_lt_card.2 ⟨z, h1', w, h2', hne⟩
    omega
  -- on the free diagonal, both outcomes are admissible and their `w`'s add up to at most `n-1`
  have key : ∀ b d b' d', b' = other u₁ u₂ b → d' = other v₁ v₂ d →
      (b = u₁ ∨ b = u₂) → (d = v₁ ∨ d = v₂) → b ≠ b' → d ≠ d' →
      (b, d) ∉ F → (b', d') ∉ F →
      wParam F b d + wParam F b' d' ≤ F.card + 1 := by
    intro b d b' d' hb' hd' _ _ hbb hdd hbd hbd'
    have hsub : F.filter (fun z => (z.1 = b ∨ z.2 = d) ∧ (z.1 = b' ∨ z.2 = d')) ⊆
        F.filter (fun z => (z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂)) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, ?_⟩
      obtain ⟨hzF, h1, h2⟩ := hz
      -- `z` lies on the other diagonal of `H`
      have hz' : (z.1 = b ∧ z.2 = d') ∨ (z.1 = b' ∧ z.2 = d) := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1 ▸ h2) hbb
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
        · exact absurd (h1 ▸ h2) hdd
      subst hb'
      subst hd'
      have hbmem : b = u₁ ∨ b = u₂ := by assumption
      have hdmem : d = v₁ ∨ d = v₂ := by assumption
      have hother1 : other u₁ u₂ b = u₁ ∨ other u₁ u₂ b = u₂ := by
        rcases hbmem with rfl | rfl
        · exact Or.inr other_left
        · exact Or.inl (other_right hu)
      have hother2 : other v₁ v₂ d = v₁ ∨ other v₁ v₂ d = v₂ := by
        rcases hdmem with rfl | rfl
        · exact Or.inr other_left
        · exact Or.inl (other_right hv)
      rcases hz' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨ha ▸ hbmem, hb ▸ hother2⟩
      · exact ⟨ha ▸ hother1, hb ▸ hdmem⟩
    have hcard := Finset.card_le_card hsub
    have := wParam_add_wParam_le (F := F) (b := b) (d := d) (b' := b') (d' := d')
    omega
  rcases hdiag with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hk := key u₁ v₁ u₂ v₂ (other_left).symm (other_left).symm (Or.inl rfl) (Or.inl rfl)
      (Ne.symm hu) (Ne.symm hv) h1 h2
    by_cases hw : wParam F u₁ v₁ + 3 ≤ n
    · exact ⟨u₁, v₁, Or.inl rfl, Or.inl rfl, h1, by rw [other_left, other_left]; exact h2, hw⟩
    · refine ⟨u₂, v₂, Or.inr rfl, Or.inr rfl, h2, ?_, by omega⟩
      rw [other_right hu, other_right hv]
      exact h1
  · have hk := key u₁ v₂ u₂ v₁ (other_left).symm (other_right hv).symm (Or.inl rfl) (Or.inr rfl)
      (Ne.symm hu) hv h1 h2
    by_cases hw : wParam F u₁ v₂ + 3 ≤ n
    · exact ⟨u₁, v₂, Or.inl rfl, Or.inr rfl, h1, by rw [other_left, other_right hv]; exact h2, hw⟩
    · refine ⟨u₂, v₁, Or.inr rfl, Or.inl rfl, h2, ?_, by omega⟩
      rw [other_right hu, other_left]
      exact h1

theorem other_other {x y a : Fin n} (hxy : y ≠ x) (ha : a = x ∨ a = y) :
    other x y (other x y a) = a := by
  rcases ha with rfl | rfl
  · rw [other_left, other_right hxy]
  · rw [other_right hxy, other_left]

theorem eq_other {x y a c : Fin n} (hxy : y ≠ x) (ha : a = x ∨ a = y) (hc : c = x ∨ c = y)
    (hca : c ≠ a) : c = other x y a := by
  rcases ha with rfl | rfl
  · rw [other_left]
    rcases hc with rfl | rfl
    · exact absurd rfl hca
    · rfl
  · rw [other_right hxy]
    rcases hc with rfl | rfl
    · rfl
    · exact absurd rfl hca

/-- A set whose matching number equals its cardinality is a matching. -/
theorem isMatching_of_nu_eq_card {F : Finset (Cell n)} (h : nu F = F.card) : IsMatching F := by
  obtain ⟨M, hMF, hM, hcard⟩ := exists_max_matching F
  have : M = F := Finset.eq_of_subset_of_card_le hMF (by omega)
  exact this ▸ hM

/-- First part of **Lemma 8** (structure of `F` when `w = 0`) of `main.tex`: if the
outcome `(b,d)` chosen by the tie-break is admissible and has `w = 0`, then no O-stone lies in
the open block `H = {u₁,u₂} × {v₁,v₂}` (in particular O's latest stone `x_{n-2}` is not in
`H`, so all four corners of `H` are admissible). -/
theorem structF_no_stone_in_block {u₁ u₂ v₁ v₂ b d : Fin n} {F : Finset (Cell n)}
    (hu : u₂ ≠ u₁) (hv : v₂ ≠ v₁) (hb : b = u₁ ∨ b = u₂) (hd : d = v₁ ∨ d = v₂)
    (hoppfree : (other u₁ u₂ b, other v₁ v₂ d) ∉ F) (hw : wParam F b d = 0) :
    ∀ z ∈ F, ¬ ((z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂)) := by
  intro z hzF hzH
  have hfilter : F.filter (fun z => z.1 = b ∨ z.2 = d) = ∅ := by
    rw [← Finset.card_eq_zero]
    exact hw
  have hz : ¬ (z.1 = b ∨ z.2 = d) := by
    intro h
    have : z ∈ F.filter (fun z => z.1 = b ∨ z.2 = d) := Finset.mem_filter.2 ⟨hzF, h⟩
    rw [hfilter] at this
    exact absurd this (Finset.notMem_empty z)
  push_neg at hz
  have h1 : z.1 = other u₁ u₂ b := eq_other hu hb hzH.1 hz.1
  have h2 : z.2 = other v₁ v₂ d := eq_other hv hd hzH.2 hz.2
  have hzeq : z = (other u₁ u₂ b, other v₁ v₂ d) := Prod.ext h1 h2
  exact hoppfree (hzeq ▸ hzF)

/-- Second part of **Lemma 8** of `main.tex`: if moreover `ν(F) = n - 2`, then `F` is a
perfect matching of `A × B`, where `A = R \ {u₁,u₂}` and `B = C \ {v₁,v₂}`. The hypothesis
`htie` is the tie-break rule of §4: no admissible outcome has `1 ≤ w ≤ n - 3`. -/
theorem structF_perfect_matching {u₁ u₂ v₁ v₂ b d : Fin n} {F : Finset (Cell n)}
    (hu : u₂ ≠ u₁) (hv : v₂ ≠ v₁) (hn : 4 ≤ n) (hFcard : F.card + 2 = n)
    (hb : b = u₁ ∨ b = u₂) (hd : d = v₁ ∨ d = v₂) (hw : wParam F b d = 0)
    (hnoblock : ∀ z ∈ F, ¬ ((z.1 = u₁ ∨ z.1 = u₂) ∧ (z.2 = v₁ ∨ z.2 = v₂)))
    (htie : ∀ b' d', (b' = u₁ ∨ b' = u₂) → (d' = v₁ ∨ d' = v₂) → (b', d') ∉ F →
      (other u₁ u₂ b', other v₁ v₂ d') ∉ F → wParam F b' d' = 0 ∨ n < wParam F b' d' + 3)
    (hnu : nu F + 2 = n) :
    IsMatching F ∧ (∀ z ∈ F, z.1 ≠ u₁ ∧ z.1 ≠ u₂ ∧ z.2 ≠ v₁ ∧ z.2 ≠ v₂) ∧
      F.image Prod.fst = (Finset.univ.erase u₁).erase u₂ ∧
      F.image Prod.snd = (Finset.univ.erase v₁).erase v₂ := by
  have hmatch : IsMatching F := isMatching_of_nu_eq_card (by omega)
  -- `w = 0` says `F` misses row `b` and column `d`
  have hrowb : ∀ z ∈ F, z.1 ≠ b ∧ z.2 ≠ d := by
    intro z hzF
    have hfilter : F.filter (fun z => z.1 = b ∨ z.2 = d) = ∅ := by
      rw [← Finset.card_eq_zero]; exact hw
    have : ¬ (z.1 = b ∨ z.2 = d) := by
      intro h
      have : z ∈ F.filter (fun z => z.1 = b ∨ z.2 = d) := Finset.mem_filter.2 ⟨hzF, h⟩
      rw [hfilter] at this
      exact absurd this (Finset.notMem_empty z)
    exact not_or.1 this
  have hcorner : ∀ b' d', (b' = u₁ ∨ b' = u₂) → (d' = v₁ ∨ d' = v₂) → (b', d') ∉ F := by
    intro b' d' hb' hd' hmem
    exact hnoblock _ hmem ⟨hb', hd'⟩
  -- no O-stone in the opposite row
  have hrowb' : ∀ z ∈ F, z.1 ≠ other u₁ u₂ b := by
    intro z hzF hz1
    have hb' : other u₁ u₂ b = u₁ ∨ other u₁ u₂ b = u₂ := by
      rcases hb with rfl | rfl
      · exact Or.inr other_left
      · exact Or.inl (other_right hu)
    have hadm1 : (other u₁ u₂ b, d) ∉ F := hcorner _ _ hb' hd
    have hadm2 : (other u₁ u₂ (other u₁ u₂ b), other v₁ v₂ d) ∉ F := by
      rw [other_other hu hb]
      refine hcorner _ _ hb ?_
      rcases hd with rfl | rfl
      · exact Or.inr other_left
      · exact Or.inl (other_right hv)
    have hw1 : wParam F (other u₁ u₂ b) d = 1 := by
      have hset : F.filter (fun w => w.1 = other u₁ u₂ b ∨ w.2 = d) = {z} := by
        apply Finset.eq_singleton_iff_unique_mem.2
        refine ⟨Finset.mem_filter.2 ⟨hzF, Or.inl hz1⟩, ?_⟩
        intro w hw'
        rw [Finset.mem_filter] at hw'
        rcases hw'.2 with h | h
        · exact hmatch w hw'.1 z hzF (Or.inl (h.trans hz1.symm))
        · exact absurd h (hrowb w hw'.1).2
      rw [wParam, hset]
      simp
    rcases htie _ _ hb' hd hadm1 hadm2 with h | h <;> omega
  -- no O-stone in the opposite column
  have hcold' : ∀ z ∈ F, z.2 ≠ other v₁ v₂ d := by
    intro z hzF hz2
    have hd' : other v₁ v₂ d = v₁ ∨ other v₁ v₂ d = v₂ := by
      rcases hd with rfl | rfl
      · exact Or.inr other_left
      · exact Or.inl (other_right hv)
    have hadm1 : (b, other v₁ v₂ d) ∉ F := hcorner _ _ hb hd'
    have hadm2 : (other u₁ u₂ b, other v₁ v₂ (other v₁ v₂ d)) ∉ F := by
      rw [other_other hv hd]
      refine hcorner _ _ ?_ hd
      rcases hb with rfl | rfl
      · exact Or.inr other_left
      · exact Or.inl (other_right hu)
    have hw1 : wParam F b (other v₁ v₂ d) = 1 := by
      have hset : F.filter (fun w => w.1 = b ∨ w.2 = other v₁ v₂ d) = {z} := by
        apply Finset.eq_singleton_iff_unique_mem.2
        refine ⟨Finset.mem_filter.2 ⟨hzF, Or.inr hz2⟩, ?_⟩
        intro w hw'
        rw [Finset.mem_filter] at hw'
        rcases hw'.2 with h | h
        · exact absurd h (hrowb w hw'.1).1
        · exact hmatch w hw'.1 z hzF (Or.inr (h.trans hz2.symm))
      rw [wParam, hset]
      simp
    rcases htie _ _ hb hd' hadm1 hadm2 with h | h <;> omega
  have hout : ∀ z ∈ F, z.1 ≠ u₁ ∧ z.1 ≠ u₂ ∧ z.2 ≠ v₁ ∧ z.2 ≠ v₂ := by
    intro z hzF
    have h1 := (hrowb z hzF).1
    have h2 := hrowb' z hzF
    have h3 := (hrowb z hzF).2
    have h4 := hcold' z hzF
    rcases hb with rfl | rfl
    · rw [other_left] at h2
      rcases hd with rfl | rfl
      · rw [other_left] at h4
        exact ⟨h1, h2, h3, h4⟩
      · rw [other_right hv] at h4
        exact ⟨h1, h2, h4, h3⟩
    · rw [other_right hu] at h2
      rcases hd with rfl | rfl
      · rw [other_left] at h4
        exact ⟨h2, h1, h3, h4⟩
      · rw [other_right hv] at h4
        exact ⟨h2, h1, h4, h3⟩
  refine ⟨hmatch, hout, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hr
      exact Finset.mem_erase.2 ⟨(hout z hz).2.1,
        Finset.mem_erase.2 ⟨(hout z hz).1, Finset.mem_univ _⟩⟩
    · rw [hmatch.card_image_fst, Finset.card_erase_of_mem
        (Finset.mem_erase.2 ⟨hu, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ u₁)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
  · apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
      exact Finset.mem_erase.2 ⟨(hout z hz).2.2.2,
        Finset.mem_erase.2 ⟨(hout z hz).2.2.1, Finset.mem_univ _⟩⟩
    · rw [hmatch.card_image_snd, Finset.card_erase_of_mem
        (Finset.mem_erase.2 ⟨hv, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ v₁)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega

end Transversal
