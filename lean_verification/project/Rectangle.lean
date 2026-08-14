import project.Threat

/-!
# Lemma 3 (growth of the threat rectangle) and the remark following it

This file formalises the rest of §3 of `main.tex`:

* the near-perfect matching `M` of size `n - 1` missing row `b` and column `d`, together with
  the induced bijection `σ : R \ {b} → C \ {d}` (here encoded as a permutation `σ` of the rows
  with `σ b = d`, which is exactly the same datum);
* **Lemma 3** ("growth of the threat rectangle"), cases (a)–(d);
* the **remark** following Lemma 3: adding a cell outside row `b` and column `d` does not
  create any new completing cell.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-! ### Auxiliary tools -/

/-- If no cell of `S` lies in column `d` while `S` contains a matching of size `n - 1`, then
`ν(S) = n - 1` and `D_C = {d}`. -/
theorem nu_and_exposedCols_of_col_empty {S M : Finset (Cell n)} {d : Fin n}
    (hMS : M ⊆ S) (hM : IsMatching M) (hcard : M.card + 1 = n)
    (hcol : ∀ z ∈ S, z.2 ≠ d) : nu S + 1 = n ∧ ExposedCols S = {d} := by
  have hub : ∀ M' ⊆ S, IsMatching M' → M'.card + 1 ≤ n := by
    intro M' hM'S hM'
    have h1 : M'.image Prod.snd ⊆ Finset.univ.erase d := by
      intro c hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
      exact Finset.mem_erase.2 ⟨hcol z (hM'S hz), Finset.mem_univ _⟩
    have h2 := Finset.card_le_card h1
    rw [hM'.card_image_snd, Finset.card_erase_of_mem (Finset.mem_univ d)] at h2
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have : 1 ≤ n := Fin.pos d
    omega
  have hnu : nu S + 1 = n := by
    obtain ⟨M', hM'S, hM', hM'card⟩ := exists_max_matching S
    have h1 := le_nu hMS hM
    have h2 := hub M' hM'S hM'
    omega
  refine ⟨hnu, ?_⟩
  ext c
  constructor
  · rintro ⟨M', hM'S, hM', hM'card, hM'c⟩
    have himg : M'.image Prod.snd = Finset.univ.erase d := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 he
        exact Finset.mem_erase.2 ⟨hcol z (hM'S hz), Finset.mem_univ _⟩
      · rw [hM'.card_image_snd, Finset.card_erase_of_mem (Finset.mem_univ d)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
    by_contra hcd
    have : c ∈ M'.image Prod.snd := by
      rw [himg]; exact Finset.mem_erase.2 ⟨hcd, Finset.mem_univ _⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 this
    exact hM'c z hz rfl
  · intro hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨M, hMS, hM, by omega, fun z hz => hcol z (hMS hz)⟩

/-- If no cell of `S` lies in row `b` while `S` contains a matching of size `n - 1`, then
`ν(S) = n - 1` and `D_R = {b}`. -/
theorem nu_and_exposedRows_of_row_empty {S M : Finset (Cell n)} {b : Fin n}
    (hMS : M ⊆ S) (hM : IsMatching M) (hcard : M.card + 1 = n)
    (hrow : ∀ z ∈ S, z.1 ≠ b) : nu S + 1 = n ∧ ExposedRows S = {b} := by
  have hub : ∀ M' ⊆ S, IsMatching M' → M'.card + 1 ≤ n := by
    intro M' hM'S hM'
    have h1 : M'.image Prod.fst ⊆ Finset.univ.erase b := by
      intro c hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
      exact Finset.mem_erase.2 ⟨hrow z (hM'S hz), Finset.mem_univ _⟩
    have h2 := Finset.card_le_card h1
    rw [hM'.card_image_fst, Finset.card_erase_of_mem (Finset.mem_univ b)] at h2
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have : 1 ≤ n := Fin.pos b
    omega
  have hnu : nu S + 1 = n := by
    obtain ⟨M', hM'S, hM', hM'card⟩ := exists_max_matching S
    have h1 := le_nu hMS hM
    have h2 := hub M' hM'S hM'
    omega
  refine ⟨hnu, ?_⟩
  ext r
  constructor
  · rintro ⟨M', hM'S, hM', hM'card, hM'r⟩
    have himg : M'.image Prod.fst = Finset.univ.erase b := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 he
        exact Finset.mem_erase.2 ⟨hrow z (hM'S hz), Finset.mem_univ _⟩
      · rw [hM'.card_image_fst, Finset.card_erase_of_mem (Finset.mem_univ b)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
    by_contra hrb
    have : r ∈ M'.image Prod.fst := by
      rw [himg]; exact Finset.mem_erase.2 ⟨hrb, Finset.mem_univ _⟩
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 this
    exact hM'r z hz rfl
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨M, hMS, hM, by omega, fun z hz => hrow z (hMS hz)⟩

/-- Two rows whose only cells of `S` lie in one and the same column cannot both be covered:
hence `ν(S) ≤ n - 1` and every maximum matching exposes one of them. -/
theorem nu_le_of_row_conflict {S : Finset (Cell n)} {b r c : Fin n} (hbr : b ≠ r)
    (hb : ∀ z ∈ S, z.1 = b → z.2 = c) (hr : ∀ z ∈ S, z.1 = r → z.2 = c) :
    ∀ M' ⊆ S, IsMatching M' → M'.card + 1 ≤ n := by
  intro M' hM'S hM'
  by_contra hcon
  push_neg at hcon
  have hn : M'.card = n := le_antisymm hM'.card_le (by omega)
  have himg : M'.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hM'.card_image_fst, hn]
    simp
  have hbmem : b ∈ M'.image Prod.fst := by rw [himg]; exact Finset.mem_univ _
  have hrmem : r ∈ M'.image Prod.fst := by rw [himg]; exact Finset.mem_univ _
  obtain ⟨zb, hzb, hzb'⟩ := Finset.mem_image.1 hbmem
  obtain ⟨zr, hzr, hzr'⟩ := Finset.mem_image.1 hrmem
  have h1 : zb.2 = c := hb zb (hM'S hzb) hzb'
  have h2 : zr.2 = c := hr zr (hM'S hzr) hzr'
  have : zb = zr := hM' zb hzb zr hzr (Or.inr (h1.trans h2.symm))
  rw [this, hzr'] at hzb'
  exact hbr hzb'.symm

/-- Dual of `nu_le_of_row_conflict` for two columns whose only cells lie in one and the same
row. -/
theorem nu_le_of_col_conflict {S : Finset (Cell n)} {d e s : Fin n} (hde : d ≠ e)
    (hd : ∀ z ∈ S, z.2 = d → z.1 = s) (he : ∀ z ∈ S, z.2 = e → z.1 = s) :
    ∀ M' ⊆ S, IsMatching M' → M'.card + 1 ≤ n := by
  intro M' hM'S hM'
  by_contra hcon
  push_neg at hcon
  have hn : M'.card = n := le_antisymm hM'.card_le (by omega)
  have himg : M'.image Prod.snd = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hM'.card_image_snd, hn]
    simp
  have hdmem : d ∈ M'.image Prod.snd := by rw [himg]; exact Finset.mem_univ _
  have hemem : e ∈ M'.image Prod.snd := by rw [himg]; exact Finset.mem_univ _
  obtain ⟨zd, hzd, hzd'⟩ := Finset.mem_image.1 hdmem
  obtain ⟨ze, hze, hze'⟩ := Finset.mem_image.1 hemem
  have h1 : zd.1 = s := hd zd (hM'S hzd) hzd'
  have h2 : ze.1 = s := he ze (hM'S hze) hze'
  have : zd = ze := hM' zd hzd ze hze (Or.inl (h1.trans h2.symm))
  rw [this, hze'] at hzd'
  exact hde hzd'.symm

/-- Under the hypotheses of `nu_le_of_row_conflict`, every maximum matching of `S` (of size
`n - 1`) exposes one of the two conflicting rows. -/
theorem exposedRows_subset_of_row_conflict {S : Finset (Cell n)} {b r c : Fin n} (hbr : b ≠ r)
    (hnu : nu S + 1 = n)
    (hb : ∀ z ∈ S, z.1 = b → z.2 = c) (hr : ∀ z ∈ S, z.1 = r → z.2 = c) :
    ExposedRows S ⊆ {b, r} := by
  rintro z ⟨M', hM'S, hM', hM'card, hM'z⟩
  by_contra hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  have himg : M'.image Prod.fst = Finset.univ.erase z :=
    image_fst_eq_erase hM' (by omega) hM'z
  have hbmem : b ∈ M'.image Prod.fst := by
    rw [himg]; exact Finset.mem_erase.2 ⟨fun h => hz.1 h.symm, Finset.mem_univ _⟩
  have hrmem : r ∈ M'.image Prod.fst := by
    rw [himg]; exact Finset.mem_erase.2 ⟨fun h => hz.2 h.symm, Finset.mem_univ _⟩
  obtain ⟨zb, hzb, hzb'⟩ := Finset.mem_image.1 hbmem
  obtain ⟨zr, hzr, hzr'⟩ := Finset.mem_image.1 hrmem
  have h1 : zb.2 = c := hb zb (hM'S hzb) hzb'
  have h2 : zr.2 = c := hr zr (hM'S hzr) hzr'
  have : zb = zr := hM' zb hzb zr hzr (Or.inr (h1.trans h2.symm))
  rw [this, hzr'] at hzb'
  exact hbr hzb'.symm

/-- Dual of `exposedRows_subset_of_row_conflict`. -/
theorem exposedCols_subset_of_col_conflict {S : Finset (Cell n)} {d e s : Fin n} (hde : d ≠ e)
    (hnu : nu S + 1 = n)
    (hd : ∀ z ∈ S, z.2 = d → z.1 = s) (he : ∀ z ∈ S, z.2 = e → z.1 = s) :
    ExposedCols S ⊆ {d, e} := by
  rintro z ⟨M', hM'S, hM', hM'card, hM'z⟩
  by_contra hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  have himg : M'.image Prod.snd = Finset.univ.erase z :=
    image_snd_eq_erase hM' (by omega) hM'z
  have hdmem : d ∈ M'.image Prod.snd := by
    rw [himg]; exact Finset.mem_erase.2 ⟨fun h => hz.1 h.symm, Finset.mem_univ _⟩
  have hemem : e ∈ M'.image Prod.snd := by
    rw [himg]; exact Finset.mem_erase.2 ⟨fun h => hz.2 h.symm, Finset.mem_univ _⟩
  obtain ⟨zd, hzd, hzd'⟩ := Finset.mem_image.1 hdmem
  obtain ⟨ze, hze, hze'⟩ := Finset.mem_image.1 hemem
  have h1 : zd.1 = s := hd zd (hM'S hzd) hzd'
  have h2 : ze.1 = s := he ze (hM'S hze) hze'
  have : zd = ze := hM' zd hzd ze hze (Or.inl (h1.trans h2.symm))
  rw [this, hze'] at hzd'
  exact hde hzd'.symm

/-! ### The near-perfect matching `M` and its bijection `σ` -/

/-- The matching `M` of §3–§4 of `main.tex`: a matching of size `n - 1` missing row `b`
and column `d = σ b`, whose induced bijection `R \ {b} → C \ {d}` is the restriction of the
permutation `σ`. -/
noncomputable def nearMatching (σ : Equiv.Perm (Fin n)) (b : Fin n) : Finset (Cell n) :=
  (Finset.univ.erase b).image (fun r => (r, σ r))

variable {σ : Equiv.Perm (Fin n)} {b : Fin n}

theorem mem_nearMatching {z : Cell n} : z ∈ nearMatching σ b ↔ z.1 ≠ b ∧ z.2 = σ z.1 := by
  constructor
  · intro hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨(Finset.mem_erase.1 hr).1, rfl⟩
  · intro ⟨h1, h2⟩
    exact Finset.mem_image.2 ⟨z.1, Finset.mem_erase.2 ⟨h1, Finset.mem_univ _⟩,
      by rw [← h2]⟩

theorem nearMatching_isMatching : IsMatching (nearMatching σ b) := by
  intro p hp q hq h
  rw [mem_nearMatching] at hp hq
  rcases h with h | h
  · exact Prod.ext h (by rw [hp.2, hq.2, h])
  · have : σ p.1 = σ q.1 := by rw [← hp.2, ← hq.2, h]
    have h1 : p.1 = q.1 := σ.injective this
    exact Prod.ext h1 h

theorem card_nearMatching : (nearMatching σ b).card + 1 = n := by
  rw [nearMatching, Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.1 h).1),
    Finset.card_erase_of_mem (Finset.mem_univ b)]
  simp only [Finset.card_univ, Fintype.card_fin]
  have : 1 ≤ n := Fin.pos b
  omega

theorem nearMatching_row {z : Cell n} (hz : z ∈ nearMatching σ b) : z.1 ≠ b :=
  (mem_nearMatching.1 hz).1

theorem nearMatching_col {z : Cell n} (hz : z ∈ nearMatching σ b) : z.2 ≠ σ b := by
  intro h
  have := (mem_nearMatching.1 hz).2
  rw [this] at h
  exact (mem_nearMatching.1 hz).1 (σ.injective h)

theorem nearMatching_mem {r : Fin n} (hr : r ≠ b) : (r, σ r) ∈ nearMatching σ b :=
  mem_nearMatching.2 ⟨hr, rfl⟩


/-- `M` with the cell `(r, σ r)` replaced by `(b, σ r)`: a maximum matching exposing row `r`. -/
noncomputable def swapMatchingRow (σ : Equiv.Perm (Fin n)) (b r : Fin n) : Finset (Cell n) :=
  insert (b, σ r) ((nearMatching σ b).erase (r, σ r))

/-- `M` with the cell `(s, σ s)` replaced by `(s, σ b)`: a maximum matching exposing
column `σ s`. -/
noncomputable def swapMatchingCol (σ : Equiv.Perm (Fin n)) (b s : Fin n) : Finset (Cell n) :=
  insert (s, σ b) ((nearMatching σ b).erase (s, σ s))

theorem mem_swapMatchingRow {r : Fin n} {z : Cell n} :
    z ∈ swapMatchingRow σ b r ↔ z = (b, σ r) ∨ (z.1 ≠ b ∧ z.1 ≠ r ∧ z.2 = σ z.1) := by
  rw [swapMatchingRow, Finset.mem_insert, Finset.mem_erase, mem_nearMatching]
  constructor
  · rintro (h | ⟨hne, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_, h2⟩
      rintro rfl
      exact hne (Prod.ext rfl h2)
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨fun h => h2 (congrArg Prod.fst h), h1, h3⟩

theorem mem_swapMatchingCol {s : Fin n} {z : Cell n} :
    z ∈ swapMatchingCol σ b s ↔ z = (s, σ b) ∨ (z.1 ≠ b ∧ z.1 ≠ s ∧ z.2 = σ z.1) := by
  rw [swapMatchingCol, Finset.mem_insert, Finset.mem_erase, mem_nearMatching]
  constructor
  · rintro (h | ⟨hne, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_, h2⟩
      rintro rfl
      exact hne (Prod.ext rfl h2)
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨fun h => h2 (congrArg Prod.fst h), h1, h3⟩

theorem swapMatchingRow_isMatching {r : Fin n} : IsMatching (swapMatchingRow σ b r) := by
  intro p hp q hq h
  rw [mem_swapMatchingRow] at hp hq
  rcases hp with rfl | ⟨hp1, hp2, hp3⟩ <;> rcases hq with rfl | ⟨hq1, hq2, hq3⟩
  · rfl
  · rcases h with h | h
    · exact absurd h.symm hq1
    · exact absurd (σ.injective (h.trans hq3)).symm hq2
  · rcases h with h | h
    · exact absurd h hp1
    · exact absurd (σ.injective (hp3 ▸ h)) hp2
  · rcases h with h | h
    · exact Prod.ext h (by rw [hp3, hq3, h])
    · exact Prod.ext (σ.injective (by rw [← hp3, ← hq3, h])) h

theorem swapMatchingCol_isMatching {s : Fin n} : IsMatching (swapMatchingCol σ b s) := by
  intro p hp q hq h
  rw [mem_swapMatchingCol] at hp hq
  rcases hp with rfl | ⟨hp1, hp2, hp3⟩ <;> rcases hq with rfl | ⟨hq1, hq2, hq3⟩
  · rfl
  · rcases h with h | h
    · exact absurd h.symm hq2
    · exact absurd (σ.injective (h.trans hq3)).symm hq1
  · rcases h with h | h
    · exact absurd h hp2
    · exact absurd (σ.injective (hp3 ▸ h)) hp1
  · rcases h with h | h
    · exact Prod.ext h (by rw [hp3, hq3, h])
    · exact Prod.ext (σ.injective (by rw [← hp3, ← hq3, h])) h

theorem card_swapMatchingRow {r : Fin n} (hr : r ≠ b) : (swapMatchingRow σ b r).card + 1 = n := by
  have hmem : (r, σ r) ∈ nearMatching σ b := nearMatching_mem hr
  have hnot : (b, σ r) ∉ (nearMatching σ b).erase (r, σ r) := by
    intro h
    exact nearMatching_row (Finset.mem_of_mem_erase h) rfl
  rw [swapMatchingRow, Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hmem]
  have := card_nearMatching (σ := σ) (b := b)
  have h1 : 1 ≤ (nearMatching σ b).card := Finset.card_pos.2 ⟨_, hmem⟩
  omega

theorem card_swapMatchingCol {s : Fin n} (hs : s ≠ b) : (swapMatchingCol σ b s).card + 1 = n := by
  have hmem : (s, σ s) ∈ nearMatching σ b := nearMatching_mem hs
  have hnot : (s, σ b) ∉ (nearMatching σ b).erase (s, σ s) := by
    intro h
    exact nearMatching_col (Finset.mem_of_mem_erase h) rfl
  rw [swapMatchingCol, Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem hmem]
  have := card_nearMatching (σ := σ) (b := b)
  have h1 : 1 ≤ (nearMatching σ b).card := Finset.card_pos.2 ⟨_, hmem⟩
  omega

theorem swapMatchingRow_row {r : Fin n} (hr : r ≠ b) {z : Cell n}
    (hz : z ∈ swapMatchingRow σ b r) : z.1 ≠ r := by
  rcases mem_swapMatchingRow.1 hz with rfl | ⟨_, h, _⟩
  · exact Ne.symm hr
  · exact h

theorem swapMatchingCol_col {s : Fin n} (hs : s ≠ b) {z : Cell n}
    (hz : z ∈ swapMatchingCol σ b s) : z.2 ≠ σ s := by
  rcases mem_swapMatchingCol.1 hz with rfl | ⟨_, h, h3⟩
  · intro hc
    exact hs (σ.injective hc).symm
  · intro hc
    rw [h3] at hc
    exact h (σ.injective hc)

theorem nu_eq_of_ub {S M : Finset (Cell n)} (hMS : M ⊆ S) (hM : IsMatching M)
    (hcard : M.card + 1 = n) (hub : ∀ M' ⊆ S, IsMatching M' → M'.card + 1 ≤ n) :
    nu S + 1 = n := by
  obtain ⟨M', hM'S, hM', hM'card⟩ := exists_max_matching S
  have h1 := le_nu hMS hM
  have h2 := hub M' hM'S hM'
  omega


theorem swapMatchingRow_subset {r : Fin n} :
    swapMatchingRow σ b r ⊆ insert (b, σ r) (nearMatching σ b) :=
  Finset.insert_subset_insert _ (Finset.erase_subset _ _)

theorem swapMatchingCol_subset {s : Fin n} :
    swapMatchingCol σ b s ⊆ insert (s, σ b) (nearMatching σ b) :=
  Finset.insert_subset_insert _ (Finset.erase_subset _ _)

/-! ### Lemma 3 (growth of the threat rectangle) -/

/-- **Lemma 3(a)** of `main.tex`: for `S = M ∪ {(b, σ r)}` we have `ν(S) = n - 1`,
`D_R = {b, r}`, `D_C = {d}`, so the completing cells are `(b,d)` and `(r,d)`. -/
theorem rectangle_a {r : Fin n} (hr : r ≠ b) :
    nu (insert (b, σ r) (nearMatching σ b)) + 1 = n ∧
      ExposedRows (insert (b, σ r) (nearMatching σ b)) = {b, r} ∧
      ExposedCols (insert (b, σ r) (nearMatching σ b)) = {σ b} ∧
      {f : Cell n | Completes f (insert (b, σ r) (nearMatching σ b))} =
        ({b, r} : Set (Fin n)) ×ˢ ({σ b} : Set (Fin n)) := by
  set S := insert (b, σ r) (nearMatching σ b) with hSdef
  have hMS : nearMatching σ b ⊆ S := Finset.subset_insert _ _
  have hcol : ∀ z ∈ S, z.2 ≠ σ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact fun h => hr (σ.injective h)
    · exact nearMatching_col hz'
  obtain ⟨hnu, hC⟩ :=
    nu_and_exposedCols_of_col_empty hMS nearMatching_isMatching card_nearMatching hcol
  have hcardM : (nearMatching σ b).card = nu S := by
    have := card_nearMatching (σ := σ) (b := b)
    omega
  have hconf1 : ∀ z ∈ S, z.1 = b → z.2 = σ r := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · rfl
    · exact absurd h (nearMatching_row hz')
  have hconf2 : ∀ z ∈ S, z.1 = r → z.2 = σ r := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact absurd h.symm hr
    · rw [(mem_nearMatching.1 hz').2, h]
  have hR : ExposedRows S = {b, r} := by
    apply Set.Subset.antisymm
    · exact exposedRows_subset_of_row_conflict (Ne.symm hr) hnu hconf1 hconf2
    · intro z hz
      rcases hz with h | h <;> rw [h]
      · exact ⟨nearMatching σ b, hMS, nearMatching_isMatching, hcardM,
          fun w hw => nearMatching_row hw⟩
      · refine ⟨swapMatchingRow σ b r, swapMatchingRow_subset, swapMatchingRow_isMatching, ?_,
          fun w hw => swapMatchingRow_row hr hw⟩
        have := card_swapMatchingRow (σ := σ) hr
        omega
  refine ⟨hnu, hR, hC, ?_⟩
  rw [threat_structure hnu, hR, hC]

/-- **Lemma 3(b)** of `main.tex`: for `S = M ∪ {(r, d)}` we have `ν(S) = n - 1`,
`D_R = {b}`, `D_C = {d, σ r}`, so the completing cells are `(b,d)` and `(b, σ r)`. -/
theorem rectangle_b {r : Fin n} (hr : r ≠ b) :
    nu (insert (r, σ b) (nearMatching σ b)) + 1 = n ∧
      ExposedRows (insert (r, σ b) (nearMatching σ b)) = {b} ∧
      ExposedCols (insert (r, σ b) (nearMatching σ b)) = {σ b, σ r} ∧
      {f : Cell n | Completes f (insert (r, σ b) (nearMatching σ b))} =
        ({b} : Set (Fin n)) ×ˢ ({σ b, σ r} : Set (Fin n)) := by
  set S := insert (r, σ b) (nearMatching σ b) with hSdef
  have hMS : nearMatching σ b ⊆ S := Finset.subset_insert _ _
  have hrow : ∀ z ∈ S, z.1 ≠ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact hr
    · exact nearMatching_row hz'
  obtain ⟨hnu, hR⟩ :=
    nu_and_exposedRows_of_row_empty hMS nearMatching_isMatching card_nearMatching hrow
  have hcardM : (nearMatching σ b).card = nu S := by
    have := card_nearMatching (σ := σ) (b := b)
    omega
  have hconf1 : ∀ z ∈ S, z.2 = σ b → z.1 = r := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · rfl
    · exact absurd h (nearMatching_col hz')
  have hconf2 : ∀ z ∈ S, z.2 = σ r → z.1 = r := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact absurd (σ.injective h).symm hr
    · rw [(mem_nearMatching.1 hz').2] at h
      exact σ.injective h
  have hC : ExposedCols S = {σ b, σ r} := by
    apply Set.Subset.antisymm
    · refine exposedCols_subset_of_col_conflict ?_ hnu hconf1 hconf2
      exact fun h => hr (σ.injective h).symm
    · intro z hz
      rcases hz with h | h <;> rw [h]
      · exact ⟨nearMatching σ b, hMS, nearMatching_isMatching, hcardM,
          fun w hw => nearMatching_col hw⟩
      · refine ⟨swapMatchingCol σ b r, swapMatchingCol_subset, swapMatchingCol_isMatching, ?_,
          fun w hw => swapMatchingCol_col hr hw⟩
        have := card_swapMatchingCol (σ := σ) hr
        omega
  refine ⟨hnu, hR, hC, ?_⟩
  rw [threat_structure hnu, hR, hC]

/-- **Lemma 3(c)** of `main.tex`: for `S = M ∪ {(b, σ r), (s, d)}` with `r ≠ s` we have
`ν(S) = n - 1`, `D_R = {b, r}`, `D_C = {d, σ s}`, so the completing cells form the rectangle
`{b, r} × {d, σ s}`. -/
theorem rectangle_c {r s : Fin n} (hr : r ≠ b) (hs : s ≠ b) (hrs : r ≠ s) :
    nu (insert (b, σ r) (insert (s, σ b) (nearMatching σ b))) + 1 = n ∧
      ExposedRows (insert (b, σ r) (insert (s, σ b) (nearMatching σ b))) = {b, r} ∧
      ExposedCols (insert (b, σ r) (insert (s, σ b) (nearMatching σ b))) = {σ b, σ s} ∧
      {f : Cell n | Completes f (insert (b, σ r) (insert (s, σ b) (nearMatching σ b)))} =
        ({b, r} : Set (Fin n)) ×ˢ ({σ b, σ s} : Set (Fin n)) := by
  set S := insert (b, σ r) (insert (s, σ b) (nearMatching σ b)) with hSdef
  have hMS : nearMatching σ b ⊆ S :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have hrowconf1 : ∀ z ∈ S, z.1 = b → z.2 = σ r := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · rfl
    rcases Finset.mem_insert.1 hz' with rfl | hz''
    · exact absurd h hs
    · exact absurd h (nearMatching_row hz'')
  have hrowconf2 : ∀ z ∈ S, z.1 = r → z.2 = σ r := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact absurd h.symm hr
    rcases Finset.mem_insert.1 hz' with rfl | hz''
    · exact absurd h.symm hrs
    · rw [(mem_nearMatching.1 hz'').2, h]
  have hnu : nu S + 1 = n :=
    nu_eq_of_ub hMS nearMatching_isMatching card_nearMatching
      (nu_le_of_row_conflict (Ne.symm hr) hrowconf1 hrowconf2)
  have hcardM : (nearMatching σ b).card = nu S := by
    have := card_nearMatching (σ := σ) (b := b)
    omega
  have hcolconf1 : ∀ z ∈ S, z.2 = σ b → z.1 = s := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact absurd (σ.injective h) hr
    rcases Finset.mem_insert.1 hz' with rfl | hz''
    · rfl
    · exact absurd h (nearMatching_col hz'')
  have hcolconf2 : ∀ z ∈ S, z.2 = σ s → z.1 = s := by
    intro z hz h
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact absurd (σ.injective h) hrs
    rcases Finset.mem_insert.1 hz' with rfl | hz''
    · rfl
    · rw [(mem_nearMatching.1 hz'').2] at h
      exact σ.injective h
  have hR : ExposedRows S = {b, r} := by
    apply Set.Subset.antisymm
    · exact exposedRows_subset_of_row_conflict (Ne.symm hr) hnu hrowconf1 hrowconf2
    · intro z hz
      rcases hz with h | h <;> rw [h]
      · exact ⟨nearMatching σ b, hMS, nearMatching_isMatching, hcardM,
          fun w hw => nearMatching_row hw⟩
      · refine ⟨swapMatchingRow σ b r, swapMatchingRow_subset.trans
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _)),
          swapMatchingRow_isMatching, ?_, fun w hw => swapMatchingRow_row hr hw⟩
        have := card_swapMatchingRow (σ := σ) hr
        omega
  have hC : ExposedCols S = {σ b, σ s} := by
    apply Set.Subset.antisymm
    · refine exposedCols_subset_of_col_conflict ?_ hnu hcolconf1 hcolconf2
      exact fun h => hs (σ.injective h).symm
    · intro z hz
      rcases hz with h | h <;> rw [h]
      · exact ⟨nearMatching σ b, hMS, nearMatching_isMatching, hcardM,
          fun w hw => nearMatching_col hw⟩
      · refine ⟨swapMatchingCol σ b s, swapMatchingCol_subset.trans ?_,
          swapMatchingCol_isMatching, ?_, fun w hw => swapMatchingCol_col hs hw⟩
        · intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw'
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw')
        · have := card_swapMatchingCol (σ := σ) hs
          omega
  refine ⟨hnu, hR, hC, ?_⟩
  rw [threat_structure hnu, hR, hC]

/-- **Lemma 3(d)** of `main.tex`: for `S = M ∪ {(r, d), (b, σ s)}` with `r ≠ s` we have
`ν(S) = n - 1`, `D_R = {b, s}`, `D_C = {d, σ r}`, so the completing cells form the rectangle
`{b, s} × {d, σ r}`. This is case (c) with the roles of `r` and `s` exchanged. -/
theorem rectangle_d {r s : Fin n} (hr : r ≠ b) (hs : s ≠ b) (hrs : r ≠ s) :
    nu (insert (r, σ b) (insert (b, σ s) (nearMatching σ b))) + 1 = n ∧
      ExposedRows (insert (r, σ b) (insert (b, σ s) (nearMatching σ b))) = {b, s} ∧
      ExposedCols (insert (r, σ b) (insert (b, σ s) (nearMatching σ b))) = {σ b, σ r} ∧
      {f : Cell n | Completes f (insert (r, σ b) (insert (b, σ s) (nearMatching σ b)))} =
        ({b, s} : Set (Fin n)) ×ˢ ({σ b, σ r} : Set (Fin n)) := by
  have h := rectangle_c (σ := σ) (b := b) (r := s) (s := r) hs hr (Ne.symm hrs)
  rwa [Finset.insert_comm] at h

/-- **Remark** following Lemma 3 of `main.tex`: only cells in row `b` or column `d`
create new completing cells. Adding to `M` a cell `(p, q)` with `p ≠ b` and `q ≠ d` leaves
`D_R = {b}`, `D_C = {d}`, so `(b,d)` remains the unique completing cell. -/
theorem rectangle_remark {p q : Fin n} (hp : p ≠ b) (hq : q ≠ σ b) :
    nu (insert (p, q) (nearMatching σ b)) + 1 = n ∧
      ExposedRows (insert (p, q) (nearMatching σ b)) = {b} ∧
      ExposedCols (insert (p, q) (nearMatching σ b)) = {σ b} ∧
      {f : Cell n | Completes f (insert (p, q) (nearMatching σ b))} = {(b, σ b)} := by
  set S := insert (p, q) (nearMatching σ b) with hSdef
  have hMS : nearMatching σ b ⊆ S := Finset.subset_insert _ _
  have hrow : ∀ z ∈ S, z.1 ≠ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact hp
    · exact nearMatching_row hz'
  have hcol : ∀ z ∈ S, z.2 ≠ σ b := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz'
    · exact hq
    · exact nearMatching_col hz'
  obtain ⟨hnu, hR⟩ :=
    nu_and_exposedRows_of_row_empty hMS nearMatching_isMatching card_nearMatching hrow
  obtain ⟨-, hC⟩ :=
    nu_and_exposedCols_of_col_empty hMS nearMatching_isMatching card_nearMatching hcol
  refine ⟨hnu, hR, hC, ?_⟩
  rw [threat_structure hnu, hR, hC]
  ext f
  simp [Prod.ext_iff]

end Transversal
