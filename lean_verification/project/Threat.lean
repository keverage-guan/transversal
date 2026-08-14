import project.Basic

/-!
# Lemma 1 (threat structure) and Corollary 2 (tempo)

This file formalises §2 of `main.tex` up to and including Corollary 2:

* Lemma 1 ("threat structure"): if `ν(S) = n - 1` then the set of cells completing `S`
  is exactly the rectangle `D_R × D_C`, and if `ν(S) ≤ n - 2` no single cell completes `S`;
* the two remarks following Lemma 1 (`D_R × D_C` is disjoint from `S`);
* Corollary 2 ("tempo").

The proof of the inclusion `D_R × D_C ⊆ {f : f completes S}` given here is a Hall-type
argument replacing the alternating-path argument of the paper.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- The columns adjacent to the row `r` inside the set of cells `S`. -/
noncomputable def nbrs (S : Finset (Cell n)) (r : Fin n) : Finset (Fin n) :=
  (S.filter (fun z => z.1 = r)).image Prod.snd

theorem mem_nbrs {S : Finset (Cell n)} {r c : Fin n} : c ∈ nbrs S r ↔ (r, c) ∈ S := by
  simp only [nbrs, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨z, ⟨hz, rfl⟩, rfl⟩; exact hz
  · intro h; exact ⟨(r, c), ⟨h, rfl⟩, rfl⟩

/-- A matching of size `n - 1` all of whose cells avoid the row `p` meets every other row. -/
theorem image_fst_eq_erase {M : Finset (Cell n)} {p : Fin n} (hM : IsMatching M)
    (hcard : M.card + 1 = n) (hp : ∀ z ∈ M, z.1 ≠ p) :
    M.image Prod.fst = Finset.univ.erase p := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hr
    exact Finset.mem_erase.2 ⟨hp z hz, Finset.mem_univ _⟩
  · rw [hM.card_image_fst, Finset.card_erase_of_mem (Finset.mem_univ p)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega

/-- A matching of size `n - 1` all of whose cells avoid the column `q` meets every other
column. -/
theorem image_snd_eq_erase {M : Finset (Cell n)} {q : Fin n} (hM : IsMatching M)
    (hcard : M.card + 1 = n) (hq : ∀ z ∈ M, z.2 ≠ q) :
    M.image Prod.snd = Finset.univ.erase q := by
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_erase.2 ⟨hq z hz, Finset.mem_univ _⟩
  · rw [hM.card_image_snd, Finset.card_erase_of_mem (Finset.mem_univ q)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega

/-- The easy inclusion of Lemma 1 of `main.tex`: a cell completing `S` lies in
`D_R × D_C`. -/
theorem exposed_of_completes {S : Finset (Cell n)} (hS : nu S + 1 = n) {f : Cell n}
    (hf : Completes f S) : f.1 ∈ ExposedRows S ∧ f.2 ∈ ExposedCols S := by
  obtain ⟨M, hMS, hM, hcard⟩ := exists_max_matching (insert f S)
  rw [Completes] at hf
  rw [hf] at hcard
  have hfM : f ∈ M := by
    by_contra hfM
    have : M ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.1 (hMS hz) with h | h
      · exact absurd (h ▸ hz) hfM
      · exact h
    have := le_nu this hM
    omega
  set M' := M.erase f with hM'
  have hM'S : M' ⊆ S := by
    intro z hz
    have hz' := Finset.mem_of_mem_erase hz
    rcases Finset.mem_insert.1 (hMS hz') with h | h
    · exact absurd h (Finset.ne_of_mem_erase hz)
    · exact h
  have hM'match : IsMatching M' := hM.subset (Finset.erase_subset _ _)
  have hM'card : M'.card = nu S := by
    rw [hM', Finset.card_erase_of_mem hfM, hcard]; omega
  have hrow : ∀ z ∈ M', z.1 ≠ f.1 := by
    intro z hz h
    exact (Finset.ne_of_mem_erase hz) (hM z (Finset.mem_of_mem_erase hz) f hfM (Or.inl h))
  have hcol : ∀ z ∈ M', z.2 ≠ f.2 := by
    intro z hz h
    exact (Finset.ne_of_mem_erase hz) (hM z (Finset.mem_of_mem_erase hz) f hfM (Or.inr h))
  exact ⟨⟨M', hM'S, hM'match, hM'card, hrow⟩, ⟨M', hM'S, hM'match, hM'card, hcol⟩⟩

/-- The hard inclusion of Lemma 1 of `main.tex`: every cell of `D_R × D_C` completes `S`.
Where the paper argues with an alternating path in `M₁ △ M₂`, we verify Hall's condition for
the bipartite graph `S` restricted to the rows `≠ p` and the columns `≠ q`. -/
theorem completes_of_exposed {S : Finset (Cell n)} (hS : nu S + 1 = n) {p q : Fin n}
    (hp : p ∈ ExposedRows S) (hq : q ∈ ExposedCols S) : Completes (p, q) S := by
  obtain ⟨M₁, hM₁S, hM₁, hM₁card, hM₁p⟩ := hp
  obtain ⟨M₂, hM₂S, hM₂, hM₂card, hM₂q⟩ := hq
  have hrows : M₁.image Prod.fst = Finset.univ.erase p :=
    image_fst_eq_erase hM₁ (by omega) hM₁p
  have hcols : M₂.image Prod.snd = Finset.univ.erase q :=
    image_snd_eq_erase hM₂ (by omega) hM₂q
  -- Hall's condition for the restricted bipartite graph
  have hall : ∀ s : Finset {r : Fin n // r ≠ p},
      s.card ≤ (s.biUnion (fun r => (nbrs S r.1).erase q)).card := by
    intro s
    set A : Finset (Fin n) := s.image Subtype.val with hA
    have hAcard : A.card = s.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hAp : ∀ r ∈ A, r ≠ p := by
      intro r hr
      obtain ⟨r', _, rfl⟩ := Finset.mem_image.1 hr
      exact r'.2
    set NA : Finset (Fin n) := A.biUnion (nbrs S) with hNA
    have hbi : s.biUnion (fun r => (nbrs S r.1).erase q) = NA.erase q := by
      ext c
      constructor
      · intro hc
        obtain ⟨r, hr, hc'⟩ := Finset.mem_biUnion.1 hc
        rw [Finset.mem_erase] at hc' ⊢
        exact ⟨hc'.1, Finset.mem_biUnion.2 ⟨(r : Fin n), Finset.mem_image.2 ⟨r, hr, rfl⟩, hc'.2⟩⟩
      · intro hc
        rw [Finset.mem_erase] at hc
        obtain ⟨r, hr, hc'⟩ := Finset.mem_biUnion.1 hc.2
        obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hr
        exact Finset.mem_biUnion.2 ⟨r', hr', Finset.mem_erase.2 ⟨hc.1, hc'⟩⟩
    rw [hbi, ← hAcard]
    -- `P₁` matches `A` injectively into `NA`
    set P₁ : Finset (Cell n) := M₁.filter (fun z => z.1 ∈ A) with hP₁
    have hP₁fst : P₁.image Prod.fst = A := by
      apply Finset.Subset.antisymm
      · intro r hr
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hr
        exact (Finset.mem_filter.1 hz).2
      · intro r hr
        have : r ∈ M₁.image Prod.fst := by
          rw [hrows]; exact Finset.mem_erase.2 ⟨hAp r hr, Finset.mem_univ _⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 this
        exact Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, hr⟩, rfl⟩
    have hP₁card : P₁.card = A.card := by
      rw [← hP₁fst, (hM₁.subset (Finset.filter_subset _ _)).card_image_fst]
    have hP₁snd : P₁.image Prod.snd ⊆ NA := by
      intro c hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
      rw [Finset.mem_filter] at hz
      refine Finset.mem_biUnion.2 ⟨z.1, hz.2, mem_nbrs.2 ?_⟩
      simpa using hM₁S hz.1
    have hAle : A.card ≤ NA.card := by
      calc A.card = P₁.card := hP₁card.symm
        _ = (P₁.image Prod.snd).card := ((hM₁.subset (Finset.filter_subset _ _)).card_image_snd).symm
        _ ≤ NA.card := Finset.card_le_card hP₁snd
    by_cases hqNA : q ∈ NA
    · -- If `|NA| = |A|` we can build a perfect matching, contradicting `ν(S) = n - 1`.
      by_contra hcon
      push_neg at hcon
      have hcardNA : NA.card = A.card := by
        rw [Finset.card_erase_of_mem hqNA] at hcon
        have : 1 ≤ NA.card := Finset.card_pos.2 ⟨q, hqNA⟩
        omega
      -- `P₂` matches all columns outside `NA`
      set P₂ : Finset (Cell n) := M₂.filter (fun z => z.2 ∉ NA) with hP₂
      have hP₂row : ∀ z ∈ P₂, z.1 ∉ A := by
        intro z hz hzA
        rw [Finset.mem_filter] at hz
        refine hz.2 (Finset.mem_biUnion.2 ⟨z.1, hzA, mem_nbrs.2 ?_⟩)
        simpa using hM₂S hz.1
      have hP₂snd : P₂.image Prod.snd = Finset.univ \ NA := by
        apply Finset.Subset.antisymm
        · intro c hc
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hc
          rw [Finset.mem_filter] at hz
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hz.2⟩
        · intro c hc
          rw [Finset.mem_sdiff] at hc
          have hcq : c ≠ q := by rintro rfl; exact hc.2 hqNA
          have : c ∈ M₂.image Prod.snd := by
            rw [hcols]; exact Finset.mem_erase.2 ⟨hcq, Finset.mem_univ _⟩
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 this
          exact Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, hc.2⟩, rfl⟩
      have hP₂card : P₂.card = n - NA.card := by
        rw [← (hM₂.subset (Finset.filter_subset _ _)).card_image_snd, hP₂snd,
          Finset.card_univ_diff]
        simp
      -- the union is a perfect matching inside `S`
      have hdisj : Disjoint P₁ P₂ := by
        rw [Finset.disjoint_left]
        intro z hz hz'
        exact hP₂row z hz' (Finset.mem_filter.1 hz).2
      have hUS : P₁ ∪ P₂ ⊆ S := by
        intro z hz
        rcases Finset.mem_union.1 hz with h | h
        · exact hM₁S (Finset.mem_filter.1 h).1
        · exact hM₂S (Finset.mem_filter.1 h).1
      have hUmatch : IsMatching (P₁ ∪ P₂) := by
        intro z hz w hw hzw
        have key : ∀ z ∈ P₁, ∀ w ∈ P₂, z.1 ≠ w.1 ∧ z.2 ≠ w.2 := by
          intro z hz w hw
          have h1 : z.1 ∈ A := (Finset.mem_filter.1 hz).2
          have h2 : w.1 ∉ A := hP₂row w hw
          have h3 : z.2 ∈ NA := hP₁snd (Finset.mem_image.2 ⟨z, hz, rfl⟩)
          have h4 : w.2 ∉ NA := (Finset.mem_filter.1 hw).2
          exact ⟨fun h => h2 (h ▸ h1), fun h => h4 (h ▸ h3)⟩
        rcases Finset.mem_union.1 hz with h | h <;> rcases Finset.mem_union.1 hw with h' | h'
        · exact (hM₁.subset (Finset.filter_subset _ _)) z h w h' hzw
        · rcases hzw with hzw | hzw
          · exact absurd hzw (key z h w h').1
          · exact absurd hzw (key z h w h').2
        · rcases hzw with hzw | hzw
          · exact absurd hzw.symm (key w h' z h).1
          · exact absurd hzw.symm (key w h' z h).2
        · exact (hM₂.subset (Finset.filter_subset _ _)) z h w h' hzw
      have hcardU : (P₁ ∪ P₂).card = n := by
        rw [Finset.card_union_of_disjoint hdisj, hP₁card, hP₂card, ← hcardNA]
        have : NA.card ≤ n := by
          simpa using Finset.card_le_univ NA
        omega
      have := le_nu hUS hUmatch
      omega
    · rw [Finset.erase_eq_of_notMem hqNA]
      exact hAle
  obtain ⟨g, hginj, hg⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun r : {r : Fin n // r ≠ p} => (nbrs S r.1).erase q)).1 hall
  set M : Finset (Cell n) := Finset.univ.image (fun r : {r : Fin n // r ≠ p} => ((r : Fin n), g r))
    with hM
  have hMinj : Function.Injective (fun r : {r : Fin n // r ≠ p} => ((r : Fin n), g r)) := by
    intro a b h
    exact Subtype.ext (congrArg Prod.fst h)
  have hMcard : M.card = n - 1 := by
    rw [hM, Finset.card_image_of_injective _ hMinj]
    simp [Fintype.card_subtype_compl]
  have hMmem : ∀ z ∈ M, ∃ r : {r : Fin n // r ≠ p}, z = ((r : Fin n), g r) := by
    intro z hz
    obtain ⟨r, _, hr⟩ := Finset.mem_image.1 hz
    exact ⟨r, hr.symm⟩
  have hMS : M ⊆ S := by
    intro z hz
    obtain ⟨r, rfl⟩ := hMmem z hz
    exact mem_nbrs.1 (Finset.mem_of_mem_erase (hg r))
  have hMmatch : IsMatching M := by
    intro z hz w hw h
    obtain ⟨a, rfl⟩ := hMmem z hz
    obtain ⟨b, rfl⟩ := hMmem w hw
    have hab : a = b := by
      rcases h with h | h
      · exact Subtype.ext h
      · exact hginj h
    rw [hab]
  have hrowp : ∀ z ∈ M, z.1 ≠ p := by
    intro z hz
    obtain ⟨r, rfl⟩ := hMmem z hz
    exact r.2
  have hcolq : ∀ z ∈ M, z.2 ≠ q := by
    intro z hz
    obtain ⟨r, rfl⟩ := hMmem z hz
    exact Finset.ne_of_mem_erase (hg r)
  have hpq : (p, q) ∉ M := fun h => hrowp _ h rfl
  have hins : IsMatching (insert (p, q) M) := by
    intro z hz w hw h
    rcases Finset.mem_insert.1 hz with rfl | hz' <;> rcases Finset.mem_insert.1 hw with rfl | hw'
    · rfl
    · rcases h with h | h
      · exact absurd h.symm (hrowp w hw')
      · exact absurd h.symm (hcolq w hw')
    · rcases h with h | h
      · exact absurd h (hrowp z hz')
      · exact absurd h (hcolq z hz')
    · exact hMmatch z hz' w hw' h
  have hcardins : (insert (p, q) M).card = n := by
    rw [Finset.card_insert_of_notMem hpq, hMcard]
    have : 1 ≤ n := Fin.pos p
    omega
  have hsub : insert (p, q) M ⊆ insert (p, q) S := Finset.insert_subset_insert _ hMS
  have h1 := le_nu hsub hins
  have h2 := nu_le (insert (p, q) S)
  unfold Completes
  omega

/-- **Lemma 1** (threat structure) of `main.tex`: if `ν(S) = n - 1`, then the set of
cells completing `S` is exactly the rectangle `D_R × D_C`, where `D_R` (resp. `D_C`) is the set
of rows (resp. columns) exposed by some maximum matching of `S`. -/
theorem threat_structure {S : Finset (Cell n)} (hS : nu S + 1 = n) :
    {f : Cell n | Completes f S} = ExposedRows S ×ˢ ExposedCols S := by
  ext f
  constructor
  · intro hf
    exact exposed_of_completes hS hf
  · rintro ⟨h1, h2⟩
    have h := completes_of_exposed hS h1 h2
    simpa using h

/-- **Lemma 1** of `main.tex`, in `iff` form. -/
theorem completes_iff {S : Finset (Cell n)} (hS : nu S + 1 = n) (f : Cell n) :
    Completes f S ↔ f.1 ∈ ExposedRows S ∧ f.2 ∈ ExposedCols S := by
  constructor
  · exact exposed_of_completes hS
  · rintro ⟨h1, h2⟩
    have h := completes_of_exposed hS h1 h2
    simpa using h

/-- Last clause of **Lemma 1** of `main.tex`: if `ν(S) ≤ n - 2`, no single cell
completes `S`, because adding one cell raises `ν` by at most `1`. -/
theorem not_completes_of_nu_add_two_le {S : Finset (Cell n)} (hS : nu S + 2 ≤ n) (f : Cell n) :
    ¬ Completes f S := by
  intro hf
  have := nu_insert_le f S
  rw [Completes] at hf
  omega

/-- First remark after Lemma 1 of `main.tex`: the rectangle `D_R × D_C` is automatically
disjoint from `S`, so no completing cell is already occupied by the owner of `S`. -/
theorem notMem_of_mem_exposed {S : Finset (Cell n)} (hS : nu S + 1 = n) {p q : Fin n}
    (hp : p ∈ ExposedRows S) (hq : q ∈ ExposedCols S) : (p, q) ∉ S := by
  intro hmem
  have h := completes_of_exposed hS hp hq
  rw [Completes, Finset.insert_eq_self.2 hmem] at h
  omega

/-! ### Corollary 2 (tempo) -/

/-- **Corollary 2** (tempo) of `main.tex`, first clause: a player holding fewer than
`n - 1` stones has `ν ≤ n - 2` and hence no threat. -/
theorem no_threat_of_card_lt {S : Finset (Cell n)} (hS : S.card + 1 < n) (f : Cell n) :
    ¬ Completes f S := by
  refine not_completes_of_nu_add_two_le ?_ f
  have := nu_le_card S
  omega

/-- **Corollary 2** (tempo) of `main.tex`, second clause: a player holding fewer than `n`
stones has not won. -/
theorem not_hasTransversal_of_card_lt {S : Finset (Cell n)} (hS : S.card < n) :
    ¬ HasTransversal S := by
  intro h
  have := nu_le_card S
  rw [HasTransversal] at h
  omega

/-- The matching number of a matching is its own cardinality. -/
theorem nu_of_isMatching {M : Finset (Cell n)} (hM : IsMatching M) : nu M = M.card :=
  le_antisymm (nu_le_card M) (le_nu (Finset.Subset.refl M) hM)

/-- **Corollary 2** (tempo) of `main.tex`, third clause: if a player's set consists
exactly of a matching `M` of size `n - 1` missing row `b` and column `d`, then `D_R = {b}`,
`D_C = {d}` and `(b, d)` is the unique completing cell. -/
theorem tempo_unique_completing {M : Finset (Cell n)} {b d : Fin n} (hM : IsMatching M)
    (hcard : M.card + 1 = n) (hb : ∀ z ∈ M, z.1 ≠ b) (hd : ∀ z ∈ M, z.2 ≠ d) :
    ExposedRows M = {b} ∧ ExposedCols M = {d} ∧ {f : Cell n | Completes f M} = {(b, d)} := by
  have hnu : nu M + 1 = n := by rw [nu_of_isMatching hM]; exact hcard
  have hrows : M.image Prod.fst = Finset.univ.erase b := image_fst_eq_erase hM hcard hb
  have hcols : M.image Prod.snd = Finset.univ.erase d := image_snd_eq_erase hM hcard hd
  have hR : ExposedRows M = {b} := by
    ext r
    constructor
    · rintro ⟨M', hM'S, hM'match, hM'card, hM'r⟩
      have : M' = M := by
        apply Finset.eq_of_subset_of_card_le hM'S
        omega
      subst this
      by_contra hrb
      have : r ∈ M'.image Prod.fst := by
        rw [hrows]
        exact Finset.mem_erase.2 ⟨hrb, Finset.mem_univ _⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 this
      exact hM'r z hz rfl
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨M, Finset.Subset.refl M, hM, by omega, hb⟩
  have hC : ExposedCols M = {d} := by
    ext c
    constructor
    · rintro ⟨M', hM'S, hM'match, hM'card, hM'c⟩
      have : M' = M := by
        apply Finset.eq_of_subset_of_card_le hM'S
        omega
      subst this
      by_contra hcd
      have : c ∈ M'.image Prod.snd := by
        rw [hcols]
        exact Finset.mem_erase.2 ⟨hcd, Finset.mem_univ _⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 this
      exact hM'c z hz rfl
    · intro hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact ⟨M, Finset.Subset.refl M, hM, by omega, hd⟩
  refine ⟨hR, hC, ?_⟩
  rw [threat_structure hnu, hR, hC]
  ext f
  simp [Prod.ext_iff]

end Transversal
