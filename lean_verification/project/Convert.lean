import project.Rectangle

/-!
# Transversals and near-perfect matchings as permutations

`main.tex` identifies a transversal with a perfect matching of `K_{n,n}`, i.e. with a
permutation of the rows, and it writes any matching `M` of size `n-1` missing row `b` and
column `d` through "the induced bijection `σ : R \ {b} → C \ {d}`" (Lemma 2.3 and §3). This
file supplies the two dictionary lemmas that make those identifications formal.
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- A perfect matching of `K_{n,n}`, i.e. a transversal, is the graph of a permutation
(§1 of `main.tex`, "The board as `K_{n,n}`"). -/
theorem exists_perm_of_perfect {M : Finset (Cell n)} (hM : IsMatching M) (hcard : M.card = n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, (i, σ i) ∈ M := by
  classical
  have hrows : M.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hM.card_image_fst, hcard, Fintype.card_fin]
  have hex : ∀ x : Fin n, ∃ y, ((x, y) : Cell n) ∈ M := by
    intro x
    have hxmem : x ∈ M.image Prod.fst := by rw [hrows]; exact Finset.mem_univ x
    obtain ⟨z, hz, hz1⟩ := Finset.mem_image.1 hxmem
    exact ⟨z.2, by rw [← hz1]; simpa using hz⟩
  refine ⟨Equiv.ofBijective (fun x => Classical.choose (hex x)) ?_, ?_⟩
  · refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    have hx := Classical.choose_spec (hex x)
    have hy := Classical.choose_spec (hex y)
    have : ((x, Classical.choose (hex x)) : Cell n) = (y, Classical.choose (hex y)) :=
      hM _ hx _ hy (Or.inr hxy)
    exact (Prod.mk.injEq _ _ _ _ ▸ this).1
  · intro i
    exact Classical.choose_spec (hex i)

/-- A set of cells contains a transversal exactly when it contains the graph of a permutation.
This is the identification of a transversal with a perfect matching of `K_{n,n}` from §1 of
`main.tex`. -/
theorem hasTransversal_iff_exists_perm {S : Finset (Cell n)} :
    HasTransversal S ↔ ∃ σ : Equiv.Perm (Fin n), ∀ i, (i, σ i) ∈ S := by
  classical
  constructor
  · intro h
    obtain ⟨M, hMS, hM, hMcard⟩ := exists_max_matching S
    obtain ⟨σ, hσ⟩ := exists_perm_of_perfect hM (by rw [hMcard]; exact h)
    exact ⟨σ, fun i => hMS (hσ i)⟩
  · rintro ⟨σ, hσ⟩
    set T : Finset (Cell n) := Finset.univ.image (fun i => ((i, σ i) : Cell n)) with hT
    have hTS : T ⊆ S := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact hσ i
    have hTmatch : IsMatching T := by
      intro p hp q hq hpq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
      rcases hpq with h | h
      · simp only at h
        rw [h]
      · simp only at h
        rw [σ.injective h]
    have hTcard : T.card = n := by
      rw [hT, Finset.card_image_of_injective _ (fun i j h => (Prod.mk.injEq _ _ _ _ ▸ h).1),
        Finset.card_univ, Fintype.card_fin]
    have h1 : n ≤ nu S := by
      have := le_nu hTS hTmatch
      omega
    have h2 := nu_le S
    exact le_antisymm h2 h1

/-- The bijection `σ : R \ {b} → C \ {d}` induced by a matching `M` of size `n-1` missing row
`b` and column `d` (§3 of `main.tex`, and the hypothesis of Lemma 2.3): extending it by
`b ↦ d` exhibits `M` as `nearMatching σ b`. -/
theorem exists_perm_of_matching {M : Finset (Cell n)} {b d : Fin n} (hM : IsMatching M)
    (hcard : M.card + 1 = n) (hb : ∀ z ∈ M, z.1 ≠ b) (hd : ∀ z ∈ M, z.2 ≠ d) :
    ∃ σ : Equiv.Perm (Fin n), σ b = d ∧ M = nearMatching σ b := by
  classical
  have hrows : M.image Prod.fst = Finset.univ.erase b := image_fst_eq_erase hM hcard hb
  have hex : ∀ x : Fin n, x ≠ b → ∃ y, ((x, y) : Cell n) ∈ M := by
    intro x hx
    have hxmem : x ∈ M.image Prod.fst := by
      rw [hrows]; exact Finset.mem_erase.2 ⟨hx, Finset.mem_univ x⟩
    obtain ⟨z, hz, hz1⟩ := Finset.mem_image.1 hxmem
    exact ⟨z.2, by rw [← hz1]; simpa using hz⟩
  set f : Fin n → Fin n := fun x => if hx : x = b then d else Classical.choose (hex x hx)
    with hf
  have hfb : f b = d := by simp [hf]
  have hfmem : ∀ x, x ≠ b → ((x, f x) : Cell n) ∈ M := by
    intro x hx
    have hfx : f x = Classical.choose (hex x hx) := by simp [hf, hx]
    rw [hfx]
    exact Classical.choose_spec (hex x hx)
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = b <;> by_cases hy : y = b
    · rw [hx, hy]
    · subst hx
      rw [hfb] at hxy
      exact absurd hxy.symm (hd _ (hfmem y hy))
    · subst hy
      rw [hfb] at hxy
      exact absurd hxy (hd _ (hfmem x hx))
    · have h := hM _ (hfmem x hx) _ (hfmem y hy) (Or.inr hxy)
      exact (Prod.mk.injEq _ _ _ _ ▸ h).1
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hfb, ?_⟩
  ext z
  simp only [mem_nearMatching, Equiv.ofBijective_apply]
  constructor
  · intro hz
    refine ⟨hb z hz, ?_⟩
    have h := hM _ hz _ (hfmem z.1 (hb z hz)) (Or.inl rfl)
    exact congrArg Prod.snd h
  · rintro ⟨h1, h2⟩
    have h := hfmem z.1 h1
    rw [← h2] at h
    simpa using h

end Transversal
