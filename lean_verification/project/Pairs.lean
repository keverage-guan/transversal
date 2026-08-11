import project.Phase1

/-!
# Live rows and the choice of the pair `(r, s)` (Lemmas 4.4–4.6 of `aristotle.tex`)

At ply `2n - 3` X owns exactly the matching `M = nearMatching σ b` of size `n - 1` missing row
`b` and column `d = σ b`, while O owns the `n - 2` stones `F`. This file formalises:

* the notion of a **live** row of §3 (both `(s,d)` and `(b, σ s)` are free);
* inequality (3.1) of `aristotle.tex`: `ℓ ≥ (n-1) - w`;
* **Lemma 4.4** (admissible pair): if `w ≤ n - 3` then X can choose a pair `(r,s)` of distinct
  live rows whose cross cell is free, for either plan;
* **Lemma 4.5** (admissible pair when `w = 0` and `ν(F) = n - 2`);
* **Lemma 4.6** (all cells X needs stay free).
-/

namespace Transversal

open Finset

open scoped Classical

variable {n : ℕ}

/-- A row `s ≠ b` is **live** (§3 of `aristotle.tex`) when the cells `(s, d)` and `(b, σ s)` are
both free at ply `2n-3`. Since X's stones form the matching `M = nearMatching σ b`, which misses
row `b` and column `d = σ b`, these two cells are free exactly when they are not O-stones. -/
def Live (σ : Equiv.Perm (Fin n)) (b : Fin n) (F : Finset (Cell n)) (s : Fin n) : Prop :=
  s ≠ b ∧ (s, σ b) ∉ F ∧ (b, σ s) ∉ F

/-- The set of live rows. -/
noncomputable def liveRows (σ : Equiv.Perm (Fin n)) (b : Fin n) (F : Finset (Cell n)) :
    Finset (Fin n) :=
  (Finset.univ.erase b).filter (fun s => (s, σ b) ∉ F ∧ (b, σ s) ∉ F)

theorem mem_liveRows {σ : Equiv.Perm (Fin n)} {b : Fin n} {F : Finset (Cell n)} {s : Fin n} :
    s ∈ liveRows σ b F ↔ Live σ b F s := by
  simp only [liveRows, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Live]

/-- A cross cell `(r, σ s)` with `r ≠ s` is never an X-stone (§4, proof of Lemma 4.4). -/
theorem cross_notMem_nearMatching {σ : Equiv.Perm (Fin n)} {b r s : Fin n} (hrs : r ≠ s) :
    (r, σ s) ∉ nearMatching σ b := by
  intro h
  exact hrs (σ.injective (mem_nearMatching.1 h).2.symm)

/-- Inequality (3.1) of `aristotle.tex`: the number `ℓ` of live rows satisfies
`ℓ ≥ (n - 1) - w`, because each of the `w` O-stones in row `b` or column `d` kills at most one
row. -/
theorem card_live_ge {σ : Equiv.Perm (Fin n)} {b : Fin n} {F : Finset (Cell n)} :
    (Finset.univ.erase b).card ≤ (liveRows σ b F).card + wParam F b (σ b) := by
  classical
  have hsub : liveRows σ b F ⊆ Finset.univ.erase b := Finset.filter_subset _ _
  have hsplit : ((Finset.univ.erase b) \ liveRows σ b F).card + (liveRows σ b F).card =
      (Finset.univ.erase b).card := Finset.card_sdiff_add_card_eq_card hsub
  have hKle : ((Finset.univ.erase b) \ liveRows σ b F).card ≤ wParam F b (σ b) := by
    rw [wParam]
    refine Finset.card_le_card_of_injOn
      (fun s => if (s, σ b) ∈ F then (s, σ b) else (b, σ s)) ?_ ?_
    · intro s hs
      have hs' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hs)
      have hsb : s ≠ b := (Finset.mem_erase.1 hs'.1).1
      have hkill : (s, σ b) ∈ F ∨ (b, σ s) ∈ F := by
        by_contra hcon
        push_neg at hcon
        exact hs'.2 (mem_liveRows.2 ⟨hsb, hcon.1, hcon.2⟩)
      by_cases hc : (s, σ b) ∈ F
      · show (if (s, σ b) ∈ F then ((s, σ b) : Cell n) else (b, σ s)) ∈ _
        rw [if_pos hc]
        exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hc, Or.inr rfl⟩)
      · show (if (s, σ b) ∈ F then ((s, σ b) : Cell n) else (b, σ s)) ∈ _
        rw [if_neg hc]
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, Or.inl rfl⟩)
        rcases hkill with h | h
        · exact absurd h hc
        · exact h
    · intro s hs t ht hst
      have hs' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hs)
      have ht' := Finset.mem_sdiff.1 (Finset.mem_coe.1 ht)
      have hsb : s ≠ b := (Finset.mem_erase.1 hs'.1).1
      have htb : t ≠ b := (Finset.mem_erase.1 ht'.1).1
      have hst' : (if (s, σ b) ∈ F then ((s, σ b) : Cell n) else (b, σ s)) =
          (if (t, σ b) ∈ F then ((t, σ b) : Cell n) else (b, σ t)) := hst
      by_cases hcs : (s, σ b) ∈ F <;> by_cases hct : (t, σ b) ∈ F
      · rw [if_pos hcs, if_pos hct] at hst'
        exact congrArg Prod.fst hst'
      · rw [if_pos hcs, if_neg hct] at hst'
        exact absurd (congrArg Prod.fst hst') hsb
      · rw [if_neg hcs, if_pos hct] at hst'
        exact absurd (congrArg Prod.fst hst').symm htb
      · rw [if_neg hcs, if_neg hct] at hst'
        exact σ.injective (congrArg Prod.snd hst')
  omega

/-- **Lemma 4.4** (admissible pair) of `aristotle.tex`: if `w ≤ n - 3`, then X can choose an
ordered pair `(r, s)` of distinct live rows whose cross cell `(r, σ s)` is free, i.e. neither an
O-stone nor an X-stone. Exchanging `r` and `s` gives the pair required by plan (ii), whose cross
cell is `(s, σ r)`. -/
theorem exists_admissible_pair {σ : Equiv.Perm (Fin n)} {b : Fin n} {F : Finset (Cell n)}
    (hFcard : F.card + 2 = n) (hw : wParam F b (σ b) + 3 ≤ n) :
    ∃ r s, Live σ b F r ∧ Live σ b F s ∧ r ≠ s ∧
      (r, σ s) ∉ F ∧ (r, σ s) ∉ nearMatching σ b := by
  classical
  have hcarderase : (Finset.univ.erase b).card + 1 = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b)]
    simp only [Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Fin.pos b
    omega
  have hLcard : n ≤ (liveRows σ b F).card + wParam F b (σ b) + 1 := by
    have := card_live_ge (σ := σ) (b := b) (F := F)
    omega
  -- the bad ordered pairs inject into the O-stones outside row `b` and column `d`
  have hBadle :
      ((liveRows σ b F).offDiag.filter (fun z => (z.1, σ z.2) ∈ F)).card ≤
        (F.filter (fun z => ¬ (z.1 = b ∨ z.2 = σ b))).card := by
    refine Finset.card_le_card_of_injOn (fun z => (z.1, σ z.2)) ?_ ?_
    · intro z hz
      have hz' := Finset.mem_filter.1 (Finset.mem_coe.1 hz)
      have hoff := Finset.mem_offDiag.1 hz'.1
      have h1 : z.1 ≠ b := (mem_liveRows.1 hoff.1).1
      have h2 : z.2 ≠ b := (mem_liveRows.1 hoff.2.1).1
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hz'.2, ?_⟩)
      push_neg
      exact ⟨h1, fun h => h2 (σ.injective h)⟩
    · intro z hz z' hz' h
      have h' : ((z.1, σ z.2) : Cell n) = (z'.1, σ z'.2) := h
      rw [Prod.mk.injEq] at h'
      exact Prod.ext h'.1 (σ.injective h'.2)
  have hFfilter : (F.filter (fun z => ¬ (z.1 = b ∨ z.2 = σ b))).card + wParam F b (σ b)
      = F.card := by
    rw [wParam]
    have := Finset.card_filter_add_card_filter_not (s := F) (p := fun z => z.1 = b ∨ z.2 = σ b)
    omega
  -- counting: there are more ordered pairs of distinct live rows than bad ones
  set l := (liveRows σ b F).card with hl
  set w := wParam F b (σ b) with hwdef
  set k := (F.filter (fun z => ¬ (z.1 = b ∨ z.2 = σ b))).card with hk
  have hk1 : 1 ≤ k := by omega
  have hkl : k + 1 ≤ l := by omega
  have hoff : (liveRows σ b F).offDiag.card = l * l - l := Finset.offDiag_card _
  have hmul : (k + 1) * k ≤ l * (l - 1) := Nat.mul_le_mul hkl (by omega)
  have hll : l * (l - 1) = l * l - l := by
    cases' Nat.eq_zero_or_pos l with h h
    · simp [h]
    · rw [Nat.mul_sub, Nat.mul_one]
  have h2k : 2 * k ≤ (k + 1) * k := Nat.mul_le_mul_right _ (by omega)
  have hkey : ((liveRows σ b F).offDiag.filter (fun z => (z.1, σ z.2) ∈ F)).card
      < (liveRows σ b F).offDiag.card := by omega
  obtain ⟨z, hz, hz'⟩ := Finset.exists_mem_notMem_of_card_lt_card hkey
  have hoffz := Finset.mem_offDiag.1 hz
  refine ⟨z.1, z.2, mem_liveRows.1 hoffz.1, mem_liveRows.1 hoffz.2.1, hoffz.2.2, ?_,
    cross_notMem_nearMatching hoffz.2.2⟩
  intro hmem
  exact hz' (Finset.mem_filter.2 ⟨hz, hmem⟩)

/-- **Lemma 4.5** (admissible pair when `w = 0` and `ν(F) = n - 2`) of `aristotle.tex`. Here `e`
is X's last Phase-1 row `u_a` and `F` is a perfect matching of `A × B`, so that `F` misses the
rows `b, e` and the columns `d = σ b`, `σ e = v_c`. Then every row `≠ b` is live, some live
`r ∉ {b, e}` exists, and for the pair `(r, s) = (r, e)` the cross cell `(r, σ e)` is
automatically free. -/
theorem pair_of_w_zero {σ : Equiv.Perm (Fin n)} {b e : Fin n} (hbe : e ≠ b) (hn : 4 ≤ n)
    {F : Finset (Cell n)} (hFrow : ∀ z ∈ F, z.1 ≠ b ∧ z.1 ≠ e)
    (hFcol : ∀ z ∈ F, z.2 ≠ σ b ∧ z.2 ≠ σ e) :
    Live σ b F e ∧ ∃ r, Live σ b F r ∧ r ≠ e ∧
      (r, σ e) ∉ F ∧ (r, σ e) ∉ nearMatching σ b := by
  have hlive : ∀ s : Fin n, s ≠ b → Live σ b F s := by
    intro s hs
    refine ⟨hs, ?_, ?_⟩
    · intro hmem
      exact (hFcol _ hmem).1 rfl
    · intro hmem
      exact (hFrow _ hmem).1 rfl
  refine ⟨hlive e hbe, ?_⟩
  -- there are at least two rows different from `b`, so some `r ∉ {b, e}` exists
  obtain ⟨r, hr⟩ : ((Finset.univ.erase b).erase e).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨hbe, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ b)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hre : r ≠ e := (Finset.mem_erase.1 hr).1
  have hrb : r ≠ b := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hr)).1
  refine ⟨r, hlive r hrb, hre, ?_, cross_notMem_nearMatching hre⟩
  intro hmem
  exact (hFcol _ hmem).2 rfl

/-- **Lemma 4.6** (all cells X needs stay free) of `aristotle.tex`, for plan (i): the cells
`(b,d) , (r,d) , (b,σ r) , (s,d) , (b,σ s) , (r,σ s)` occurring between plies `2n-3` and `2n+3`
are pairwise distinct, so each cell X's plan requires is still free when X needs it. -/
theorem plan_i_cells_distinct {σ : Equiv.Perm (Fin n)} {b r s : Fin n}
    (hr : r ≠ b) (hs : s ≠ b) (hrs : r ≠ s) :
    ((b, σ r) ≠ ((b, σ b) : Cell n)) ∧
      ((s, σ b) ≠ ((b, σ b) : Cell n) ∧ (s, σ b) ≠ ((r, σ b) : Cell n) ∧
        (s, σ b) ≠ ((b, σ r) : Cell n)) ∧
      ((b, σ s) ≠ ((b, σ b) : Cell n) ∧ (b, σ s) ≠ ((r, σ b) : Cell n) ∧
        (b, σ s) ≠ ((b, σ r) : Cell n) ∧ (b, σ s) ≠ ((s, σ b) : Cell n)) ∧
      ((r, σ s) ≠ ((b, σ b) : Cell n) ∧ (r, σ s) ≠ ((r, σ b) : Cell n) ∧
        (r, σ s) ≠ ((b, σ r) : Cell n) ∧ (r, σ s) ≠ ((s, σ b) : Cell n)) := by
  have hcol : ∀ x y : Fin n, x ≠ y → σ x ≠ σ y := fun x y h h' => h (σ.injective h')
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;>
    first
      | exact hr (congrArg Prod.fst h)
      | exact hs (congrArg Prod.fst h)
      | exact hrs (congrArg Prod.fst h)
      | exact hr (congrArg Prod.fst h).symm
      | exact hs (congrArg Prod.fst h).symm
      | exact hrs (congrArg Prod.fst h).symm
      | exact hcol _ _ hr (congrArg Prod.snd h)
      | exact hcol _ _ hs (congrArg Prod.snd h)
      | exact hcol _ _ hrs (congrArg Prod.snd h)
      | exact hcol _ _ hr (congrArg Prod.snd h).symm
      | exact hcol _ _ hs (congrArg Prod.snd h).symm
      | exact hcol _ _ hrs (congrArg Prod.snd h).symm

end Transversal
