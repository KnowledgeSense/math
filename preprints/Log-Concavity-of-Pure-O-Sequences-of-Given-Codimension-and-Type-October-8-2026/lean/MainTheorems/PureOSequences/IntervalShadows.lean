import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace ResearchMain.PureOSequences

def lowerShadow (n : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter fun x => x ∈ U ∨ x + 1 ∈ U

def runStarts (U : Finset ℕ) : Finset ℕ :=
  U.filter fun x => x = 0 ∨ x - 1 ∉ U

def boundaryCount (n : ℕ) (U : Finset ℕ) : ℕ :=
  (if 0 ∈ U then 1 else 0) + (if n ∈ U then 1 else 0)

@[simp] theorem mem_lowerShadow {n x : ℕ} {U : Finset ℕ} :
    x ∈ lowerShadow n U ↔ x < n ∧ (x ∈ U ∨ x + 1 ∈ U) := by
  simp [lowerShadow]

@[simp] theorem mem_runStarts {x : ℕ} {U : Finset ℕ} :
    x ∈ runStarts U ↔ x ∈ U ∧ (x = 0 ∨ x - 1 ∉ U) := by simp [runStarts]

theorem lowerShadow_card (n : ℕ) (U : Finset ℕ) (hU : U ⊆ Finset.range (n + 1)) :
    (lowerShadow n U).card + U.card + boundaryCount n U = U.card + U.card +
      (runStarts U).card := by
  let L := U \ {n}
  let R := (U \ {0}).image (fun x => x - 1)
  have hpred : ∀ x, x ∈ R ↔ x + 1 ∈ U := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      have hmem := (Finset.mem_sdiff.mp hy).1
      have hy0 : y ≠ 0 := by simpa using (Finset.mem_sdiff.mp hy).2
      have hyx : y = x + 1 := by omega
      exact hyx ▸ hmem
    · intro hx
      exact Finset.mem_image.mpr
        ⟨x + 1, Finset.mem_sdiff.mpr ⟨hx, by simp⟩, by omega⟩
  have hshadow : lowerShadow n U = L ∪ R := by
    ext x
    simp only [mem_lowerShadow, Finset.mem_union, L, Finset.mem_sdiff,
      Finset.mem_singleton, hpred]
    have hbound : x ∈ U → x ≤ n := fun hx => Nat.le_of_lt_succ (Finset.mem_range.mp (hU hx))
    have hbound1 : x + 1 ∈ U → x + 1 ≤ n := fun hx =>
      Nat.le_of_lt_succ (Finset.mem_range.mp (hU hx))
    constructor
    · rintro ⟨hx, hmem⟩
      rcases hmem with h | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr h
    · rintro (⟨h, hne⟩ | h)
      · exact ⟨by have := hbound h; omega, Or.inl h⟩
      · exact ⟨by have := hbound1 h; omega, Or.inr h⟩
  have hL : L.card + (if n ∈ U then 1 else 0) = U.card := by
    have h := Finset.card_sdiff_add_card_inter U {n}
    simpa only [L, Finset.inter_singleton, apply_ite Finset.card, Finset.card_singleton,
      Finset.card_empty] using h
  have hinj : Set.InjOn (fun x : ℕ => x - 1) (↑(U \ {0} : Finset ℕ)) := by
    intro x hx y hy heq
    have hx0 : x ≠ 0 := by simpa using (Finset.mem_sdiff.mp hx).2
    have hy0 : y ≠ 0 := by simpa using (Finset.mem_sdiff.mp hy).2
    dsimp only at heq
    omega
  have hR : R.card + (if 0 ∈ U then 1 else 0) = U.card := by
    dsimp only [R]
    rw [Finset.card_image_of_injOn hinj]
    have h := Finset.card_sdiff_add_card_inter U {0}
    simpa only [Finset.inter_singleton, apply_ite Finset.card, Finset.card_singleton,
      Finset.card_empty] using h
  have hinter : (L ∩ R).card = (U \ runStarts U).card := by
    apply Finset.card_bij (fun x _ => x + 1)
    · intro x hx
      obtain ⟨hxl, hxr⟩ := Finset.mem_inter.mp hx
      have hxU := (Finset.mem_sdiff.mp hxl).1
      refine Finset.mem_sdiff.mpr ⟨(hpred x).mp hxr, ?_⟩
      intro h
      have hs := (mem_runStarts.mp h).2
      rcases hs with hs | hs
      · omega
      · exact hs (by simpa only [Nat.add_sub_cancel] using hxU)
    · intro x _ y _ heq
      omega
    · intro y hy
      obtain ⟨hyU, hynostart⟩ := Finset.mem_sdiff.mp hy
      have hy0 : y ≠ 0 := by intro h; exact hynostart (mem_runStarts.mpr ⟨hyU, Or.inl h⟩)
      have hypred : y - 1 ∈ U := by
        by_contra h
        exact hynostart (mem_runStarts.mpr ⟨hyU, Or.inr h⟩)
      have hybound := Finset.mem_range.mp (hU hyU)
      refine ⟨y - 1, Finset.mem_inter.mpr ⟨?_, ?_⟩, by omega⟩
      · exact Finset.mem_sdiff.mpr ⟨hypred, by simp only [Finset.mem_singleton]; omega⟩
      · apply (hpred _).mpr
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ y)] using hyU
  have hstarts : (U \ runStarts U).card + (runStarts U).card = U.card := by
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hunion := Finset.card_union_add_card_inter L R
  rw [← hshadow, hinter] at hunion
  unfold boundaryCount
  omega

theorem lowerShadow_runStarts_le (n : ℕ) (U : Finset ℕ) :
    (runStarts (lowerShadow n U)).card ≤ (runStarts U).card := by
  let f := fun x : ℕ => if x = 0 ∧ 0 ∈ U then 0 else x + 1
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    obtain ⟨hs, hstart⟩ := mem_runStarts.mp hx
    obtain ⟨hxn, hmem⟩ := mem_lowerShadow.mp hs
    by_cases hx0 : x = 0
    · subst x
      by_cases h0 : 0 ∈ U
      · simp only [f, ite_eq_left (And.intro rfl h0)]
        exact mem_runStarts.mpr ⟨h0, Or.inl rfl⟩
      · simp only [f, h0, and_false, ite_false, zero_add]
        have h1 : 1 ∈ U := by simpa only [h0, false_or, zero_add] using hmem
        exact mem_runStarts.mpr ⟨h1, Or.inr (by simpa using h0)⟩
    · have hprev : x - 1 ∉ lowerShadow n U := hstart.resolve_left hx0
      have hxnot : x ∉ U := by
        intro hxU
        apply hprev
        have heq : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
        exact mem_lowerShadow.mpr ⟨by omega, Or.inr (heq.symm ▸ hxU)⟩
      have hxnext := hmem.resolve_left hxnot
      have hf : f x = x + 1 := by simp only [f, hx0, false_and, ite_false]
      rw [hf]
      exact mem_runStarts.mpr ⟨hxnext, Or.inr (by simpa using hxnot)⟩
  · intro x _ y _ heq
    dsimp [f] at heq
    split_ifs at heq <;> omega

theorem lowerShadow_boundary_le (n : ℕ) (U : Finset ℕ) (hn : 1 ≤ n) :
    boundaryCount n U ≤ boundaryCount (n - 1) (lowerShadow n U) := by
  have hzero : 0 ∈ U → 0 ∈ lowerShadow n U := fun h =>
    mem_lowerShadow.mpr ⟨by omega, Or.inl h⟩
  have hlast : n ∈ U → n - 1 ∈ lowerShadow n U := fun h =>
    mem_lowerShadow.mpr ⟨by omega, Or.inr (by simpa only [Nat.sub_add_cancel hn] using h)⟩
  unfold boundaryCount
  split_ifs <;> simp_all

theorem iterated_shadow_concave (n : ℕ) (U : Finset ℕ)
    (hU : U ⊆ Finset.range (n + 1)) (hn : 2 ≤ n) :
    (lowerShadow (n - 1) (lowerShadow n U)).card + U.card ≤
      2 * (lowerShadow n U).card := by
  have hbound : lowerShadow n U ⊆ Finset.range n := Finset.filter_subset _ _
  have hbound' : lowerShadow n U ⊆ Finset.range (n - 1 + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hbound
  have h1 := lowerShadow_card n U hU
  have h2 := lowerShadow_card (n - 1) (lowerShadow n U) hbound'
  have hr := lowerShadow_runStarts_le n U
  have hb := lowerShadow_boundary_le n U (by omega)
  omega

end ResearchMain.PureOSequences
