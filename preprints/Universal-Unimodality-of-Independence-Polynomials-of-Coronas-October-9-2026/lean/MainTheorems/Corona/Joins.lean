import MainTheorems.Corona.Basic
import Mathlib.Combinatorics.SimpleGraph.Sum

namespace ResearchMain.Corona

open Classical Polynomial

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def join (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => True
  symm.symm := by
    rintro (u | u) (v | v) h
    · exact h.symm
    · trivial
    · trivial
    · exact h.symm
  loopless.irrefl := by
    rintro (u | u)
    · exact G.irrefl
    · exact H.irrefl

omit [Fintype V] [Fintype W] in
theorem sum_independent (G : SimpleGraph V) (H : SimpleGraph W) (R : Finset (V ⊕ W)) :
    (G.sum H).IsIndepSet (R : Set (V ⊕ W)) ↔
      G.IsIndepSet (R.toLeft : Set V) ∧ H.IsIndepSet (R.toRight : Set W) := by
  simp only [independent_iff]
  constructor
  · intro h
    exact ⟨fun u hu v hv => h (.inl u) (Finset.mem_toLeft.mp hu)
      (.inl v) (Finset.mem_toLeft.mp hv),
      fun u hu v hv => h (.inr u) (Finset.mem_toRight.mp hu)
        (.inr v) (Finset.mem_toRight.mp hv)⟩
  · rintro ⟨hG, hH⟩ (u | u) hu (v | v) hv h
    · exact hG u (Finset.mem_toLeft.mpr hu) v (Finset.mem_toLeft.mpr hv) h
    · simp only [SimpleGraph.sum_adj] at h
    · simp only [SimpleGraph.sum_adj] at h
    · exact hH u (Finset.mem_toRight.mpr hu) v (Finset.mem_toRight.mpr hv) h

omit [Fintype V] [Fintype W] in
theorem join_independent (G : SimpleGraph V) (H : SimpleGraph W) (R : Finset (V ⊕ W)) :
    (join G H).IsIndepSet (R : Set (V ⊕ W)) ↔
      G.IsIndepSet (R.toLeft : Set V) ∧ H.IsIndepSet (R.toRight : Set W) ∧
      (R.toLeft = ∅ ∨ R.toRight = ∅) := by
  simp only [independent_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact fun u hu v hv => h (.inl u) (Finset.mem_toLeft.mp hu)
        (.inl v) (Finset.mem_toLeft.mp hv)
    · exact fun u hu v hv => h (.inr u) (Finset.mem_toRight.mp hu)
        (.inr v) (Finset.mem_toRight.mp hv)
    · by_cases he : R.toLeft = ∅
      · exact Or.inl he
      · right
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr he
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact h (.inl u) (Finset.mem_toLeft.mp hu) (.inr v) (Finset.mem_toRight.mp hv) trivial
  · rintro ⟨hG, hH, he⟩ (u | u) hu (v | v) hv h
    · exact hG u (Finset.mem_toLeft.mpr hu) v (Finset.mem_toLeft.mpr hv) h
    · rcases he with he | he
      · have := Finset.mem_toLeft.mpr hu; rw [he] at this; exact Finset.notMem_empty u this
      · have := Finset.mem_toRight.mpr hv; rw [he] at this; exact Finset.notMem_empty v this
    · rcases he with he | he
      · have := Finset.mem_toLeft.mpr hv; rw [he] at this; exact Finset.notMem_empty v this
      · have := Finset.mem_toRight.mpr hu; rw [he] at this; exact Finset.notMem_empty u this
    · exact hH u (Finset.mem_toRight.mpr hu) v (Finset.mem_toRight.mpr hv) h

noncomputable def sumIndependentEquiv (G : SimpleGraph V) (H : SimpleGraph W) :
    ↑(independentSets G) × ↑(independentSets H) ≃ ↑(independentSets (G.sum H)) where
  toFun ST := ⟨ST.1.val.disjSum ST.2.val, (mem_independentSets _ _).mpr (by
    rw [sum_independent, Finset.toLeft_disjSum, Finset.toRight_disjSum]
    exact ⟨(mem_independentSets _ _).mp ST.1.property, (mem_independentSets _ _).mp ST.2.property⟩)⟩
  invFun R :=
    let hR := (sum_independent G H R.val).mp ((mem_independentSets _ _).mp R.property)
    (⟨R.val.toLeft, (mem_independentSets _ _).mpr hR.1⟩,
      ⟨R.val.toRight, (mem_independentSets _ _).mpr hR.2⟩)
  left_inv ST := by
    apply Prod.ext <;> apply Subtype.ext
    · exact Finset.toLeft_disjSum
    · exact Finset.toRight_disjSum
  right_inv R := by
    apply Subtype.ext
    exact Finset.toLeft_disjSum_toRight

theorem independencePolynomial_sum (G : SimpleGraph V) (H : SimpleGraph W) :
    independencePolynomial (G.sum H) = independencePolynomial G * independencePolynomial H := by
  have he := Fintype.sum_equiv (sumIndependentEquiv G H)
    (fun ST => (X : ℝ[X]) ^ ST.1.val.card * X ^ ST.2.val.card)
    (fun R => (X : ℝ[X]) ^ R.val.card) (by
      intro ST
      change X ^ ST.1.val.card * X ^ ST.2.val.card = X ^ (ST.1.val.disjSum ST.2.val).card
      rw [Finset.card_disjSum, pow_add])
  rw [Finset.sum_coe_sort (independentSets (G.sum H)) (fun R => (X : ℝ[X]) ^ R.card)] at he
  rw [independencePolynomial, ← he, Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum (f := fun S : ↑(independentSets G) => (X : ℝ[X]) ^ S.val.card)
    (g := fun S : ↑(independentSets H) => (X : ℝ[X]) ^ S.val.card)]
  rw [Finset.sum_coe_sort (independentSets G) (fun S => (X : ℝ[X]) ^ S.card),
    Finset.sum_coe_sort (independentSets H) (fun S => (X : ℝ[X]) ^ S.card)]
  rfl

theorem independencePolynomial_join (G : SimpleGraph V) (H : SimpleGraph W) :
    independencePolynomial (join G H) = independencePolynomial G + independencePolynomial H - 1 := by
  let L := (independentSets G).image (fun S => S.disjSum (∅ : Finset W))
  let R := (independentSets H).image (fun T => (∅ : Finset V).disjSum T)
  have hsets : independentSets (join G H) = L ∪ R := by
    ext S
    rw [mem_independentSets, join_independent, Finset.mem_union]
    constructor
    · rintro ⟨hG, hH, he⟩
      rcases he with he | he
      · right
        exact Finset.mem_image.mpr ⟨S.toRight, (mem_independentSets _ _).mpr hH, by
          rw [← he]
          exact Finset.toLeft_disjSum_toRight⟩
      · left
        exact Finset.mem_image.mpr ⟨S.toLeft, (mem_independentSets _ _).mpr hG, by
          rw [← he]
          exact Finset.toLeft_disjSum_toRight⟩
    · rintro (hL | hR)
      · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hL
        simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
        exact ⟨(mem_independentSets _ _).mp hT, independent_empty H, Or.inr trivial⟩
      · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hR
        simp only [Finset.toLeft_disjSum, Finset.toRight_disjSum]
        exact ⟨independent_empty G, (mem_independentSets _ _).mp hT, Or.inl trivial⟩
  have hinter : L ∩ R = {∅} := by
    ext S
    rw [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hL, hR⟩
      obtain ⟨T, _, hT⟩ := Finset.mem_image.mp hL
      obtain ⟨U, _, hU⟩ := Finset.mem_image.mp hR
      have hleft := congrArg Finset.toLeft (hT.trans hU.symm)
      simp only [Finset.toLeft_disjSum] at hleft
      rw [← hT, hleft]
      simp
    · rintro rfl
      constructor
      · exact Finset.mem_image.mpr ⟨∅, (mem_independentSets _ _).mpr (independent_empty G), by simp⟩
      · exact Finset.mem_image.mpr ⟨∅, (mem_independentSets _ _).mpr (independent_empty H), by simp⟩
  have hL : ∑ S ∈ L, (X : ℝ[X]) ^ S.card = independencePolynomial G := by
    rw [Finset.sum_image]
    · simp only [Finset.card_disjSum, Finset.card_empty, add_zero]
      rfl
    · intro S _ T _ hST
      have h := congrArg Finset.toLeft hST
      simpa only [Finset.toLeft_disjSum] using h
  have hR : ∑ S ∈ R, (X : ℝ[X]) ^ S.card = independencePolynomial H := by
    rw [Finset.sum_image]
    · simp only [Finset.card_disjSum, Finset.card_empty, zero_add]
      rfl
    · intro S _ T _ hST
      have h := congrArg Finset.toRight hST
      simpa only [Finset.toRight_disjSum] using h
  have hs := Finset.sum_union_inter (s₁ := L) (s₂ := R) (f := fun S => (X : ℝ[X]) ^ S.card)
  rw [hinter, hL, hR] at hs
  simp only [Finset.sum_singleton, Finset.card_empty, pow_zero] at hs
  unfold independencePolynomial
  rw [hsets]
  exact eq_sub_of_add_eq hs

end ResearchMain.Corona
