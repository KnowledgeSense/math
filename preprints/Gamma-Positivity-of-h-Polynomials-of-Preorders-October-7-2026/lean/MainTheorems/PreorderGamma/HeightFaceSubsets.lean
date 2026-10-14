import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma

open Module
open scoped BigOperators Classical

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T]

omit [Fintype I] [DecidableEq I] [Fintype T] in
theorem affine_independent_nonzero_level (V : T → I → ℝ)
    (hV : AffineIndependent ℝ V) (l : (I → ℝ) →ₗ[ℝ] ℝ)
    (m : ℝ) (hm : m ≠ 0) (hlevel : ∀ t, l (V t) = m) :
    LinearIndependent ℝ V := by
  apply linearIndependent_iff'.mpr
  intro F c hc t ht
  have hsum : (∑ s ∈ F, c s) * m = 0 := by
    have h := congrArg l hc
    simpa only [map_sum, map_smul, smul_eq_mul, hlevel, map_zero,
      Finset.sum_mul] using h
  exact hV.eq_zero_of_sum_eq_zero ((mul_eq_zero.mp hsum).resolve_right hm) hc t ht

omit [DecidableEq I] in
theorem real_column_basis_extension (V : T → I → ℝ) (S : Set T)
    (hS : LinearIndepOn ℝ V S) (hspan : Submodule.span ℝ (Set.range V) = ⊤) :
    ∃ f : I → T, Function.Injective f ∧ S ⊆ Set.range f ∧ LinearIndependent ℝ (V ∘ f) := by
  obtain ⟨B, _, hSB, hspanB, hlin⟩ :=
    exists_linearIndepOn_extension hS (Set.subset_univ S)
  have hfamily : LinearIndependent ℝ (fun t : B => V t.val) := hlin
  have hrange : Set.range (fun t : B => V t.val) = V '' B := by
    ext x
    simp
  have hfull : ⊤ ≤ Submodule.span ℝ (Set.range (fun t : B => V t.val)) := by
    rw [hrange, ← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    exact hspanB (by simpa only [Set.image_univ] using hx)
  let b : Basis B ℝ (I → ℝ) := Basis.mk hfamily hfull
  have hcard : Fintype.card B = Fintype.card I := by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_fintype_fun_eq_card ℝ
  let e : B ≃ I := Fintype.equivOfCardEq hcard
  refine ⟨fun i => (e.symm i).val, Subtype.val_injective.comp e.symm.injective, ?_, ?_⟩
  · intro t ht
    refine ⟨e ⟨t, hSB ht⟩, ?_⟩
    simp only [e.symm_apply_apply]
  · exact hfamily.comp e.symm e.symm.injective

omit [DecidableEq I] in
theorem independent_subset_direction (V : T → I → ℝ) (F S : Set T)
    (hF : LinearIndepOn ℝ V F) (hspan : Submodule.span ℝ (Set.range V) = ⊤) :
    ∃ d : (I → ℝ) →ₗ[ℝ] ℝ,
      ∀ t ∈ F, d (V t) = if t ∈ S then 0 else -1 := by
  obtain ⟨f, _, hsub, hlin⟩ := real_column_basis_extension V F hF hspan
  let b : Basis I ℝ (I → ℝ) := basisOfPiSpaceOfLinearIndependent hlin
  have hb : ∀ i, b i = V (f i) := fun i =>
    congrFun (coe_basisOfPiSpaceOfLinearIndependent hlin) i
  let c : I → ℝ := fun i => if f i ∈ S then 0 else -1
  refine ⟨b.constr ℝ c, ?_⟩
  intro t ht
  obtain ⟨i, hi⟩ := hsub ht
  have hbi : b i = V t := (hb i).trans (congrArg V hi)
  rw [← hbi, Basis.constr_basis]
  simp only [c, hi]

omit [Fintype I] [DecidableEq I] [Fintype T] in
theorem finite_positive_lower_bound (F : Finset T) (b : T → ℝ)
    (hb : ∀ t ∈ F, 0 < b t) : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ F, ε < b t := by
  revert hb
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, by norm_num, by simp⟩
  | @insert t F ht ih =>
    intro hb
    obtain ⟨ε, hε, hbound⟩ := ih (fun s hs => hb s (Finset.mem_insert_of_mem hs))
    have htpos : 0 < b t := hb t (Finset.mem_insert_self _ _)
    refine ⟨min (b t / 2) ε, lt_min (by linarith) hε, ?_⟩
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact (min_le_left _ _).trans_lt (by linarith)
    · exact (min_le_right _ _).trans_lt (hbound s hs)

omit [DecidableEq I] in
theorem height_face_subset_support (V : T → I → ℝ) (height : T → ℝ)
    (F S : Set T) (hF : LinearIndepOn ℝ V F) (hSF : S ⊆ F)
    (hspan : Submodule.span ℝ (Set.range V) = ⊤)
    (l : (I → ℝ) →ₗ[ℝ] ℝ) (hbound : ∀ t, l (V t) ≤ height t)
    (htight : ∀ t, t ∈ F ↔ l (V t) = height t) :
    ∃ l' : (I → ℝ) →ₗ[ℝ] ℝ,
      (∀ t, l' (V t) ≤ height t) ∧ (∀ t, t ∈ S ↔ l' (V t) = height t) := by
  obtain ⟨d, hd⟩ := independent_subset_direction V F S hF hspan
  have hgap : ∀ t, t ∉ F → 0 < height t - l (V t) := by
    intro t ht
    apply sub_pos.mpr
    exact lt_of_le_of_ne (hbound t) (fun he => ht ((htight t).mpr he))
  let b : T → ℝ := fun t =>
    if t ∈ F then 1 else (height t - l (V t)) / (|d (V t)| + 1)
  have hb : ∀ t ∈ (Finset.univ : Finset T), 0 < b t := by
    intro t ht
    by_cases h : t ∈ F
    · simp only [b, ite_eq_left h]
      norm_num
    · simp only [b, ite_eq_right h]
      exact div_pos (hgap t h) (by positivity)
  obtain ⟨ε, hε, hsmall⟩ := finite_positive_lower_bound Finset.univ b hb
  let l' : (I → ℝ) →ₗ[ℝ] ℝ := l + ε • d
  have hl' : ∀ t, l' (V t) = l (V t) + ε * d (V t) := fun t => rfl
  have hexact : ∀ t ∈ S, l' (V t) = height t := by
    intro t ht
    rw [hl', hd t (hSF ht), ite_eq_left ht, mul_zero, add_zero]
    exact (htight t).mp (hSF ht)
  have hstrict : ∀ t, t ∉ S → l' (V t) < height t := by
    intro t ht
    by_cases htF : t ∈ F
    · rw [hl', hd t htF, ite_eq_right ht, (htight t).mp htF]
      linarith
    · have hεt : ε < (height t - l (V t)) / (|d (V t)| + 1) := by
        simpa only [b, ite_eq_right htF] using hsmall t (Finset.mem_univ t)
      have hmul : ε * (|d (V t)| + 1) < height t - l (V t) :=
        (lt_div_iff₀ (by positivity : 0 < |d (V t)| + 1)).mp hεt
      have hle : ε * d (V t) ≤ ε * |d (V t)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      rw [hl']
      nlinarith
  refine ⟨l', ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ S
    · exact (hexact t ht).le
    · exact (hstrict t ht).le
  · intro t
    constructor
    · exact hexact t
    · intro he
      by_contra ht
      exact (hstrict t ht).ne he

omit [DecidableEq I] in
theorem height_face_subset_nonzero_support (V : T → I → ℝ) (height : T → ℝ)
    (F S : Set T) (hF : LinearIndepOn ℝ V F) (hSF : S ⊆ F) (hS : S.Nonempty)
    (hspan : Submodule.span ℝ (Set.range V) = ⊤) (hheight : ∀ t, 0 < height t)
    (l : (I → ℝ) →ₗ[ℝ] ℝ) (hbound : ∀ t, l (V t) ≤ height t)
    (htight : ∀ t, t ∈ F ↔ l (V t) = height t) :
    ∃ l' : (I → ℝ) →ₗ[ℝ] ℝ, l' ≠ 0 ∧
      (∀ t, l' (V t) ≤ height t) ∧ (∀ t, t ∈ S ↔ l' (V t) = height t) := by
  obtain ⟨l', hbound', htight'⟩ := height_face_subset_support V height F S hF hSF hspan
    l hbound htight
  refine ⟨l', ?_, hbound', htight'⟩
  intro hl
  obtain ⟨s, hs⟩ := hS
  have h := (htight' s).mp hs
  rw [hl, LinearMap.zero_apply] at h
  linarith [hheight s]

omit [DecidableEq I] in
theorem affine_support_subset_nonzero (V : T → I → ℝ) (F S : Set T)
    (hF : AffineIndependent ℝ (fun t : F => V t.val)) (hSF : S ⊆ F)
    (hS : S.Nonempty) (hspan : Submodule.span ℝ (Set.range V) = ⊤)
    (l : (I → ℝ) →ₗ[ℝ] ℝ) (m : ℝ) (hm : 0 < m)
    (hbound : ∀ t, l (V t) ≤ m) (htight : ∀ t, t ∈ F ↔ l (V t) = m) :
    ∃ l' : (I → ℝ) →ₗ[ℝ] ℝ, l' ≠ 0 ∧
      (∀ t, l' (V t) ≤ m) ∧ (∀ t, t ∈ S ↔ l' (V t) = m) := by
  have hlin : LinearIndepOn ℝ V F :=
    affine_independent_nonzero_level (fun t : F => V t.val) hF l m hm.ne'
      (fun t => (htight t.val).mp t.property)
  exact height_face_subset_nonzero_support V (fun _ => m) F S hlin hSF hS hspan
    (fun _ => hm) l hbound htight

end ResearchMain.PreorderGamma
