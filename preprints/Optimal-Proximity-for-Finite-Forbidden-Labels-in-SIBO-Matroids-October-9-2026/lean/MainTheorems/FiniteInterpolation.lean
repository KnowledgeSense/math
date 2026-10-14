import MainTheorems.Characters
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

namespace ResearchMain.SIBO

open scoped BigOperators
open Module

/-- On a finite set, a function algebra separating points contains every function. -/
theorem finite_function_algebra_eq_top {ι : Type*} [Fintype ι]
    (B : Subalgebra ℂ (ι → ℂ))
    (hsep : ∀ i j, i ≠ j → ∃ f ∈ B, f i ≠ f j) : B = ⊤ := by
  classical
  have hdelta (a : ι) : (fun x => if x = a then (1 : ℂ) else 0) ∈ B := by
    choose f hf hne using fun b : {x : ι // x ≠ a} => hsep a b b.property.symm
    let p (b : {x : ι // x ≠ a}) : ι → ℂ :=
      fun x => (f b a - f b b)⁻¹ * (f b x - f b b)
    have hp (b : {x : ι // x ≠ a}) : p b ∈ B := by
      exact B.mul_mem (B.algebraMap_mem _) (B.sub_mem (hf b) (B.algebraMap_mem _))
    have hprod : (∏ b : {x : ι // x ≠ a}, p b) ∈ B :=
      B.prod_mem fun b _ => hp b
    have heq : (∏ b : {x : ι // x ≠ a}, p b) =
        fun x => if x = a then (1 : ℂ) else 0 := by
      ext x
      simp only [Finset.prod_apply]
      by_cases hx : x = a
      · subst x
        simp [p, sub_ne_zero.mpr (hne _)]
      · simp only [ite_eq_right_iff.mpr (fun h => (hx h).elim)]
        apply Finset.prod_eq_zero (Finset.mem_univ ⟨x, hx⟩)
        simp [p]
    rwa [heq] at hprod
  apply eq_top_iff.mpr
  intro g _
  have hs : (∑ a : ι, g a • (fun x => if x = a then (1 : ℂ) else 0)) ∈ B :=
    B.sum_mem fun a _ => B.smul_mem (hdelta a) _
  have heq : (∑ a : ι, g a • (fun x => if x = a then (1 : ℂ) else 0)) = g := by
    ext x
    simp [Finset.sum_apply, eq_comm]
  rwa [heq] at hs

variable {A : Type*} [AddCommGroup A]

def evaluationCharacters {ι : Type*} (s : ι → A) : Submonoid (ι → ℂ) where
  carrier := Set.range (fun χ : AddChar A ℂ => fun i => χ (s i))
  one_mem' := ⟨1, rfl⟩
  mul_mem' := by
    rintro f g ⟨χ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨χ * ψ, rfl⟩

/-- Evaluation vectors of complex characters span all functions on a finite set of distinct points. -/
theorem character_evaluation_span {ι : Type*} [Fintype ι]
    (s : ι → A) (hs : Function.Injective s) :
    Submodule.span ℂ (evaluationCharacters s : Set (ι → ℂ)) = ⊤ := by
  let B := Algebra.adjoin ℂ (evaluationCharacters s : Set (ι → ℂ))
  have htop : B = ⊤ := by
    apply finite_function_algebra_eq_top
    intro i j hij
    obtain ⟨χ, hχ⟩ := exists_separating_character (sub_ne_zero.mpr (hs.ne hij))
    refine ⟨fun x => χ (s x), Algebra.subset_adjoin ⟨χ, rfl⟩, ?_⟩
    intro heq
    change χ (s i) = χ (s j) at heq
    apply hχ
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, heq, ← AddChar.map_add_eq_mul]
    simp
  have heq : B.toSubmodule = Submodule.span ℂ (evaluationCharacters s : Set (ι → ℂ)) := by
    dsimp only [B]
    rw [Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rw [← heq, htop]
  rfl

/-- Any prescribed values at `n` distinct points can be interpolated with `n` characters. -/
theorem finite_character_interpolation {ι : Type*} [Fintype ι]
    (s : ι → A) (hs : Function.Injective s) (u : ι → ℂ) :
    ∃ χ : Fin (Fintype.card ι) → AddChar A ℂ,
      ∃ c : Fin (Fintype.card ι) → ℂ,
        ∀ i, (∑ t, c t * χ t (s i)) = u i := by
  classical
  have hspan := character_evaluation_span s hs
  let b := Basis.ofSpan (le_of_eq hspan.symm)
  let _ := FiniteDimensional.fintypeBasisIndex b
  have hcard := (Module.finrank_eq_card_basis b).symm
  rw [Module.finrank_pi] at hcard
  let e := Fintype.equivFinOfCardEq hcard
  have hb : ∀ j, b j ∈ (evaluationCharacters s : Set (ι → ℂ)) := fun j =>
    Basis.ofSpan_subset (le_of_eq hspan.symm) ⟨j, rfl⟩
  choose χ hχ using hb
  refine ⟨fun j => χ (e.symm j), fun j => b.repr u (e.symm j), ?_⟩
  intro i
  have heval := congrFun (b.sum_repr u) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heval
  rw [← heval, ← Equiv.sum_comp e.symm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hχ (e.symm j)]

/-- A forbidden set of size `q` avoiding zero has an annihilator with `q + 1` terms. -/
theorem finite_forbidden_annihilator (T : Finset A) (hzero : 0 ∉ T) :
    ∃ χ : Fin (T.card + 1) → AddChar A ℂ,
      ∃ c : Fin (T.card + 1) → ℂ,
        (∑ j, c j) = 1 ∧ ∀ a ∈ T, (∑ j, c j * χ j a) = 0 := by
  classical
  let S := insert 0 T
  have hcard : Fintype.card S = T.card + 1 := by simp [S, hzero]
  have h := finite_character_interpolation (fun a : S => (a : A))
    Subtype.coe_injective (fun a => if (a : A) = 0 then 1 else 0)
  rw [hcard] at h
  obtain ⟨χ, c, hc⟩ := h
  refine ⟨χ, c, ?_, ?_⟩
  · simpa using hc ⟨0, by simp [S]⟩
  · intro a ha
    have hne : a ≠ 0 := by rintro rfl; exact hzero ha
    simpa [hne] using hc ⟨a, by simp [S, ha]⟩

end ResearchMain.SIBO
