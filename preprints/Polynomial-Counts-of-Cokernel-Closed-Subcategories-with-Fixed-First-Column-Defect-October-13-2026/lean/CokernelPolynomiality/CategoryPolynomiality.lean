import CokernelPolynomiality.CategoryEquivalence
import CokernelPolynomiality.PolynomialFormula

noncomputable section
namespace CokernelPolynomiality

/-- Full fixed-defect polynomiality for actual replete full additive,
idempotent-split, cokernel-closed subcategories of finite-dimensional complex
representations of the reverse oriented chain. -/
theorem categoricalFixedDefectPolynomiality :
    ∀ i : ℕ, ∃ P : Polynomial ℚ,
      (∀ n : ℕ, i ≤ n+1 → (categoryCount n (n+1-i) : ℚ)=P.eval (n : ℚ)) ∧
      P.natDegree=2*i ∧ P.coeff (2*i)=(i.factorial : ℚ)⁻¹ := by
  intro i
  obtain ⟨P,hP,hdeg,hcoeff⟩ := fixedDefectPolynomiality i
  exact ⟨P,fun n hn => by rw [categoryCount_eq_r]; exact hP n hn,hdeg,hcoeff⟩

end CokernelPolynomiality
