import MainTheorems.Hypercomb.ExcludedExtension
import MainTheorems.Hypercomb.IncludedExtension

namespace ResearchMain.Hypercomb

open Classical Polynomial

variable {V P T : Type*} [Fintype V] [Fintype P] [Fintype T]
  [DecidableEq V] [DecidableEq P] [DecidableEq T]

theorem excludedPolynomial_extension (H : Finset (Finset V)) (r : V) :
    excludedPolynomial (extensionEdges (P := P) (T := T) H r) (Sum.inr (Sum.inl none)) =
      excludedPolynomial H r * (1 + C (Fintype.card P : ℝ) * X) * (1 + C (Fintype.card T : ℝ) * X) +
      includedPolynomial H r * (1 + C (Fintype.card T : ℝ) * X) := by
  rw [excludedPolynomial, ← Equiv.sum_comp (excludedExtensionEquiv (P := P) (T := T) H r)]
  change (∑ x : ExcludedExtensionData (P := P) (T := T) H r, X ^ (excludedExtension H r x).val.card) = _
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, excludedExtension_card_left, excludedExtension_card_right, pow_add]
  have hleft : (∑ S : Excluded H r, ∑ L : SmallSet P, ∑ U : SmallSet T,
      (X : ℝ[X]) ^ S.val.card * X ^ L.val.card * X ^ U.val.card) =
      excludedPolynomial H r * (1 + C (Fintype.card P : ℝ) * X) * (1 + C (Fintype.card T : ℝ) * X) := by
    simp only [excludedPolynomial, ← Finset.mul_sum, ← Finset.sum_mul, smallSet_polynomial]
  have hright : (∑ S : Included H r, ∑ U : SmallSet T,
      (X : ℝ[X]) ^ S.val.card * X ^ U.val.card) =
      includedPolynomial H r * (1 + C (Fintype.card T : ℝ) * X) := by
    simp only [includedPolynomial, ← Finset.mul_sum, ← Finset.sum_mul, smallSet_polynomial]
  rw [hleft, hright]

theorem includedPolynomial_extension (H : Finset (Finset V)) (r : V) :
    includedPolynomial (extensionEdges (P := P) (T := T) H r) (Sum.inr (Sum.inl none)) =
      X * excludedPolynomial H r := by
  rw [includedPolynomial, ← Equiv.sum_comp (includedExtensionEquiv (P := P) (T := T) H r)]
  change (∑ S : Excluded H r, X ^ (includedExtension H r S).val.card) = _
  simp only [includedExtension_card, pow_succ, ← Finset.sum_mul, excludedPolynomial]
  ring

end ResearchMain.Hypercomb
