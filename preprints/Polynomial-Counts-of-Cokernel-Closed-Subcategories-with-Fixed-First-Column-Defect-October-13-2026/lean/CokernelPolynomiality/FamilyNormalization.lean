import CokernelPolynomiality.FamilyShear

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def familyNormalization {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) :
    intervalFamily n m c d ≅ intervalFamily n m c d := by
  classical
  exact squareZeroShearIso (familyElimination f hab hbn R) (familyElimination_square f hab hbn R) ≪≫
    familyDiagonalIso c d
      (fun j => if j ∈ R.P then (intervalScalar (f ≫ intervalFamilyProj n m c d j) hab hbn)⁻¹ else 1)
      (by
        intro j
        by_cases hj : j ∈ R.P
        · rw [ite_eq_left hj]
          exact inv_ne_zero (intervalScalar_ne_zero _ hab hbn ((mem_familyActive f j).mp (R.subset hj)))
        · rw [ite_eq_right hj]
          exact one_ne_zero)

theorem familyNormalization_nonpivot {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) (j : Fin m) (hj : j ∉ R.P) :
    f ≫ (familyNormalization f hab hbn R).hom ≫ intervalFamilyProj n m c d j=0 := by
  classical
  simp only [familyNormalization,Iso.trans_hom,familyDiagonalIso,squareZeroShearIso,Category.assoc,
    familyDiagonal_proj,ite_eq_right hj,one_smul,Preadditive.sub_comp,Category.id_comp,
    Preadditive.comp_sub]
  rw [familyElimination_source f hab hbn R j hj,sub_self]

theorem familyNormalization_pivot {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) (j : Fin m) (hj : j ∈ R.P)
    (hac : a ≤ c j) (hbd : b ≤ d j) :
    f ≫ (familyNormalization f hab hbn R).hom ≫ intervalFamilyProj n m c d j=
      intervalHom n a b (c j) (d j) hac hbd := by
  classical
  have hf := (mem_familyActive f j).mp (R.subset hj)
  have ho := intervalHom_order_of_ne_zero _ hf hbn
  have hs := intervalScalar_ne_zero _ hab hbn hf
  simp only [familyNormalization,Iso.trans_hom,familyDiagonalIso,squareZeroShearIso,Category.assoc,
    familyDiagonal_proj,ite_eq_left hj,Linear.comp_smul,Preadditive.sub_comp,Category.id_comp]
  rw [familyElimination_proj_pivot f hab hbn R j hj,smul_zero,sub_zero,Linear.comp_smul]
  conv_lhs => rhs; rw [intervalHom_eq_scalar (f ≫ intervalFamilyProj n m c d j) hac ho.2.1 hbd hbn]
  rw [smul_smul,inv_mul_cancel₀ hs,one_smul]

end CokernelPolynomiality
