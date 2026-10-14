import HonestEmbeddingDimension.ThreeCoordinateNormalForm

namespace HonestEmbeddingDimension

def TripleJetIndex (a b N : ℕ) := {v : Fin N × Fin N // a*v.1.val+b*v.2.val < N}

instance (a b N : ℕ) : Fintype (TripleJetIndex a b N) := inferInstanceAs (Fintype {v : Fin N × Fin N // a*v.1.val+b*v.2.val < N})

noncomputable def tripleCoordinates (m : ℕ) (Y Z : PowerSeries ℂ) : Fin 3 → PowerSeries ℂ :=
  ![PowerSeries.X^m,Y,Z]

/-- Grouping the parameter powers gives an actual finite parameter-module jet representation. -/
theorem triple_polynomial_jet (m a b N : ℕ) (hm : m ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (Y Z : PowerSeries ℂ) (hY : Y.order = a) (hZ : Z.order = b)
    (P : MvPolynomial (Fin 3) ℂ) :
    ∃ u : TripleJetIndex a b N → PowerSeries ℂ,
      formalJet N (MvPolynomial.aeval (tripleCoordinates m Y Z) P) =
      formalJet N (∑ v, PowerSeries.expand m hm (u v) * (Y^v.val.1.val * Z^v.val.2.val)) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have hev : MvPolynomial.aeval (tripleCoordinates m Y Z) (MvPolynomial.monomial α c) =
        c • ((PowerSeries.X^m)^(α 0) * (Y^(α 1)*Z^(α 2))) := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp [tripleCoordinates,Fin.prod_univ_three,Algebra.smul_def,mul_assoc]
    rw [hev]
    by_cases hw : a*α 1+b*α 2 < N
    · have h1 : α 1 < N := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha) (lt_of_le_of_lt (Nat.le_add_right _ _) hw)
      have h2 : α 2 < N := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hb) (lt_of_le_of_lt (Nat.le_add_left _ _) hw)
      let v : TripleJetIndex a b N := ⟨(⟨α 1,h1⟩,⟨α 2,h2⟩),hw⟩
      refine ⟨Pi.single v (PowerSeries.monomial (α 0) c),?_⟩
      congr 1
      rw [Finset.sum_eq_single v]
      · rw [Pi.single_eq_same]
        simp [v,PowerSeries.monomial_eq_C_mul_X_pow,PowerSeries.expand_C,Algebra.smul_def,mul_assoc]
      · intro w _ hwv
        simp [hwv]
      · simp
    · refine ⟨0,?_⟩
      ext j
      have ho : (N : ℕ∞) ≤ (c • ((PowerSeries.X^m)^(α 0) * (Y^(α 1)*Z^(α 2)))).order := by
        apply le_trans _ PowerSeries.le_order_smul
        simp only [PowerSeries.order_mul,PowerSeries.order_pow,PowerSeries.order_X,hY,hZ,nsmul_eq_mul]
        apply le_trans _ (le_add_left le_rfl)
        exact_mod_cast (show N ≤ α 1*a+α 2*b by simpa [Nat.mul_comm] using Nat.le_of_not_gt hw)
      have hz := PowerSeries.coeff_of_lt_order (φ := c • ((PowerSeries.X^m)^(α 0) * (Y^(α 1)*Z^(α 2))))
        j (lt_of_lt_of_le (by exact_mod_cast j.isLt) ho)
      simpa [formalJet] using hz
  | add P Q hP hQ =>
    obtain ⟨u,hu⟩ := hP
    obtain ⟨v,hv⟩ := hQ
    refine ⟨u+v,?_⟩
    ext j
    have huj := congrFun hu j
    have hvj := congrFun hv j
    simp only [formalJet,map_add] at huj hvj ⊢
    rw [huj,hvj]
    simp [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]

end HonestEmbeddingDimension
