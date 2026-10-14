import HonestEmbeddingDimension.AnalyticPlane

namespace HonestEmbeddingDimension

/-- A high-order second coordinate contributes nothing to a low jet. -/
theorem plane_jet_of_high_second (m N : ℕ) (hm : m ≠ 0) (Y : PowerSeries ℂ)
    (hY : (N : ℕ∞) ≤ Y.order) (P : MvPolynomial (Fin 2) ℂ) :
    ∃ u : PowerSeries ℂ, formalJet N (MvPolynomial.aeval (planeCoordinates m Y) P) =
      formalJet N (PowerSeries.expand m hm u) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have hev : MvPolynomial.aeval (planeCoordinates m Y) (MvPolynomial.monomial α c) =
        c • ((PowerSeries.X ^ m) ^ (α 0) * Y ^ (α 1)) := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp [planeCoordinates, Fin.prod_univ_two, Algebra.smul_def]
    rw [hev]
    by_cases hj : α 1 = 0
    · refine ⟨PowerSeries.monomial (α 0) c, ?_⟩
      congr 1
      simp [hj, PowerSeries.monomial_eq_C_mul_X_pow, PowerSeries.expand_C, Algebra.smul_def]
    · refine ⟨0, ?_⟩
      ext j
      have ho : (N : ℕ∞) ≤ (c • ((PowerSeries.X ^ m) ^ (α 0) * Y ^ (α 1))).order := by
        apply le_trans _ PowerSeries.le_order_smul
        rw [PowerSeries.order_mul, PowerSeries.order_pow Y]
        apply le_trans hY
        apply le_trans _ (le_add_left le_rfl)
        rw [nsmul_eq_mul]
        exact le_mul_of_one_le_left (zero_le : (0 : ℕ∞) ≤ Y.order) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj)
      have hz := PowerSeries.coeff_of_lt_order (φ := c • ((PowerSeries.X ^ m) ^ (α 0) * Y ^ (α 1)))
        j (lt_of_lt_of_le (by exact_mod_cast j.isLt) ho)
      simpa [formalJet] using hz
  | add P Q hP hQ =>
    obtain ⟨u,hu⟩ := hP
    obtain ⟨v,hv⟩ := hQ
    refine ⟨u+v, ?_⟩
    ext j
    have huj := congrFun hu j
    have hvj := congrFun hv j
    simp only [formalJet, map_add] at huj hvj ⊢
    rw [huj, hvj]

/-- A plane value below the order of the second coordinate is a parameter multiple. -/
theorem plane_low_value_dvd (m N n : ℕ) (hm : m ≠ 0) (Y : PowerSeries ℂ)
    (hY : (N : ℕ∞) ≤ Y.order) (hn : n < N)
    (hval : n ∈ polynomialValues (planeCoordinates m Y)) : m ∣ n := by
  obtain ⟨P,hP⟩ := hval
  obtain ⟨u,hu⟩ := plane_jet_of_high_second m N hm Y hY P
  have he := (order_eq_of_jet_eq hu hn).mp hP
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at he
  rw [PowerSeries.order_expand, ← PowerSeries.coe_toNat_order hu0, nsmul_eq_mul] at he
  have he' : m*u.order.toNat = n := by exact_mod_cast he
  exact ⟨u.order.toNat, he'.symm⟩

end HonestEmbeddingDimension
