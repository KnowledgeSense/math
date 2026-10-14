import HonestEmbeddingDimension.ResidueRank

namespace HonestEmbeddingDimension

noncomputable def planeCoordinates (m : ℕ) (Y : PowerSeries ℂ) : Fin 2 → PowerSeries ℂ :=
  ![PowerSeries.X ^ m, Y]

/-- Every finite plane-algebra jet below the first repeated residue is in the actual parameter span. -/
theorem plane_polynomial_jet (m a : ℕ) (hm : m ≠ 0) (Y : PowerSeries ℂ)
    (hY : Y.order = a) (P : MvPolynomial (Fin 2) ℂ) :
    ∃ u : Fin m → PowerSeries ℂ,
      formalJet (m*a) (MvPolynomial.aeval (planeCoordinates m Y) P) =
      formalJet (m*a) (∑ j, PowerSeries.expand m hm (u j) * Y ^ j.val) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have hev : MvPolynomial.aeval (planeCoordinates m Y) (MvPolynomial.monomial α c) =
        c • ((PowerSeries.X ^ m) ^ (α 0) * Y ^ (α 1)) := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp [planeCoordinates, Fin.prod_univ_two, Algebra.smul_def]
    rw [hev]
    by_cases hj : α 1 < m
    · refine ⟨Pi.single ⟨α 1,hj⟩ (PowerSeries.monomial (α 0) c), ?_⟩
      congr 1
      rw [Finset.sum_eq_single ⟨α 1,hj⟩]
      · simp [PowerSeries.monomial_eq_C_mul_X_pow, PowerSeries.expand_C,
          Algebra.smul_def, mul_assoc]
      · intro b _ hb
        simp [hb]
      · simp
    · refine ⟨0, ?_⟩
      ext j
      have horder : ((m*a : ℕ) : ℕ∞) ≤ (c • ((PowerSeries.X ^ m) ^ (α 0) * Y ^ (α 1))).order := by
        apply le_trans _ PowerSeries.le_order_smul
        simp only [PowerSeries.order_mul, PowerSeries.order_pow,
          PowerSeries.order_X, hY, nsmul_eq_mul]
        have hma : m*a ≤ α 1*a := Nat.mul_le_mul_right a (Nat.le_of_not_gt hj)
        exact le_trans (by exact_mod_cast hma) (le_add_left le_rfl)
      have hz : PowerSeries.coeff j (c • ((PowerSeries.X ^ m) ^ (α 0) * Y ^ (α 1))) = 0 :=
        PowerSeries.coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast j.isLt) horder)
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
    simp [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem order_eq_of_jet_eq {N n : ℕ} {f g : PowerSeries ℂ}
    (h : formalJet N f = formalJet N g) (hn : n < N) :
    f.order = n ↔ g.order = n := by
  have hc (j : ℕ) (hj : j < N) : PowerSeries.coeff j f = PowerSeries.coeff j g :=
    congrFun h ⟨j,hj⟩
  simp only [PowerSeries.order_eq_nat]
  rw [hc n hn]
  apply and_congr_right
  intro _
  exact forall_congr' fun j => imp_congr_right fun hj => by rw [hc j (lt_trans hj hn)]

/-- Below the collision threshold, a plane-algebra value is a nonnegative combination of its two coordinate orders. -/
theorem plane_value_below_threshold (m a : ℕ) (hm : m ≠ 0) (hcop : m.Coprime a)
    (Y : PowerSeries ℂ) (hY : Y.order = a) (n : ℕ) (hn : n < m*a)
    (hval : n ∈ polynomialValues (planeCoordinates m Y)) :
    ∃ k j : ℕ, j < m ∧ n = m*k + a*j := by
  obtain ⟨P,hP⟩ := hval
  obtain ⟨u,hu⟩ := plane_polynomial_jet m a hm Y hY P
  have ho := (order_eq_of_jet_eq hu hn).mp hP
  obtain ⟨i,_,k,hk⟩ := order_of_parameter_span Finset.univ m hm u
    (fun i : Fin m => Y ^ i.val) (fun i => i.val*a)
    (by intro i _; simp [PowerSeries.order_pow, hY, nsmul_eq_mul])
    (by
      intro i _ j _ hij he
      apply hij
      apply Fin.ext
      have heq : i.val ≡ j.val [MOD m] := Nat.ModEq.cancel_right_of_coprime hcop he
      simpa [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using heq)
    n ho
  exact ⟨k,i.val,i.isLt,by simpa [Nat.mul_comm a] using hk⟩

end HonestEmbeddingDimension
