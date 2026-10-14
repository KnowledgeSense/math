import CircleResidues.Recurrence

noncomputable section
open PowerSeries Finset
namespace CircleResidues
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem sourceCoefficient_odd {k : ℕ} (hk : Odd k) : sourceCoefficient k = 0 := by
  by_cases hk1 : k = 1
  · simp [hk1, sourceCoefficient]
  · have hgt : 1 < k := by
      have hpos := hk.pos
      omega
    simp [sourceCoefficient, bernoulli_eq_zero_of_odd hk hgt]

/-- Exact bridge from the original Bernoulli sequence to the even exponent. -/
theorem sourceExponent_even (a : ℚ) :
    (mk fun k => a * sourceCoefficient k) = (evenExponent a).subst (X ^ 2) := by
  ext k
  rw [coeff_mk, coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0)]
  by_cases hk : 2 ∣ k
  · rcases hk with ⟨r, rfl⟩
    have hrdiv : 2 * r / 2 = r := by omega
    simp only [dvd_mul_right, ↓reduceIte, hrdiv, Algebra.algebraMap_self, RingHom.id_apply, evenExponent, coeff_mk,
      sourceCoefficient, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · rw [ite_eq_right hk]
    have hodd : Odd k := Nat.not_even_iff_odd.mp (fun he => hk he.two_dvd)
    simp [sourceCoefficient_odd hodd]

/-- The evaluated original ordinary Bell polynomial is the reduced coefficient. -/
theorem residuePolynomial_even (a : ℚ) (n : ℕ) :
    residuePolynomial (-a) (2 * n) = evenResidue a n := by
  simp only [residuePolynomial, neg_neg]
  rw [sourceExponent_even]
  rw [← subst_comp_subst_apply (evenExponent_hasSubst a) (HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0))]
  rw [coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp [evenResidue]

/-- Every half-integer of the required form has valuation `-1`. -/
theorem half_integer_valuation (m : ℕ) :
    (m : ℚ) - 1 / 2 ≠ 0 ∧ padicValRat 2 ((m : ℚ) - 1 / 2) = -1 := by
  have hvalhalf : Rat.padicValuation 2 (1 / 2 : ℚ) = WithZero.exp (1 : ℤ) := by
    have htwo : Rat.padicValuation 2 (2 : ℚ) = WithZero.exp (-1 : ℤ) :=
      Rat.padicValuation_self 2
    rw [map_div₀, map_one, htwo, one_div]
    simp
  have hmle : Rat.padicValuation 2 (m : ℚ) ≤ 1 := by
    rw [Rat.padicValuation_le_one_iff]
    simp
  have heq := (Rat.padicValuation 2).map_sub_eq_of_lt_right
    (lt_of_le_of_lt hmle (by rw [hvalhalf]; exact WithZero.one_lt_exp_iff.mpr (by norm_num)))
  rw [hvalhalf] at heq
  have hnz : (m : ℚ) - 1 / 2 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at heq
    exact WithZero.exp_ne_zero heq.symm
  refine ⟨hnz, ?_⟩
  change (if (m : ℚ) - 1 / 2 = 0 then 0 else
    WithZero.exp (-padicValRat 2 ((m : ℚ) - 1 / 2))) = WithZero.exp 1 at heq
  simp only [hnz, ↓reduceIte, WithZero.exp_inj] at heq
  omega

/-- Exact valuation at every pole-index parameter of the original residue polynomial. -/
theorem residuePolynomial_valuation (m : ℕ) :
    residuePolynomial (1 / 2 - m) (2 * m) ≠ 0 ∧
    padicValRat 2 (residuePolynomial (1 / 2 - m) (2 * m)) =
      -3 * (m : ℤ) - padicValNat 2 m.factorial := by
  have hm := half_integer_valuation m
  have h := evenResidue_valuation ((m : ℚ) - 1 / 2) hm.1 hm.2 m
  rw [show (1 / 2 - (m : ℚ)) = -((m : ℚ) - 1 / 2) by ring,
    residuePolynomial_even]
  exact h

/-- Every arithmetic residue factor on the circle pole lattice is nonzero. -/
theorem residuePolynomial_ne_zero (m : ℕ) :
    residuePolynomial (1 / 2 - m) (2 * m) ≠ 0 :=
  (residuePolynomial_valuation m).1

end CircleResidues
