import ArithmeticSections.ApproximationBounds

namespace ArithmeticSections

set_option backward.isDefEq.respectTransparency false in
/-- Relation between signed errors of consecutive convergents. -/
theorem consecutive_error_relation {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ) :
    (actualDenominator θ n : ℝ) * θ - actualNumerator θ n =
      -completeQuotient θ (n + 2) *
        ((actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1)) := by
  have h := GenContFract.compExactValue_correctness_of_stream_eq_some
    (completeQuotient_stream hθ (n + 1))
  have hfr := ne_of_gt (completeQuotient_fract_pos hθ (n + 1))
  dsimp only [GenContFract.IntFractPair.of, GenContFract.compExactValue] at h
  rw [ite_eq_right hfr] at h
  change θ = (completeQuotient θ (n + 2) * (GenContFract.of θ).nums (n + 1) +
      1 * (GenContFract.of θ).nums n) /
    (completeQuotient θ (n + 2) * (GenContFract.of θ).dens (n + 1) +
      1 * (GenContFract.of θ).dens n) at h
  rw [← actualNumerator_eq_mathlib hθ hlo hhi (n + 1),
    ← actualNumerator_eq_mathlib hθ hlo hhi n,
    ← actualDenominator_eq_mathlib hθ (n + 1), ← actualDenominator_eq_mathlib hθ n,
    one_mul, one_mul] at h
  have hq : (0 : ℝ) < actualDenominator θ (n + 1) := by
    exact_mod_cast denominator_pos (one_le_actualDigit_succ hθ) (n + 1)
  have hc : 0 < completeQuotient θ (n + 2) := by linarith [one_lt_completeQuotient_succ hθ (n + 1)]
  have hd : completeQuotient θ (n + 2) * (actualDenominator θ (n + 1) : ℝ) + actualDenominator θ n ≠ 0 := by positivity
  have he := (eq_div_iff hd).mp h
  nlinarith

/-- Elementary unimodular lattice argument for best approximation. -/
theorem bestApproximation_of_unimodular {p p' q q' : ℤ} {x c : ℝ}
    (hq : 0 < q) (hq' : 0 < q')
    (hdet : (p * q' - p' * q) ^ 2 = 1) (hc : 1 < c)
    (hrel : (q' : ℝ) * x - p' = -c * ((q : ℝ) * x - p))
    (hne : (q : ℝ) * x - p ≠ 0) (r s : ℤ) (hs : 0 < s) (hsq : s ≤ q) :
    |(q : ℝ) * x - p| ≤ |(s : ℝ) * x - r| := by
  by_contra h
  have hsmall := lt_of_not_ge h
  let D : ℤ := p * q' - p' * q
  let A : ℤ := (r * q' - s * p') * D
  let B : ℤ := (p * s - q * r) * D
  have hpRep : r = A * p + B * p' := by
    calc
      r = r * D ^ 2 := by dsimp [D]; rw [hdet]; ring
      _ = A * p + B * p' := by dsimp [A, B, D]; ring
  have hqRep : s = A * q + B * q' := by
    calc
      s = s * D ^ 2 := by dsimp [D]; rw [hdet]; ring
      _ = A * q + B * q' := by dsimp [A, B, D]; ring
  have hpR : (r : ℝ) = A * (p : ℝ) + B * (p' : ℝ) := by exact_mod_cast hpRep
  have hqR : (s : ℝ) = A * (q : ℝ) + B * (q' : ℝ) := by exact_mod_cast hqRep
  have he : (s : ℝ) * x - r = ((A : ℝ) - B * c) * ((q : ℝ) * x - p) := by
    rw [hpR, hqR]
    calc
      ((A : ℝ) * q + B * q') * x - (A * p + B * p') =
          A * ((q : ℝ) * x - p) + B * ((q' : ℝ) * x - p') := by ring
      _ = _ := by rw [hrel]; ring
  rw [he, abs_mul] at hsmall
  have ha : |(A : ℝ) - B * c| < 1 := by
    have hepos := abs_pos.mpr hne
    nlinarith
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  rcases lt_trichotomy B 0 with hb | hb | hb
  · have hbR : (B : ℝ) < 0 := by exact_mod_cast hb
    have hAR : (A : ℝ) < B + 1 := by nlinarith
    have hA : A ≤ B := by
      have hi : A < B + 1 := by exact_mod_cast hAR
      omega
    nlinarith
  · have hAR : -1 < (A : ℝ) ∧ (A : ℝ) < 1 := by simpa [hb] using And.intro ha1 ha2
    have h1 : (-1 : ℤ) < A := by exact_mod_cast hAR.1
    have h2 : A < (1 : ℤ) := by exact_mod_cast hAR.2
    have hA : A = 0 := by omega
    simp [hA, hb] at hqRep
    omega
  · have hbR : (0 : ℝ) < B := by exact_mod_cast hb
    have hAR : (B : ℝ) - 1 < A := by nlinarith
    have hA : B ≤ A := by
      have h' : B - 1 < A := by exact_mod_cast hAR
      omega
    nlinarith

/-- Equation (2.5), for actual convergents. -/
theorem actual_bestApproximation {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ) (m : ℕ) (r : ℤ)
    (hm : 1 ≤ m) (hmq : m ≤ actualDenominator θ (n + 1)) :
    |(actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1)| ≤
      |(m : ℝ) * θ - r| := by
  have hq := denominator_pos (one_le_actualDigit_succ hθ) (n + 1)
  have hq' := denominator_pos (one_le_actualDigit_succ hθ) n
  have hdet : ((actualNumerator θ (n + 1) : ℤ) * actualDenominator θ n -
      (actualNumerator θ n : ℤ) * actualDenominator θ (n + 1)) ^ 2 = 1 := by
    change ((numerator (actualDigit θ) (n + 1) : ℤ) * denominator (actualDigit θ) n -
      (numerator (actualDigit θ) n : ℤ) * denominator (actualDigit θ) (n + 1)) ^ 2 = 1
    rw [continuant_determinant, ← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hne : (actualDenominator θ (n + 1) : ℝ) * θ - actualNumerator θ (n + 1) ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa only [mul_comm, actualDenominator] using
      (hθ.mul_natCast (Nat.ne_of_gt hq)).ne_nat (actualNumerator θ (n + 1))
  simpa only [Int.cast_natCast] using
    (bestApproximation_of_unimodular
      (p := (actualNumerator θ (n + 1) : ℤ)) (p' := (actualNumerator θ n : ℤ))
      (q := (actualDenominator θ (n + 1) : ℤ)) (q' := (actualDenominator θ n : ℤ))
      (x := θ) (c := completeQuotient θ (n + 2))
      (by exact_mod_cast hq) (by exact_mod_cast hq') hdet
      (one_lt_completeQuotient_succ hθ (n + 1))
      (by simpa only [Int.cast_natCast] using consecutive_error_relation hθ hlo hhi n)
      (by simpa only [Int.cast_natCast] using hne)
      r (m : ℤ) (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmq))

theorem integerDistance_lower_bound {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ) (m : ℕ)
    (hm : 1 ≤ m) (hmq : m ≤ actualDenominator θ (n + 1)) :
    1 / ((actualDenominator θ (n + 1) : ℝ) * (actualDigit θ (n + 2) + 2)) <
      integerDistance ((m : ℝ) * θ) :=
  lt_of_lt_of_le (actual_error_bounds hθ hlo hhi n).1
    (actual_bestApproximation hθ hlo hhi n m (round ((m : ℝ) * θ)) hm hmq)

end ArithmeticSections
