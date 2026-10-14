import MainTheorems.DiagonalSchatten.TwoRowPowerConnection

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped Matrix.Norms.Elementwise

def symmetricGap (m : Fin 3 → ℝ) : ℝ :=
  Real.sqrt ((m 0 - m 1) ^ 2 + 4 * m 2 ^ 2)

def symmetricPlus (m : Fin 3 → ℝ) : ℝ := (m 0 + m 1 + symmetricGap m) / 2
def symmetricMinus (m : Fin 3 → ℝ) : ℝ := (m 0 + m 1 - symmetricGap m) / 2

def symmetricDividedPower (r : ℝ) (m : Fin 3 → ℝ) : ℝ :=
  (symmetricPlus m ^ r - symmetricMinus m ^ r) / symmetricGap m

def symmetricPower (r : ℝ) (m : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let d := symmetricDividedPower r m
  ![symmetricMinus m ^ r + d * (m 0 - symmetricMinus m),
    symmetricMinus m ^ r + d * (m 1 - symmetricMinus m), d * m 2]

def symmetricGapVariation (m z : Fin 3 → ℝ) : ℝ :=
  ((m 0 - m 1) * (z 0 - z 1) + 4 * m 2 * z 2) / symmetricGap m

def symmetricPlusVariation (m z : Fin 3 → ℝ) : ℝ :=
  (z 0 + z 1 + symmetricGapVariation m z) / 2

def symmetricMinusVariation (m z : Fin 3 → ℝ) : ℝ :=
  (z 0 + z 1 - symmetricGapVariation m z) / 2

def symmetricDividedPowerVariation (r : ℝ) (m z : Fin 3 → ℝ) : ℝ :=
  (r * symmetricPlus m ^ (r - 1) * symmetricPlusVariation m z -
    r * symmetricMinus m ^ (r - 1) * symmetricMinusVariation m z -
    symmetricDividedPower r m * symmetricGapVariation m z) / symmetricGap m

def symmetricPowerVariation (r : ℝ) (m z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let d := symmetricDividedPower r m
  let v := symmetricDividedPowerVariation r m z
  let l := symmetricMinusVariation m z
  ![r * symmetricMinus m ^ (r - 1) * l + v * (m 0 - symmetricMinus m) + d * (z 0 - l),
    r * symmetricMinus m ^ (r - 1) * l + v * (m 1 - symmetricMinus m) + d * (z 1 - l),
    v * m 2 + d * z 2]

theorem symmetricGap_positive (m : Fin 3 → ℝ) (hc : m 2 ≠ 0) : 0 < symmetricGap m := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (m 0 - m 1), sq_pos_of_ne_zero hc]

theorem symmetricGap_curve_deriv (m z : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => symmetricGap (m + t • z)) (symmetricGapVariation m z) 0 := by
  have hcoord (i : Fin 3) : HasDerivAt (fun t : ℝ => (m + t • z) i) (z i) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (m i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (z i)) using 1
    simp
  have hD : HasDerivAt (fun t : ℝ =>
      ((m + t • z) 0 - (m + t • z) 1) ^ 2 + 4 * (m + t • z) 2 ^ 2)
      (2 * (m 0 - m 1) * (z 0 - z 1) + 8 * m 2 * z 2) 0 := by
    convert! (((hcoord 0).sub (hcoord 1)).fun_pow 2).add
      (((hcoord 2).fun_pow 2).const_mul 4) using 1
    simp
    ring
  have hDn : ((m + (0 : ℝ) • z) 0 - (m + (0 : ℝ) • z) 1) ^ 2 +
      4 * (m + (0 : ℝ) • z) 2 ^ 2 ≠ 0 := by
    simp only [zero_smul, add_zero]
    have hpos : 0 < (m 0 - m 1) ^ 2 + 4 * m 2 ^ 2 := by
      nlinarith [sq_nonneg (m 0 - m 1), sq_pos_of_ne_zero hc]
    exact hpos.ne'
  convert! hD.sqrt hDn using 1
  simp only [zero_smul, add_zero]
  unfold symmetricGapVariation symmetricGap
  have hg := (symmetricGap_positive m hc).ne'
  unfold symmetricGap at hg
  field_simp [hg]
  ring

theorem symmetricPlus_curve_deriv (m z : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => symmetricPlus (m + t • z)) (symmetricPlusVariation m z) 0 := by
  have hcoord (i : Fin 3) : HasDerivAt (fun t : ℝ => (m + t • z) i) (z i) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (m i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (z i)) using 1
    simp
  exact (((hcoord 0).add (hcoord 1)).add (symmetricGap_curve_deriv m z hc)).div_const 2

theorem symmetricMinus_curve_deriv (m z : Fin 3 → ℝ) (hc : m 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => symmetricMinus (m + t • z)) (symmetricMinusVariation m z) 0 := by
  have hcoord (i : Fin 3) : HasDerivAt (fun t : ℝ => (m + t • z) i) (z i) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (m i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (z i)) using 1
    simp
  exact (((hcoord 0).add (hcoord 1)).sub (symmetricGap_curve_deriv m z hc)).div_const 2

theorem symmetricDividedPower_curve_deriv (r : ℝ) (m z : Fin 3 → ℝ)
    (hc : m 2 ≠ 0) (hp : symmetricPlus m ≠ 0) (hm : symmetricMinus m ≠ 0) :
    HasDerivAt (fun t : ℝ => symmetricDividedPower r (m + t • z))
      (symmetricDividedPowerVariation r m z) 0 := by
  have hplus := (symmetricPlus_curve_deriv m z hc).rpow_const (p := r)
    (Or.inl (by simpa only [zero_smul, add_zero] using hp))
  have hminus := (symmetricMinus_curve_deriv m z hc).rpow_const (p := r)
    (Or.inl (by simpa only [zero_smul, add_zero] using hm))
  have hd := (hplus.sub hminus).div (symmetricGap_curve_deriv m z hc)
    (by simpa only [zero_smul, add_zero] using (symmetricGap_positive m hc).ne')
  convert! hd using 1
  simp only [zero_smul, add_zero, Pi.sub_apply]
  unfold symmetricDividedPowerVariation symmetricDividedPower
  field_simp [(symmetricGap_positive m hc).ne']

theorem symmetricPower_curve_deriv (r : ℝ) (m z : Fin 3 → ℝ)
    (hc : m 2 ≠ 0) (hp : symmetricPlus m ≠ 0) (hm : symmetricMinus m ≠ 0) :
    HasDerivAt (fun t : ℝ => symmetricPower r (m + t • z))
      (symmetricPowerVariation r m z) 0 := by
  have hcoord (i : Fin 3) : HasDerivAt (fun t : ℝ => (m + t • z) i) (z i) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (m i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (z i)) using 1
    simp
  have hl := symmetricMinus_curve_deriv m z hc
  have hlpow := hl.rpow_const (p := r)
    (Or.inl (by simpa only [zero_smul, add_zero] using hm))
  have hd := symmetricDividedPower_curve_deriv r m z hc hp hm
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hlpow.add (hd.mul ((hcoord 0).sub hl)) using 1
    dsimp [symmetricPower, symmetricPowerVariation]
    simp
    ring
  · convert! hlpow.add (hd.mul ((hcoord 1).sub hl)) using 1
    dsimp [symmetricPower, symmetricPowerVariation]
    simp
    ring
  · convert! hd.mul (hcoord 2) using 1
    dsimp [symmetricPower, symmetricPowerVariation]
    simp

theorem contDiffAt_symmetricPower {n : WithTop ℕ∞} (r : ℝ) (m : Fin 3 → ℝ)
    (hc : m 2 ≠ 0) (hp : symmetricPlus m ≠ 0) (hm : symmetricMinus m ≠ 0) :
    ContDiffAt ℝ n (symmetricPower r) m := by
  have hrad : ContDiffAt ℝ n (fun z : Fin 3 → ℝ =>
      (z 0 - z 1) ^ 2 + 4 * z 2 ^ 2) m := by fun_prop
  have hnon : (m 0 - m 1) ^ 2 + 4 * m 2 ^ 2 ≠ 0 := by
    have hpos : 0 < (m 0 - m 1) ^ 2 + 4 * m 2 ^ 2 := by
      nlinarith [sq_nonneg (m 0 - m 1), sq_pos_of_ne_zero hc]
    exact hpos.ne'
  have hg : ContDiffAt ℝ n symmetricGap m := hrad.sqrt hnon
  have hpC : ContDiffAt ℝ n symmetricPlus m := by
    unfold symmetricPlus
    exact ((show ContDiffAt ℝ n (fun z : Fin 3 → ℝ => z 0 + z 1) m by fun_prop).add hg).div_const 2
  have hmC : ContDiffAt ℝ n symmetricMinus m := by
    unfold symmetricMinus
    exact ((show ContDiffAt ℝ n (fun z : Fin 3 → ℝ => z 0 + z 1) m by fun_prop).sub hg).div_const 2
  have hd : ContDiffAt ℝ n (symmetricDividedPower r) m :=
    ((hpC.rpow_const_of_ne hp).sub (hmC.rpow_const_of_ne hm)).div hg
      (symmetricGap_positive m hc).ne'
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (hmC.rpow_const_of_ne hm).add (hd.mul
      ((show ContDiffAt ℝ n (fun z : Fin 3 → ℝ => z 0) m by fun_prop).sub hmC))
  · exact (hmC.rpow_const_of_ne hm).add (hd.mul
      ((show ContDiffAt ℝ n (fun z : Fin 3 → ℝ => z 1) m by fun_prop).sub hmC))
  · exact hd.mul (show ContDiffAt ℝ n (fun z : Fin 3 → ℝ => z 2) m by fun_prop)

theorem fderiv_symmetricPower (r : ℝ) (m z : Fin 3 → ℝ)
    (hc : m 2 ≠ 0) (hp : symmetricPlus m ≠ 0) (hm : symmetricMinus m ≠ 0) :
    fderiv ℝ (symmetricPower r) m z = symmetricPowerVariation r m z := by
  have hd := (contDiffAt_symmetricPower (n := 1) r m hc hp hm).differentiableAt (by norm_num)
  have hcurve : HasDerivAt (fun t : ℝ => m + t • z) z 0 := by
    convert! (hasDerivAt_const (0 : ℝ) m).add ((hasDerivAt_id (0 : ℝ)).smul_const z) using 1
    simp
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  exact hcomp.unique (symmetricPower_curve_deriv r m z hc hp hm)

variable {J : Type*} [Fintype J]

theorem symmetricPower_gram (r : ℝ) (X : Matrix (Fin 2) J ℝ) :
    symmetricPower r ![gramFirst X, gramSecond X, gramCross X] = realGramPowerCoefficient r X := by
  simp [symmetricPower, symmetricDividedPower, symmetricPlus, symmetricMinus, symmetricGap,
    realGramPowerCoefficient, realGramPlus, realGramMinus, realGramGap]

end

end ResearchMain.DiagonalSchatten
