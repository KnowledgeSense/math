import AlternativeQCharlier.Definitions

namespace AlternativeQCharlier
noncomputable section

 theorem parameter_pos {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) :
    0 < 1 + ρ*q^n := by
  have := mul_pos h.1 (pow_pos h.2.2.1 n)
  linarith

 theorem c_pos {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) : 0 < c ρ q n := by
  unfold c
  exact div_pos (mul_pos (pow_pos h.2.2.1 n) (parameter_pos h n))
    (mul_pos (parameter_pos h _) (parameter_pos h _))

 theorem t_pos {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) : 0 < t ρ q (n+1) := by
  have hq : q < 1 := by linarith [h.2.2.2]
  have hp : q^(n+1) < 1 := pow_lt_one₀ (le_of_lt h.2.2.1) hq (by omega)
  simp only [t]
  exact div_pos
    (mul_pos (mul_pos (mul_pos h.1 (pow_pos h.2.2.1 n)) (sub_pos.mpr hp))
      (parameter_pos h _))
    (mul_pos (parameter_pos h _) (parameter_pos h _))

 theorem t_nonneg {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) : 0 ≤ t ρ q n := by
  cases n with
  | zero => simp [t]
  | succ n => exact le_of_lt (t_pos h n)

 theorem qpow_le_one {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) : q^n ≤ 1 := by
  exact pow_le_one₀ (le_of_lt h.2.2.1) (by linarith [h.2.2.2])

 theorem t_le {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) : t ρ q n ≤ 5/16 := by
  cases n with
  | zero => norm_num [t]
  | succ n =>
    have hr := h.1
    have hq := h.2.2.1
    have hp0 : 0 ≤ q^n := le_of_lt (pow_pos hq _)
    have hp1 : 0 ≤ q^(n+1) := le_of_lt (pow_pos hq _)
    have hp2 : 0 ≤ q^(2*n+1) := le_of_lt (pow_pos hq _)
    have hp3 : 0 ≤ q^(2*n+3) := le_of_lt (pow_pos hq _)
    have hpn := qpow_le_one h n
    have hpnn := qpow_le_one h (n+1)
    have hpnnn := qpow_le_one h (2*n+3)
    have hnum : ρ*q^n*(1-q^(n+1))*(1+ρ*q^(2*n+3)) ≤ ρ*(1+ρ) := by
      calc
        _ ≤ ρ*1*1*(1+ρ*1)  := by gcongr; linarith
        _ = ρ*(1+ρ) := by ring
    have hden : 1 ≤ (1+ρ*q^(n+1))*(1+ρ*q^(2*n+1)) := by
      have : 0 ≤ ρ*q^(n+1)*(ρ*q^(2*n+1)) := by positivity
      nlinarith [mul_nonneg (le_of_lt hr) hp1, mul_nonneg (le_of_lt hr) hp2]
    have hbound : ρ*(1+ρ) ≤ (5:ℝ)/16 := by nlinarith [h.2.1]
    simp only [t]
    apply (div_le_iff₀ (by linarith : 0 < (1+ρ*q^(n+1))*(1+ρ*q^(2*n+1)))).mpr
    nlinarith

 theorem x_eq_rescaling {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) :
    x ρ q n = c ρ q n * (1+t ρ q n) := by
  have hr : 0 < ρ := h.1
  have hqpos : 0 < q := h.2.2.1
  have hq : q ≠ 0 := ne_of_gt hqpos
  have hp : ∀ k, 1+ρ*q^k ≠ 0 := fun k => ne_of_gt (parameter_pos h k)
  cases n with
  | zero =>
    have hi : 1+ρ*q⁻¹ ≠ 0 := by positivity
    simp only [x, c, t, pow_zero, Nat.mul_zero, Nat.zero_add, pow_one]
    field_simp [hi, hq, hp, ne_of_gt (show 0 < 1+ρ by positivity)]
    ring
  | succ n =>
    simp only [x, c, t]
    field_simp [hp]
    simp only [pow_mul, pow_succ]
    ring

 theorem y_eq_rescaling {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) :
    y ρ q n = c ρ q n * c ρ q (n+1) * t ρ q (n+1) := by
  have hp : ∀ k, 1+ρ*q^k ≠ 0 := fun k => ne_of_gt (parameter_pos h k)
  simp only [y, c, t]
  field_simp [hp]
  simp only [pow_mul, pow_succ]
  ring

 theorem t_ratio_identity {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) :
    t ρ q (n+2) = t ρ q (n+1) *
      (q * ((1-q^(n+2))/(1-q^(n+1))) *
      ((1+ρ*q^(2*n+5))/(1+ρ*q^(2*n+3))) *
      ((1+ρ*q^(n+1))/(1+ρ*q^(n+2))) *
      ((1+ρ*q^(2*n+1))/(1+ρ*q^(2*n+3)))) := by
  have hp : ∀ k, 1+ρ*q^k ≠ 0 := fun k => ne_of_gt (parameter_pos h k)
  have hq : q < 1 := by linarith [h.2.2.2]
  have hz : 1-q^(n+1) ≠ 0 := ne_of_gt (sub_pos.mpr
    (pow_lt_one₀ (le_of_lt h.2.2.1) hq (by omega)))
  simp only [t]
  field_simp [hp, hz]
  simp only [pow_mul, pow_succ]
  ring

 theorem t_ratio_le {ρ q : ℝ} (h : ParameterBox ρ q) (n : ℕ) :
    t ρ q (n+2) ≤ (3/8)*t ρ q (n+1) := by
  have hr : 0 < ρ := h.1
  have hq : 0 < q := h.2.2.1
  have hq1 : q < 1 := by linarith [h.2.2.2]
  have hden : 0 < 1-q^(n+1) := sub_pos.mpr
    (pow_lt_one₀ (le_of_lt hq) hq1 (by omega))
  have hpow : q^(n+1) ≤ q := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right (qpow_le_one h n) (le_of_lt hq)
  have hfirst : (1-q^(n+2))/(1-q^(n+1)) ≤ 1+q := by
    apply (div_le_iff₀ hden).mpr
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    nlinarith
  have hsecond : (1+ρ*q^(2*n+5))/(1+ρ*q^(2*n+3)) ≤ 1 := by
    apply (div_le_iff₀ (parameter_pos h _)).mpr
    have hpower : q^(2*n+5) ≤ q^(2*n+3) := by
      calc
        _ = q^(2*n+3)*q^2 := by rw [← pow_add]
        _ ≤ q^(2*n+3)*1 := mul_le_mul_of_nonneg_left (qpow_le_one h 2) (by positivity)
        _ = _ := mul_one _
    nlinarith
  have hfactor (j k : ℕ) : (1+ρ*q^j)/(1+ρ*q^k) ≤ 1+ρ := by
    apply (div_le_iff₀ (parameter_pos h _)).mpr
    have hj := qpow_le_one h j
    have hk : 0 ≤ ρ*q^k := by positivity
    have hprod : 0 ≤ ρ*(ρ*q^k) := by positivity
    nlinarith
  have hprod :
      q * ((1-q^(n+2))/(1-q^(n+1))) *
      ((1+ρ*q^(2*n+5))/(1+ρ*q^(2*n+3))) *
      ((1+ρ*q^(n+1))/(1+ρ*q^(n+2))) *
      ((1+ρ*q^(2*n+1))/(1+ρ*q^(2*n+3))) ≤
        q*(1+q)*1*(1+ρ)*(1+ρ) := by
    gcongr <;> exact hfactor _ _
  have hconstant : q*(1+q)*1*(1+ρ)*(1+ρ) ≤ (3:ℝ)/8 := by
    calc
      _ ≤ (1/5 : ℝ)*(1+1/5)*1*(1+1/4)*(1+1/4) := by gcongr <;> linarith [h.2.1, h.2.2.2]
      _ = _ := by norm_num
  rw [t_ratio_identity h]
  nlinarith [mul_le_mul_of_nonneg_left (hprod.trans hconstant) (le_of_lt (t_pos h n))]

end
end AlternativeQCharlier
