import HankelAutomaticity.InitialDeterminants

noncomputable section
namespace HankelAutomaticity

 def normalizationExponent (L n : ℕ) : ℕ := 2*n-2^(L+1)-1

 def normalizedPair (L n : ℕ) (q : ℚ) : ℚ × ℚ :=
  (q^normalizationExponent L n*hankel L n (1/q),
    q^normalizationExponent L n*derivativeCompanion L n (1/q))

 theorem normalized_two (q : ℚ) (hq : q≠0) : normalizedPair 0 2 q=(-q, 1-2*q) := by
  simp only [normalizedPair, normalizationExponent]
  norm_num
  rw [(pair_two q⁻¹).1, (pair_two q⁻¹).2]
  constructor <;> field_simp

 theorem normalized_three (q : ℚ) (hq : q≠0) : normalizedPair 1 3 q=(3*q-1, 2*q-1) := by
  simp only [normalizedPair, normalizationExponent]
  norm_num
  rw [(pair_three q⁻¹).1, (pair_three q⁻¹).2]
  constructor <;> field_simp

 theorem normalized_four (q : ℚ) (hq : q≠0) :
    normalizedPair 1 4 q=(q*(1-2*q)*(3-8*q), -(1-2*q)^2*(1-4*q)) := by
  simp only [normalizedPair, normalizationExponent]
  norm_num
  rw [(pair_four q⁻¹).1, (pair_four q⁻¹).2]
  constructor <;> field_simp

 theorem normalize_lower_algebra (r : ℕ) (q A B : ℚ) (hq : q≠0) :
    q^(2*r+1)*(1/q-2)^(2*r)*((1/q-2)*A-B)=
      (1-2*q)^(2*r+1)*A-q*(1-2*q)^(2*r)*B := by
  rw [show 1/q-2=(1-2*q)/q by field_simp, div_pow, pow_succ, pow_succ]
  field_simp

 theorem normalize_lower_companion (r : ℕ) (q B : ℚ) (hq : q≠0) :
    q^(2*r+1)*(1/q-2)^(2*r+1)*B=(1-2*q)^(2*r+1)*B := by
  rw [← mul_pow]
  have h : q*(1/q-2)=1-2*q := by field_simp
  rw [h]

 theorem normalize_upper_algebra (M b : ℕ) (hM : 0<M) (q A B : ℚ) (hq : q≠0) :
    q^(M+b)*2^b*(1/q-2)^(M-1)*((1/q-2)*A-B)=
      (1-2*q)^M*((2*q)^b*A)-q*(1-2*q)^(M-1)*((2*q)^b*B) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M≠0)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  rw [show 1/q-2=(1-2*q)/q by field_simp, div_pow]
  simp only [pow_add, pow_one, mul_pow]
  field_simp

 theorem normalize_upper_companion (M b : ℕ) (q B : ℚ) (hq : q≠0) :
    q^(M+b)*2^b*(1/q-2)^M*B=(1-2*q)^M*((2*q)^b*B) := by
  rw [show 1/q-2=(1-2*q)/q by field_simp, div_pow, pow_add, mul_pow]
  field_simp

 theorem normalized_lower (L t r : ℕ) (hL : 0<L)
    (h : t+r=2^L) (hr : 2*r<2^L) (q : ℚ) (hq : q≠0) :
    normalizedPair L (2^L+(r+1)) q=
      ((-1)^r*((1-2*q)^(2*r+1)*(normalizedPair (L-1) t 1).1-
        q*(1-2*q)^(2*r)*(normalizedPair (L-1) t 1).2),
       (-1)^r*(1-2*q)^(2*r+1)*(normalizedPair (L-1) t 1).2) := by
  have he : normalizationExponent L (2^L+(r+1))=2*r+1 := by
    unfold normalizationExponent
    rw [pow_succ]
    omega
  have hp := lower_pair_recurrence L t r hL h hr (1/q)
  simp only [normalizedPair, he, one_pow, one_div_one, one_mul]
  rw [hp.1, hp.2]
  apply Prod.ext <;> dsimp
  · have ha := normalize_lower_algebra r q (hankel (L-1) t 1)
      (derivativeCompanion (L-1) t 1) hq
    linear_combination (-1 : ℚ)^r*ha
  · have ha := normalize_lower_companion r q (derivativeCompanion (L-1) t 1) hq
    linear_combination (-1 : ℚ)^r*ha

 theorem normalized_upper (L a b : ℕ) (hL : 2 ≤ L)
    (h : a+b+1+a=2^L) (q : ℚ) (hq : q≠0) :
    normalizedPair L (2^L+(a+b+1)) q=
      ((1-2*q)^(2^L)*(normalizedPair (L-1) (a+b+1) (2*q)).1-
        q*(1-2*q)^(2^L-1)*(normalizedPair (L-1) (a+b+1) (2*q)).2,
       (1-2*q)^(2^L)*(normalizedPair (L-1) (a+b+1) (2*q)).2) := by
  have he : normalizationExponent L (2^L+(a+b+1))=2^L+b := by
    unfold normalizationExponent
    rw [pow_succ]
    omega
  have hc : normalizationExponent (L-1) (a+b+1)=b := by
    unfold normalizationExponent
    rw [show L-1+1=L by omega]
    omega
  have hp := upper_pair_recurrence L a b hL h (1/q)
  simp only [normalizedPair, he, hc]
  rw [hp.1, hp.2]
  have hq' : 1/q/2=1/(2*q) := by ring
  rw [hq']
  apply Prod.ext <;> dsimp
  · simpa only [mul_assoc] using normalize_upper_algebra (2^L) b (by positivity) q
      (hankel (L-1) (a+b+1) (1/(2*q))) (derivativeCompanion (L-1) (a+b+1) (1/(2*q))) hq
  · simpa only [mul_assoc] using normalize_upper_companion (2^L) b q
      (derivativeCompanion (L-1) (a+b+1) (1/(2*q))) hq

end HankelAutomaticity
