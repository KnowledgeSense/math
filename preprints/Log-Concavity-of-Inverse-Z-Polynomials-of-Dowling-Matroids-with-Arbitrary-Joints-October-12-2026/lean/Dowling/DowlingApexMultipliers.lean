import Dowling.DowlingApexAverages

noncomputable section
namespace Dowling

/-- The exact attenuation of each positive one-apex component. -/
def apexAttenuation (n k h : ℕ) : ℝ :=
  if h=0 then 1 else
    ((n-k:ℕ):ℝ)/k*((1-apexChooseRatio (n-k-1) (n-1) (2*h-1))/(2*h-1:ℕ))

theorem apexChooseRatio_lower_both (A B z : ℕ) (hA : 0<A) (hB : 0<B)
    (hz : 0<z) (hzB : z≤B) :
    apexChooseRatio A B z=(A:ℝ)/B*apexChooseRatio (A-1) (B-1) (z-1) := by
  have heA : (A:ℝ)*((A-1).choose (z-1):ℝ)=(A.choose z:ℝ)*z := by
    have h := Nat.add_one_mul_choose_eq (A-1) (z-1)
    rw [show A-1+1=A by omega,show z-1+1=z by omega] at h
    exact_mod_cast h
  have heB : (B:ℝ)*((B-1).choose (z-1):ℝ)=(B.choose z:ℝ)*z := by
    have h := Nat.add_one_mul_choose_eq (B-1) (z-1)
    rw [show B-1+1=B by omega,show z-1+1=z by omega] at h
    exact_mod_cast h
  have hc : (B.choose z:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hzB))
  have hd : ((B-1).choose (z-1):ℝ)≠0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : z-1≤B-1)))
  have hb : (B:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hB
  unfold apexChooseRatio
  field_simp
  nlinarith [congrArg (fun x:ℝ=>(B.choose z:ℝ)*x) heA,
    congrArg (fun x:ℝ=>(A.choose z:ℝ)*x) heB]

theorem apexAttenuation_nonneg (n k h : ℕ) (hk : 1≤k) (hkn : k≤n) (hh : 2*h≤n) :
    0≤apexAttenuation n k h := by
  by_cases h0 : h=0
  · simp [apexAttenuation,h0]
  · rw [apexAttenuation,ite_eq_right h0]
    have hratio : apexChooseRatio (n-k-1) (n-1) (2*h-1)≤1 := by
      have h := apexChooseRatio_antitone (n-k-1) (n-1) 0 (2*h-1) (by omega)
        (by omega) (by omega)
      simpa [apexChooseRatio_zero] using h
    apply mul_nonneg (by positivity)
    exact div_nonneg (by linarith) (by positivity)

theorem apexAttenuation_positive_indices (n k i j : ℕ) (hk : 1≤k) (hkn : k≤n)
    (hi : 1 ≤ i) (hij : i≤j) (hj : 2*j≤n) :
    apexAttenuation n k j≤apexAttenuation n k i := by
  by_cases hnk : n=k
  · subst n
    simp [apexAttenuation,show i≠0 by omega,show j≠0 by omega]
  · rw [apexAttenuation,ite_eq_right (by omega : j≠0),
      apexAttenuation,ite_eq_right (by omega : i≠0)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact apexChooseRatio_defect_average_antitone (n-k-1) (n-1) (2*i-1) (2*j-1)
      (by omega) (by omega) (by omega) (by omega)

theorem apexAttenuation_one (n k : ℕ) (hn : 2≤n) (hk : 1≤k) (hkn : k≤n) :
    apexAttenuation n k 1=((n-k:ℕ):ℝ)/(n-1:ℕ) := by
  by_cases hnk : n=k
  · subst n
    simp [apexAttenuation]
  · have hgap : 1≤n-k := by omega
    have hkR : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<k))
    have hnR : ((n-1:ℕ):ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<n-1))
    rw [apexAttenuation,ite_eq_right (by omega : (1:ℕ)≠0)]
    simp only [show 2*1-1=1 by omega,
      apexChooseRatio,Nat.choose_one_right,Nat.cast_one,div_one]
    have hcast : ((n-k-1:ℕ):ℝ)=((n-1:ℕ):ℝ)-(k:ℝ) := by
      simp only [Nat.cast_sub hgap,Nat.cast_sub hkn,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
      ring
    rw [hcast]
    field_simp
    ring

theorem apexAttenuation_antitone (n k i j : ℕ) (hn : 2≤n) (hk : 1≤k) (hkn : k≤n)
    (hij : i≤j) (hj : 2*j≤n) : apexAttenuation n k j≤apexAttenuation n k i := by
  by_cases hi : i=0
  · subst i
    by_cases hj0 : j=0
    · subst j; rfl
    · have hfirst := apexAttenuation_positive_indices n k 1 j hk hkn le_rfl (by omega) hj
      rw [apexAttenuation_one n k hn hk hkn] at hfirst
      have hbound : ((n-k:ℕ):ℝ)/(n-1:ℕ)≤1 := by
        apply (div_le_one (by exact_mod_cast (show 0<n-1 by omega))).mpr
        exact_mod_cast (show n-k≤n-1 by omega)
      simpa [apexAttenuation] using hfirst.trans hbound
  · exact apexAttenuation_positive_indices n k i j hk hkn (by omega) hij hj

theorem apexAttenuation_coefficient (n k h : ℕ) (hk : 1≤k) (hkn : k≤n)
    (hh : 1≤h) (hhn : 2*h≤n) :
    (k:ℝ)/n*(2*h-1:ℕ)*apexAttenuation n k h=
      ((n-k:ℕ):ℝ)/n-((n-k).choose (2*h):ℝ)/(n.choose (2*h):ℝ) := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<k))
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<n))
  have hh0 : ((2*h-1:ℕ):ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<2*h-1))
  by_cases hnk : n=k
  · subst n
    simp [apexAttenuation,show h≠0 by omega,Nat.choose_eq_zero_of_lt (show 0<2*h by omega)]
  · have hratio := apexChooseRatio_lower_both (n-k) n (2*h) (by omega) (by omega) (by omega) hhn
    change _=((n-k:ℕ):ℝ)/n-apexChooseRatio (n-k) n (2*h)
    rw [hratio,apexAttenuation,ite_eq_right (by omega : h≠0)]
    field_simp

end Dowling
