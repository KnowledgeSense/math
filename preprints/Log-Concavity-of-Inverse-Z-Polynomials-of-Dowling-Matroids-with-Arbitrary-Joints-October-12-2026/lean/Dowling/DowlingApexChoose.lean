import Dowling.DowlingApexAttenuation

noncomputable section
namespace Dowling

def apexChooseRatio (A B z : ℕ) : ℝ := (A.choose z:ℝ)/(B.choose z:ℝ)

theorem apexChooseRatio_nonneg (A B z : ℕ) : 0≤apexChooseRatio A B z := by
  unfold apexChooseRatio
  positivity

theorem apexChooseRatio_zero (A B : ℕ) : apexChooseRatio A B 0=1 := by
  simp [apexChooseRatio]

theorem apexChooseRatio_step (A B z : ℕ) (hz : z<B) :
    apexChooseRatio A B (z+1)=apexChooseRatio A B z*((A-z:ℕ):ℝ)/(B-z:ℕ) := by
  have hA : (A.choose (z+1):ℝ)*(z+1)=(A.choose z:ℝ)*(A-z:ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq A z
  have hB : (B.choose (z+1):ℝ)*(z+1)=(B.choose z:ℝ)*(B-z:ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq B z
  have hC : (B.choose z:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : z≤B)))
  have hD : (B.choose (z+1):ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : z+1≤B)))
  have hgap : ((B-z:ℕ):ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<B-z))
  have hz1 : (z+1:ℝ)≠0 := by positivity
  apply (mul_right_cancel₀ hz1)
  unfold apexChooseRatio
  field_simp
  nlinarith [hA,hB]

theorem apexChooseRatio_antitone_step (A B z : ℕ) (hAB : A≤B) (hz : z<B) :
    apexChooseRatio A B (z+1)≤apexChooseRatio A B z := by
  rw [apexChooseRatio_step A B z hz]
  have hg : (0:ℝ)<(B-z:ℕ) := by exact_mod_cast (show 0<B-z by omega)
  apply (div_le_iff₀ hg).mpr
  apply mul_le_mul_of_nonneg_left _ (apexChooseRatio_nonneg A B z)
  exact_mod_cast Nat.sub_le_sub_right hAB z

theorem apexChooseRatio_lower_denominator (A B z : ℕ) (hz : z<B) :
    apexChooseRatio A B z=((B-z:ℕ):ℝ)/B*apexChooseRatio A (B-1) z := by
  have he : ((B-1).choose z:ℝ)*B=(B.choose z:ℝ)*(B-z:ℕ) := by
    have h := Nat.choose_mul_succ_eq (B-1) z
    rw [show B-1+1=B by omega] at h
    exact_mod_cast h
  have hc : (B.choose z:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : z≤B)))
  have hd : ((B-1).choose z:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : z≤B-1)))
  have hb : (B:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<B))
  unfold apexChooseRatio
  field_simp
  nlinarith [congrArg (fun x:ℝ=>(A.choose z:ℝ)*x) he]

theorem apexChooseRatio_difference (A B z : ℕ) (hAB : A<B) (hz : z<B) :
    apexChooseRatio A B z-apexChooseRatio A B (z+1)=
      ((B-A:ℕ):ℝ)/B*apexChooseRatio A (B-1) z := by
  by_cases hzA : z≤A
  · rw [apexChooseRatio_step A B z hz,apexChooseRatio_lower_denominator A B z hz]
    have hg : ((B-z:ℕ):ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<B-z))
    have hb : (B:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0<B))
    have hgap : ((B-z:ℕ):ℝ)-((A-z:ℕ):ℝ)=((B-A:ℕ):ℝ) := by
      simp only [Nat.cast_sub hzA,Nat.cast_sub (by omega : z≤B),Nat.cast_sub hAB.le]
      ring
    field_simp
    nlinarith [congrArg (fun x:ℝ=>x*apexChooseRatio A (B-1) z) hgap]
  · have hAz : A<z := by omega
    simp [apexChooseRatio,Nat.choose_eq_zero_of_lt hAz,
      Nat.choose_eq_zero_of_lt (show A<z+1 by omega)]

end Dowling
