import Dowling.DowlingMixtureBalancing

noncomputable section
namespace Dowling

theorem dowlingQuadraticWeight_factor {c : ℝ} (hc : c≠0) (j : ℕ) :
    dowlingQuadraticWeight c j=(c-j)*c^j/(c*j.factorial) := by
  cases j with
  | zero => simp [hc]
  | succ j =>
    rw [dowlingQuadraticWeight_succ,pow_succ]
    push_cast
    field_simp

theorem dowlingQuadraticWeight_ratio {c : ℝ} {j : ℕ} (hc : 0<c)
    (hj : (j+1 : ℝ)<c) :
    dowlingQuadraticWeight c (j+1)/dowlingQuadraticWeight c j=
      c/(j+1)*((c-j-1)/(c-j)) := by
  rw [dowlingQuadraticWeight_factor (ne_of_gt hc),
    dowlingQuadraticWeight_factor (ne_of_gt hc),Nat.factorial_succ,pow_succ]
  push_cast
  have hcj : c-(j : ℝ)≠0 := by linarith
  have hpow : c^j≠0 := pow_ne_zero _ (ne_of_gt hc)
  have hf : (j.factorial : ℝ)≠0 := by positivity
  have hj1 : (j+1 : ℝ)≠0 := by positivity
  field_simp
  ring

theorem dowlingQuadraticWeight_ratio_antitone {c : ℝ} (hc : 0<c)
    (r s : ℕ) (hrs : r<s) (hs : (s+1 : ℝ)<c) :
    dowlingQuadraticWeight c (s+1)/dowlingQuadraticWeight c s <
      dowlingQuadraticWeight c (r+1)/dowlingQuadraticWeight c r := by
  have hrs' : (r : ℝ)<s := by exact_mod_cast hrs
  have hr : (r+1 : ℝ)<c := by linarith
  rw [dowlingQuadraticWeight_ratio hc hs,dowlingQuadraticWeight_ratio hc hr]
  have hfirst : c/(s+1)<c/(r+1) := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ)<s+1) (by positivity : (0 : ℝ)<r+1)).mpr
    nlinarith
  have hsecond : (c-s-1)/(c-s)<(c-r-1)/(c-r) := by
    apply (div_lt_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hright : 0<(c-r-1)/(c-r) := div_pos (by linarith) (by linarith)
  calc
    _ ≤ c/(s+1)*((c-r-1)/(c-r)) := mul_le_mul_of_nonneg_left (le_of_lt hsecond) (by positivity)
    _ < _ := mul_lt_mul_of_pos_right hfirst hright

theorem dowlingQuadraticWeight_strict_step {c : ℝ} (hc : 0<c)
    (r s : ℕ) (hrs : r<s) (hs : (s+1 : ℝ)<c) :
    dowlingQuadraticWeight c r*dowlingQuadraticWeight c (s+1)<
      dowlingQuadraticWeight c (r+1)*dowlingQuadraticWeight c s := by
  have hr : (r : ℝ)<c := by
    have : (r : ℝ)<s := by exact_mod_cast hrs
    linarith
  have hs' : (s : ℝ)<c := by linarith
  have h := (div_lt_div_iff₀ (dowlingQuadraticWeight_pos hc hs')
    (dowlingQuadraticWeight_pos hc hr)).mp (dowlingQuadraticWeight_ratio_antitone hc r s hrs hs)
  nlinarith

 theorem dowlingQuadraticWeight_balance {c : ℝ} (hc : 0<c)
    (r s u v : ℕ) (hru : r≤u) (huv : u≤v) (hvs : v≤s) (hsum : r+s=u+v)
    (hs : (s : ℝ)<c) :
    dowlingQuadraticWeight c r*dowlingQuadraticWeight c s≤
      dowlingQuadraticWeight c u*dowlingQuadraticWeight c v := by
  induction d : u-r generalizing r s u v with
  | zero =>
    have hu : u=r := by omega
    have hv : v=s := by omega
    simp [hu,hv]
  | succ d ih =>
    have hrs : r<s-1 := by omega
    have hs1 : s-1+1=s := by omega
    have hbound : ((s-1 : ℕ)+1 : ℝ)<c := by exact_mod_cast (show ((s-1+1 : ℕ) : ℝ)<c by simpa [hs1] using hs)
    have hfirst := dowlingQuadraticWeight_strict_step hc r (s-1) hrs hbound
    rw [hs1] at hfirst
    apply le_trans (le_of_lt hfirst)
    apply ih (r+1) (s-1) u v (by omega) huv (by omega) (by omega)
    · have hle : ((s-1 : ℕ) : ℝ)≤s := by exact_mod_cast (Nat.sub_le s 1)
      linarith
    · omega

 theorem dowlingQuadraticWeight_midpoint {c : ℝ} (hc : 0<c) (r s : ℕ)
    (hr : (r : ℝ)<c) (hs : (s : ℝ)<c) :
    dowlingQuadraticWeight c r*dowlingQuadraticWeight c s≤
      dowlingQuadraticWeight c ((r+s)/2)*dowlingQuadraticWeight c ((r+s+1)/2) := by
  by_cases hrs : r≤s
  · apply dowlingQuadraticWeight_balance hc r s _ _ (by omega) (by omega) (by omega) (by omega) hs
  · rw [mul_comm (dowlingQuadraticWeight c r)]
    apply dowlingQuadraticWeight_balance hc s r _ _ (by omega) (by omega) (by omega) (by omega) hr

end Dowling
