import Dowling.DowlingMixtureBalancing

noncomputable section
namespace Dowling

 theorem finite_weight_ratio_antitone (W : ℕ→ℝ) (J : ℕ)
    (hpos : ∀ j,j≤J→0<W j)
    (hlc : ∀ j,1≤j→j<J→W (j-1)*W (j+1)≤W j^2) :
    Antitone (fun j=>if j<J then W (j+1)/W j else 0) := by
  apply antitone_nat_of_succ_le
  intro j
  by_cases hj : j+1<J
  · rw [ite_eq_left hj,ite_eq_left (show j<J by omega)]
    apply (div_le_div_iff₀ (hpos (j+1) (by omega)) (hpos j (by omega))).mpr
    have h := hlc (j+1) (by omega) hj
    simp only [Nat.add_sub_cancel] at h
    nlinarith
  · rw [ite_eq_right hj]
    split_ifs with hj'
    · exact le_of_lt (div_pos (hpos (j+1) (by omega)) (hpos j (by omega)))
    · exact le_rfl

 theorem finite_weight_step (W : ℕ→ℝ) (J : ℕ)
    (hpos : ∀ j,j≤J→0<W j)
    (hlc : ∀ j,1≤j→j<J→W (j-1)*W (j+1)≤W j^2)
    (r s : ℕ) (hrs : r<s) (hs : s<J) : W r*W (s+1)≤W (r+1)*W s := by
  have h := finite_weight_ratio_antitone W J hpos hlc (le_of_lt hrs)
  dsimp only at h
  rw [ite_eq_left hs,ite_eq_left (show r<J by omega)] at h
  have hc := (div_le_div_iff₀ (hpos s (by omega)) (hpos r (by omega))).mp h
  nlinarith

 theorem finite_weight_balance (W : ℕ→ℝ) (J : ℕ)
    (hpos : ∀ j,j≤J→0<W j)
    (hlc : ∀ j,1≤j→j<J→W (j-1)*W (j+1)≤W j^2)
    (r s u v : ℕ) (hru : r≤u) (huv : u≤v) (hvs : v≤s) (hsJ : s≤J)
    (hsum : r+s=u+v) : W r*W s≤W u*W v := by
  induction d : u-r generalizing r s u v with
  | zero =>
    have hu : u=r := by omega
    have hv : v=s := by omega
    simp [hu,hv]
  | succ d ih =>
    have hfirst := finite_weight_step W J hpos hlc r (s-1) (by omega) (by omega)
    rw [show s-1+1=s by omega] at hfirst
    exact hfirst.trans (ih (r+1) (s-1) u v (by omega) huv (by omega) (by omega) (by omega) (by omega))

 theorem finite_weight_midpoint (W : ℕ→ℝ) (J : ℕ)
    (hpos : ∀ j,j≤J→0<W j)
    (hlc : ∀ j,1≤j→j<J→W (j-1)*W (j+1)≤W j^2)
    (r s : ℕ) (hr : r≤J) (hs : s≤J) :
    W r*W s≤W ((r+s)/2)*W ((r+s+1)/2) := by
  by_cases hrs : r≤s
  · apply finite_weight_balance W J hpos hlc r s
    all_goals omega
  · rw [mul_comm (W r)]
    apply finite_weight_balance W J hpos hlc s r
    all_goals omega

end Dowling
