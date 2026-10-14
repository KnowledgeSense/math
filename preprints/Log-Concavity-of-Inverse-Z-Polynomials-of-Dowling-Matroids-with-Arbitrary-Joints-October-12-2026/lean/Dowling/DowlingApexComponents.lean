import Dowling.DowlingApexCrossing

noncomputable section
namespace Dowling

def apexComponentCoefficient (n h : ℕ) : ℝ :=
  if h=0 then 1/n else ((2*h-1:ℕ):ℝ)/n*apexTauWeight h

def apexComponent (n h j : ℕ) : ℝ := apexComponentCoefficient n h*apexF n h j

def apexComponentDefect (n j : ℕ) (B : ℝ) (h : ℕ) : ℝ :=
  apexComponent n h (j-1)+apexComponent n h (j+1)-(2+B)*apexComponent n h j

theorem apexComponentCoefficient_pos (n h : ℕ) (hn : 0<n) : 0<apexComponentCoefficient n h := by
  by_cases hh : h=0
  · simp only [apexComponentCoefficient,ite_eq_left hh]
    positivity
  · rw [apexComponentCoefficient,ite_eq_right hh]
    have hN : (0:ℝ)<n := by exact_mod_cast hn
    have hH : (0:ℝ)<(2*h-1:ℕ) := by exact_mod_cast (show 0<2*h-1 by omega)
    exact mul_pos (div_pos hH hN) (apexTauWeight_pos h (by omega))

theorem apexComponentDefect_factor (n j h : ℕ) (B : ℝ) (hh : h≤j) (hj : 1≤j)
    (hjn : 2*(j+1)≤n) :
    apexComponentDefect n j B h=apexComponent n h j*
      (apexCurvatureRatio (((n:ℝ)+1)/2) j h-B) := by
  have hcurv := apexF_curvature n h j hh hj hjn
  unfold apexComponentDefect apexComponent
  nlinarith [congrArg (fun x:ℝ=>apexComponentCoefficient n h*x) hcurv]

theorem apexComponentDefect_entering (n j : ℕ) (B : ℝ) (hj : 1≤j)
    (hjn : 2*(j+1)≤n) : 0≤apexComponentDefect n j B (j+1) := by
  unfold apexComponentDefect apexComponent
  have hp : apexF n (j+1) (j-1)=0 := by simp [apexF,show ¬j+1≤j-1 by omega]
  have hc : apexF n (j+1) j=0 := by simp [apexF,show ¬j+1≤j by omega]
  rw [hp,hc]
  simp only [mul_zero,zero_add,sub_zero]
  exact mul_nonneg (apexComponentCoefficient_pos n (j+1) (by omega)).le
    (apexF_nonneg n (j+1) (j+1) hjn)

theorem apexComponentDefect_above (n j h : ℕ) (B : ℝ) (hh : j+1<h) :
    apexComponentDefect n j B h=0 := by
  simp [apexComponentDefect,apexComponent,apexF,show ¬h≤j-1 by omega,
    show ¬h≤j+1 by omega,show ¬h≤j by omega]

theorem apexComponentDefect_single_crossing (n j : ℕ) (B : ℝ) (hB : 0≤B)
    (hj : 1≤j) (hjn : 2*(j+1)≤n) (i h : ℕ) (hih : i<h)
    (hi : 0<apexComponentDefect n j B i) : 0≤apexComponentDefect n j B h := by
  by_cases hh : j+1<h
  · rw [apexComponentDefect_above n j h B hh]
  by_cases heq : h=j+1
  · subst h
    exact apexComponentDefect_entering n j B hj hjn
  have hhj : h≤j := by omega
  have hij : i≤j := by omega
  rw [apexComponentDefect_factor n j i B hij hj hjn] at hi
  have hci : 0<apexComponent n i j := mul_pos
    (apexComponentCoefficient_pos n i (by omega)) (apexF_pos n i j hij (by omega))
  have hri : B<apexCurvatureRatio (((n:ℝ)+1)/2) j i := by nlinarith
  have hi0 : 0 < i := by
    by_contra hz
    have hi0 : i=0 := by omega
    simp [hi0,apexCurvatureRatio] at hri
    linarith
  have hL : (j:ℝ)<((n:ℝ)+1)/2 := by
    have hb : (2*(j+1):ℝ)≤n := by exact_mod_cast hjn
    linarith
  have hmono := apexCurvatureRatio_positive_monotone (((n:ℝ)+1)/2) j i h
    (by exact_mod_cast (show 0<j by omega)) hL (by exact_mod_cast hi0)
    (by exact_mod_cast hih.le) (by exact_mod_cast hhj) (by linarith)
  rw [apexComponentDefect_factor n j h B hhj hj hjn]
  apply mul_nonneg
  · exact (mul_pos (apexComponentCoefficient_pos n h (by omega))
      (apexF_pos n h j hhj (by omega))).le
  · linarith

end Dowling
