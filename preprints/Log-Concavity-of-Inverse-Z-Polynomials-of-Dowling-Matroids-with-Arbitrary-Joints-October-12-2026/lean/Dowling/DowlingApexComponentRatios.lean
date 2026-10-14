import Dowling.ActualApexWeightsDefinitions
import Dowling.DowlingApexMultipliers

noncomputable section
namespace Dowling

theorem apexF_pos (n h j : ℕ) (hh : h≤j) (hj : 2*j≤n) : 0<apexF n h j := by
  have hD : (0:ℝ)<(j.descFactorial h:ℝ) := by exact_mod_cast Nat.descFactorial_pos.mpr hh
  have hL : 0<((n:ℝ)+1)/2-h := by
    have hb : (2*h:ℝ)≤n := by exact_mod_cast (show 2*h≤n by omega)
    linarith
  rw [apexF,ite_eq_left hh]
  positivity

theorem apexF_nonneg (n h j : ℕ) (hj : 2*j≤n) : 0≤apexF n h j := by
  by_cases hh : h≤j
  · exact (apexF_pos n h j hh hj).le
  · simp [apexF,hh]

theorem apexF_zero_component (n j : ℕ) : apexF n 0 j=1 := by
  have hL : ((n:ℝ)+1)/2≠0 := by positivity
  simp only [apexF,Nat.zero_le,ite_eq_left,Nat.descFactorial_zero,Nat.cast_one,Nat.cast_zero,
    sub_zero,Nat.sub_zero,one_mul]
  field_simp

theorem apexF_succ (n h j : ℕ) (hh : h≤j) (hj : 2*(j+1)≤n) :
    apexF n h (j+1)=apexF n h j*
      ((((n:ℝ)+1)/2-h)*(j+1)/((((n:ℝ)+1)/2)*(j+1-h))) := by
  have hcast : ((j+1-h:ℕ):ℝ)=(j:ℝ)+1-h := by
    rw [Nat.cast_sub (by omega : h≤j+1),Nat.cast_add,Nat.cast_one]
  have hd : ((j:ℝ)+1-h)*((j+1).descFactorial h:ℝ)=((j:ℝ)+1)*(j.descFactorial h:ℝ) := by
    have hhN : (j+1-h)*(j+1).descFactorial h=(j+1)*j.descFactorial h := by
      rw [← Nat.descFactorial_succ,Nat.succ_descFactorial_succ]
    rw [← hcast]
    exact_mod_cast hhN
  have hL : 0<((n:ℝ)+1)/2 := by positivity
  have hLH : 0<((n:ℝ)+1)/2-h := by
    have hR : (2*(j+1):ℝ)≤n := by exact_mod_cast hj
    have hhR : (h:ℝ)≤j := by exact_mod_cast hh
    linarith
  have hgap : (j:ℝ)+1-h≠0 := by
    have hhR : (h:ℝ)≤j := by exact_mod_cast hh
    linarith
  simp only [apexF,ite_eq_left hh,ite_eq_left (show h≤j+1 by omega),
    show j+1-h=(j-h)+1 by omega,pow_succ]
  generalize ((n:ℝ)+1)/2=L at *
  field_simp
  nlinarith [congrArg (fun x:ℝ=>x*(L-h)^(j-h)*L^2) hd]

theorem apexF_pred (n h j : ℕ) (hh : h≤j) (hj0 : 1≤j) (hj : 2*j≤n) :
    apexF n h (j-1)=apexF n h j*
      ((((n:ℝ)+1)/2)*((j:ℝ)-h)/(((((n:ℝ)+1)/2)-h)*j)) := by
  by_cases heq : h=j
  · subst h
    simp [apexF,show ¬j≤j-1 by omega]
  · have hs := apexF_succ n h (j-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel hj0] at hs
    simp only [Nat.cast_sub hj0,Nat.cast_one,sub_add_cancel] at hs
    have hL : 0<((n:ℝ)+1)/2 := by positivity
    have hLH : 0<((n:ℝ)+1)/2-h := by
      have hb : (2*h:ℝ)≤n := by exact_mod_cast (show 2*h≤n by omega)
      linarith
    have hjR : (j:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0<j)
    have hgap : (j:ℝ)-h≠0 := by
      have hhR : (h:ℝ)<j := by exact_mod_cast (show h<j by omega)
      linarith
    generalize ((n:ℝ)+1)/2=L at *
    field_simp at hs ⊢
    nlinarith

def apexCurvatureRatio (L j h : ℝ) : ℝ :=
  h*(h*(j+(L-j)^2)-L^2)/(L*j*(L-h)*(j+1-h))

theorem apexF_curvature (n h j : ℕ) (hh : h≤j) (hj0 : 1≤j) (hj : 2*(j+1)≤n) :
    apexF n h (j-1)+apexF n h (j+1)-2*apexF n h j=
      apexF n h j*apexCurvatureRatio (((n:ℝ)+1)/2) j h := by
  rw [apexF_pred n h j hh hj0 (by omega),apexF_succ n h j hh hj]
  have hL : 0<((n:ℝ)+1)/2 := by positivity
  have hLH : 0<((n:ℝ)+1)/2-h := by
    have hb : (2*h:ℝ)≤n := by exact_mod_cast (show 2*h≤n by omega)
    linarith
  have hjR : (j:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0<j)
  have hgap : (j:ℝ)+1-h≠0 := by
    have hhR : (h:ℝ)≤j := by exact_mod_cast hh
    linarith
  unfold apexCurvatureRatio
  generalize ((n:ℝ)+1)/2=L at *
  field_simp
  ring

end Dowling
