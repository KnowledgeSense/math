import Paving.SeparatedRatios
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
namespace Paving

def uniformComponent (k n i : ℕ) : ℝ :=
  ((k-1).choose i:ℝ)*((n:ℝ)-k+1)/((n:ℝ)-i)

def hyperplaneComponent (k n h i : ℕ) : ℝ :=
  ((k-1).choose i:ℝ)*((k:ℝ)-1-i)*((n:ℝ)-h)/
    (((n:ℝ)-i)*((h:ℝ)-i))

theorem uniformComponent_positive {k n i : ℕ} (hik : i < k) (hkn : k ≤ n) :
    0 < uniformComponent k n i := by
  have hc : 0 < ((k-1).choose i:ℝ) := by
    exact_mod_cast Nat.choose_pos (show i ≤ k-1 by omega)
  have hki : (i:ℝ) < k := by exact_mod_cast hik
  have hnk : (k:ℝ) ≤ n := by exact_mod_cast hkn
  unfold uniformComponent
  exact div_pos (mul_pos hc (by linarith)) (by linarith)

theorem hyperplaneComponent_positive {k n h i : ℕ}
    (hik : i+1 < k) (hkh : k ≤ h) (hhn : h < n) :
    0 < hyperplaneComponent k n h i := by
  have hc : 0 < ((k-1).choose i:ℝ) := by
    exact_mod_cast Nat.choose_pos (show i ≤ k-1 by omega)
  have hki : (i:ℝ)+1 < k := by exact_mod_cast hik
  have hhk : (k:ℝ) ≤ h := by exact_mod_cast hkh
  have hnh : (h:ℝ) < n := by exact_mod_cast hhn
  unfold hyperplaneComponent
  apply div_pos
  · exact mul_pos (mul_pos hc (by linarith)) (by linarith)
  · exact mul_pos (by linarith) (by linarith)

theorem hyperplaneComponent_difference {k n h i : ℕ}
    (hik : i < k) (hkh : k ≤ h) (hhn : h ≤ n) :
    hyperplaneComponent k n h i=uniformComponent k n i-uniformComponent k h i := by
  have hi : (i:ℝ) < k := by exact_mod_cast hik
  have hk : (k:ℝ) ≤ h := by exact_mod_cast hkh
  have hh : (h:ℝ) ≤ n := by exact_mod_cast hhn
  have hn0 : (n:ℝ)-i≠0 := by linarith
  have hh0 : (h:ℝ)-i≠0 := by linarith
  unfold hyperplaneComponent uniformComponent
  field_simp
  ring

theorem component_choose_step {k i : ℕ} (hik : i+1 ≤ k) :
    (((k-1).choose (i+1):ℝ))*((i:ℝ)+1)=
      ((k-1).choose i:ℝ)*((k:ℝ)-1-i) := by
  have h := Nat.choose_succ_right_eq (k-1) i
  have hr := congrArg (fun x:ℕ => (x:ℝ)) h
  have hk0 : 1 ≤ k := by omega
  have hi0 : i ≤ k-1 := by omega
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hi0,
    Nat.cast_sub hk0] using hr

theorem uniformComponent_step {k n i : ℕ} (hik : i+2 ≤ k) (hkn : k ≤ n) :
    uniformComponent k n (i+1)=upperRatio k n ((i:ℝ)+1)*uniformComponent k n i := by
  have hi : (i:ℝ)+2 ≤ k := by exact_mod_cast hik
  have hn : (k:ℝ) ≤ n := by exact_mod_cast hkn
  have hc := component_choose_step (show i+1 ≤ k by omega)
  have hn0 : (n:ℝ)-i≠0 := by linarith
  have hn1 : (n:ℝ)-((i:ℝ)+1)≠0 := by linarith
  have hi0 : (i:ℝ)+1≠0 := by positivity
  unfold uniformComponent upperRatio
  simp only [Nat.cast_add,Nat.cast_one]
  field_simp
  linear_combination ((n:ℝ)-k+1)*((n:ℝ)-i)*hc

theorem hyperplaneComponent_step {k n h i : ℕ}
    (hik : i+2 < k) (hkh : k ≤ h) (hhn : h < n) :
    hyperplaneComponent k n h (i+1)=
      hyperplaneRatio k n h ((i:ℝ)+1)*hyperplaneComponent k n h i := by
  have hi : (i:ℝ)+2 < k := by exact_mod_cast hik
  have hk : (k:ℝ) ≤ h := by exact_mod_cast hkh
  have hh : (h:ℝ) < n := by exact_mod_cast hhn
  have hc := component_choose_step (show i+1 ≤ k by omega)
  have hn0 : (n:ℝ)-i≠0 := by linarith
  have hn1 : (n:ℝ)-((i:ℝ)+1)≠0 := by linarith
  have hh0 : (h:ℝ)-i≠0 := by linarith
  have hh1 : (h:ℝ)-((i:ℝ)+1)≠0 := by linarith
  have hi0 : (i:ℝ)+1≠0 := by positivity
  unfold hyperplaneComponent hyperplaneRatio
  simp only [Nat.cast_add,Nat.cast_one]
  field_simp
  linear_combination ((k:ℝ)-2-i)*((n:ℝ)-h)*((n:ℝ)-i)*((h:ℝ)-i)*hc

end Paving
