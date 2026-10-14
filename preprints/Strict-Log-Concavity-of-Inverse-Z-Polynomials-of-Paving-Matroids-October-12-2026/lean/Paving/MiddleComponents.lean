import Paving.ComponentMixtures
import Paving.PenultimateComponents

noncomputable section
namespace Paving

def middleBinomial (m : ℕ) : ℝ := (2*m-1).choose (m-1)

theorem middleBinomial_positive {m : ℕ} (hm : 1 ≤ m) : 0 < middleBinomial m := by
  unfold middleBinomial
  exact_mod_cast Nat.choose_pos (show m-1 ≤ 2*m-1 by omega)

def componentPosition (m : ℕ) : Option ℕ→ℝ
  | none => (m:ℝ)-1
  | some h => (h:ℝ)-m

theorem componentPosition_bounds {m n : ℕ} (hm : 1 ≤ m) (hn : 2*m ≤ n)
    (h : Option ℕ) (hv : ValidParameter (2*m) n h) :
    (m:ℝ)-1 ≤ componentPosition m h ∧ componentPosition m h < (n:ℝ)-m := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2:ℝ)*m ≤ n := by exact_mod_cast hn
  cases h with
  | none => simp only [componentPosition]; constructor <;> linarith
  | some h =>
    have hk : (2:ℝ)*m ≤ h := by exact_mod_cast hv.1
    have hh : (h:ℝ) < n := by exact_mod_cast hv.2
    simp only [componentPosition]
    constructor <;> linarith

theorem lowerComponent_penultimate {m n : ℕ} (hm : 1 ≤ m) (hn : 2*m ≤ n)
    (h : Option ℕ) (hv : ValidParameter (2*m) n h) :
    lowerComponent (2*m) n h (m-1)=
      middleBinomial m*penultimateComponent m ((n:ℝ)-m) (componentPosition m h) := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2:ℝ)*m ≤ n := by exact_mod_cast hn
  have hm0 : (m:ℝ)≠0 := by linarith
  have hN1 : (n:ℝ)-m+1≠0 := by linarith
  cases h with
  | none =>
    unfold lowerComponent uniformComponent middleBinomial penultimateComponent componentPosition
    rw [Nat.cast_sub hm]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    field_simp (disch := first | positivity | linarith)
    ring
  | some h =>
    have hk : (2:ℝ)*m ≤ h := by exact_mod_cast hv.1
    have hh : (h:ℝ) < n := by exact_mod_cast hv.2
    have hh0 : (h:ℝ)-m+1≠0 := by linarith
    unfold lowerComponent hyperplaneComponent middleBinomial penultimateComponent componentPosition
    rw [Nat.cast_sub hm]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    field_simp (disch := first | positivity | linarith)
    ring

theorem lowerComponent_previous {m n : ℕ} (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (h : Option ℕ) (hv : ValidParameter (2*m) n h) :
    lowerComponent (2*m) n h (m-2)=
      middleBinomial m*previousComponent m ((n:ℝ)-m) (componentPosition m h) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2:ℝ)*m ≤ n := by exact_mod_cast hn
  have hN2 : (n:ℝ)-m+2≠0 := by linarith
  have hm1 : (m:ℝ)+1≠0 := by linarith
  have hc := component_choose_step (k:=2*m) (i:=m-2) (by omega)
  rw [show m-2+1=m-1 by omega,Nat.cast_sub hm] at hc
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hc
  cases h with
  | none =>
    unfold lowerComponent uniformComponent middleBinomial previousComponent componentPosition
    rw [Nat.cast_sub hm]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [show (m:ℝ)-1+2=(m:ℝ)+1 by ring]
    field_simp (disch := first | positivity | linarith)
    linear_combination -((n:ℝ)-2*m+1)*((n:ℝ)-m+2)*hc
  | some h =>
    have hk : (2:ℝ)*m ≤ h := by exact_mod_cast hv.1
    have hh : (h:ℝ) < n := by exact_mod_cast hv.2
    have hh2 : (h:ℝ)-m+2≠0 := by linarith
    unfold lowerComponent hyperplaneComponent middleBinomial previousComponent componentPosition
    rw [Nat.cast_sub hm]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    field_simp (disch := first | positivity | linarith)
    linear_combination -((n:ℝ)-h)*((n:ℝ)-m+2)*((h:ℝ)-m+2)*hc

end Paving
