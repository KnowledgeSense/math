import ASR312.SeriesDefinitions
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace ASR312

open PowerSeries

noncomputable def T (a b : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (S (n+a) (n+b) n : ℚ))

noncomputable def U (a : ℕ) : PowerSeries ℚ := (invOneSubPow ℚ a).val

@[simp] theorem coeff_T (a b n : ℕ) : coeff n (T a b) = (S (n+a) (n+b) n : ℚ) := by simp [T]
@[simp] theorem constantCoeff_T (a b : ℕ) : constantCoeff (T a b) = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply,S_zero]

@[simp] theorem U_zero : U 0 = 1 := rfl
@[simp] theorem constantCoeff_U (a : ℕ) : constantCoeff (U a) = 1 := by
  cases a with
  | zero => simp
  | succ a => simp [U,invOneSubPow,← coeff_zero_eq_constantCoeff_apply]

theorem coeff_U_succ (a n : ℕ) : coeff (n+1) (U a) = ((a+n).choose (n+1) : ℚ) := by
  cases a with
  | zero => simp
  | succ a =>
    simp only [U,invOneSubPow,coeff_mk]
    congr 1
    have hh := Nat.choose_symm (show a ≤ a+(n+1) by omega)
    have he : a+(n+1)-a = n+1 := by omega
    rw [he] at hh
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hh.symm

theorem coeff_U_pos (a n : ℕ) (hn : 0 < n) : coeff n (U a) = ((a+n-1).choose n : ℚ) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change coeff (t+1) (U a) = ((a+(t+1)-1).choose (t+1) : ℚ)
  rw [show a+(t+1)-1 = a+t by omega]
  exact coeff_U_succ a t

theorem U_mul_one_sub_X_pow (a : ℕ) : U a * (1-X : PowerSeries ℚ)^a = 1 := by
  have hh := (invOneSubPow ℚ a).val_inv
  rw [invOneSubPow_inv_eq_one_sub_pow] at hh
  exact hh

theorem U_eq_inv_one_sub_X_pow (a : ℕ) : U a = ((1-X : PowerSeries ℚ)⁻¹)^a := by
  have hinv := PowerSeries.mul_inv_cancel (1-X : PowerSeries ℚ) (by simp)
  calc
    U a = U a * ((1-X)^a * ((1-X)⁻¹)^a) := by rw [← mul_pow,hinv,one_pow,mul_one]
    _ = ((1-X)⁻¹)^a := by rw [← mul_assoc,U_mul_one_sub_X_pow,one_mul]

theorem T_square : T 0 0 = 1+X*R := by
  ext n
  cases n with
  | zero => simp [S_zero]
  | succ n =>
    simp only [coeff_T,Nat.add_zero,map_add,coeff_one,show n+1 ≠ 0 by omega,ite_false,zero_add,
      coeff_succ_X_mul,coeff_R]
    rw [S_square_schroder]

theorem two_mul_P : (2 : PowerSeries ℚ)*P = 1+X*R := by
  unfold P
  calc
    2*(C (1/2)*(1+X*R)) = (C (1/2)*2)*(1+X*R) := by ring
    _ = 1+X*R := by rw [C_half_mul_two,one_mul]

theorem emptyFirstRow_count_le_S (r k d : ℕ) (hd : d ≤ k) : r.choose d ≤ S (r+1) k d := by
  classical
  let f : EmptyFirstRowRectangles r k d → AvoidingRectangle (r+1) k d :=
    fun A => ⟨A.val,A.property.1,A.property.2.1,A.property.2.2.1⟩
  have hf : Function.Injective f := by
    intro A B h
    exact Subtype.ext (congrArg (fun C : AvoidingRectangle (r+1) k d => C.val) h)
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card,emptyFirstRow_count r k d hd,Nat.card_eq_fintype_card] at hh
  exact hh

end ASR312
