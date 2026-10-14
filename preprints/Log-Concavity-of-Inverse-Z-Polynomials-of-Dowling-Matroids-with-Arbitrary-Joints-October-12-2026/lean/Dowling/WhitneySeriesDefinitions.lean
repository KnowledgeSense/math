import Dowling.WhitneyRecurrence
import Dowling.DowlingCandidateFlatCoordinate

noncomputable section
namespace Dowling
open Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]

def whitneyTerm (G : Type*) [Group G] [Fintype G] (n k : ℕ) : Polynomial ℝ :=
  C ((whitneyCount G n k : ℝ)/(n.factorial : ℝ))*X^(n-k)

def whitneySeries (G : Type*) [Group G] [Fintype G] (k : ℕ) : PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk (fun n => whitneyTerm G n k)

@[simp] theorem whitneySeries_coeff (n k : ℕ) :
    PowerSeries.coeff n (whitneySeries G k) = whitneyTerm G n k := PowerSeries.coeff_mk _ _

theorem whitneyTerm_above (n k : ℕ) (hk : n < k) : whitneyTerm G n k = 0 := by
  simp [whitneyTerm,whitneyCount_above n k hk]

theorem whitneyTerm_zero (k : ℕ) : whitneyTerm G 0 k = if k=0 then 1 else 0 := by
  simp only [whitneyTerm,whitneyCount_zero,Nat.factorial_zero,Nat.cast_one,div_one,Nat.zero_sub,
    pow_zero,mul_one]
  split <;> simp_all

@[simp] theorem whitneySeries_constant (k : ℕ) :
    (whitneySeries G k).constantCoeff = if k=0 then 1 else 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [whitneySeries_coeff,whitneyTerm_zero]

theorem whitneyTerm_zero_column (n : ℕ) :
    whitneyTerm G n 0 = C ((n.factorial : ℝ)⁻¹)*X^n := by
  simp [whitneyTerm]

theorem whitney_scaled_recurrence (n k : ℕ) :
    ((whitneyCount G (n+1) (k+1) : ℝ)/(n+1).factorial)*(n+1) =
      (whitneyCount G n k : ℝ)/n.factorial +
        (1+(Fintype.card G : ℝ)*(k+1))*((whitneyCount G n (k+1) : ℝ)/n.factorial) := by
  rw [whitneyCount_succ_succ,Nat.factorial_succ]
  push_cast
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hf : (n.factorial:ℝ) ≠ 0 := by positivity
  field_simp

theorem whitneyTerm_derivative_step (n k : ℕ) :
    whitneyTerm G (n+1) (k+1) * ((n : Polynomial ℝ)+1) = whitneyTerm G n k +
      (C (1+(Fintype.card G : ℝ)*(k+1))*X)*whitneyTerm G n (k+1) := by
  by_cases hnk : n < k
  · rw [whitneyTerm_above (n+1) (k+1) (by omega),whitneyTerm_above n k hnk,
      whitneyTerm_above n (k+1) (by omega)]
    simp
  · have hk : k ≤ n := by omega
    by_cases he : n = k
    · subst n
      rw [whitneyTerm_above k (k+1) (by omega),mul_zero,add_zero]
      unfold whitneyTerm
      simp only [Nat.sub_self,pow_zero,mul_one]
      have h := whitney_scaled_recurrence (G := G) k k
      rw [whitneyCount_above k (k+1) (by omega)] at h
      simp only [Nat.cast_zero,zero_div,mul_zero,add_zero] at h
      simpa only [map_mul,map_add,map_natCast,map_one] using congrArg C h
    · have hk' : k+1 ≤ n := by omega
      have hp : n-k = (n-(k+1))+1 := by omega
      unfold whitneyTerm
      rw [Nat.add_sub_add_right,hp,pow_succ]
      have h := congrArg C (whitney_scaled_recurrence (G := G) n k)
      simp only [map_add,map_mul,map_natCast,map_one] at h
      calc
        _ = (C ((whitneyCount G (n+1) (k+1) : ℝ)/(n+1).factorial)*((n : Polynomial ℝ)+1))*X^(n-(k+1))*X := by ring
        _ = _ := by
          rw [h]
          simp only [map_add,map_mul,map_natCast,map_one]
          ring

end Dowling
