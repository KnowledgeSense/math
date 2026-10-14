import SumsetRanges.GeometricSeriesOrder
import SumsetRanges.BinomialBounds

open Finset
namespace SumsetRanges

def ordinaryBeta (c d : ℕ) : ℕ := (c+d-1).choose d

theorem coeff_geometricSeries_pow (c d : ℕ) (hc : 1≤c) :
    PowerSeries.coeff d (geometricSeries^c)=(ordinaryBeta c d : ℤ) := by
  have he : c=c-1+1 := by omega
  rw [he]
  change PowerSeries.coeff d ((PowerSeries.mk 1 : PowerSeries ℤ)^(c-1+1))=_
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
  simp only [PowerSeries.coeff_mk]
  congr 1
  unfold ordinaryBeta
  have hd : c-1≤c-1+d := by omega
  rw [←Nat.choose_symm hd]
  congr 1 <;> omega

theorem ordinaryBeta_recurrence (c d : ℕ) (hc : 1≤c) :
    (c+d)*ordinaryBeta c d=(d+1)*ordinaryBeta c (d+1) := by
  have he := Nat.add_one_mul_choose_eq (c+d-1) d
  have h1 : c+d-1+1=c+d := by omega
  have h2 : c+(d+1)-1=c+d := by omega
  simpa [ordinaryBeta,h1,h2,mul_comm] using he

theorem ordinaryBeta_half (h c n d : ℕ) (hh : 1≤h) (hc : 2*h≤c)
    (hn : 1≤n) (hnc : n≤c) (hgap : 4*h*(c-n)≤c) (hd : d≤h) :
    ordinaryBeta c d≤2*ordinaryBeta n d := by
  by_cases hd0 : d=0
  · subst d; simp [ordinaryBeta]
  have hdp : 1≤d := by omega
  apply choose_le_twice_choose h (c+d-1) (n+d-1) d hh (by omega) (by omega) _ hd
  have he : c+d-1-(n+d-1)=c-n := by omega
  rw [he]
  omega

theorem ordinaryBeta_double (h c d : ℕ) (hh : 1≤h) (hc : 2*h≤c) (hd : d<h) :
    2*ordinaryBeta c d≤ordinaryBeta c (d+1) := by
  have he := ordinaryBeta_recurrence c d (by omega)
  have hs : 2*(d+1)≤c+d := by omega
  have hp := Nat.mul_le_mul_right (ordinaryBeta c d) hs
  apply Nat.le_of_mul_le_mul_left (c := d+1) _ (by omega)
  nlinarith

theorem ordinaryBeta_partial_sum (h c d : ℕ) (hh : 1≤h) (hc : 2*h≤c) (hd : d<h) :
    (∑j∈range (d+1),ordinaryBeta c j)≤2*ordinaryBeta c d := by
  induction d with
  | zero => simp [ordinaryBeta]
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := ordinaryBeta_double h c d hh hc (by omega)
      omega

theorem sum_Icc_ordinaryBeta_sub (c D : ℕ) (hD : 1≤D) :
    (∑e∈Icc 2 D,ordinaryBeta c (D-e))=∑j∈range (D-1),ordinaryBeta c j := by
  refine Finset.sum_bij (fun e _ => D-e) ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_Icc] at he
    simp only [mem_range]
    omega
  · intro e he f hf hef
    simp only [mem_Icc] at he hf
    omega
  · intro j hj
    simp only [mem_range] at hj
    refine ⟨D-j,?_,?_⟩
    · simp only [mem_Icc]; omega
    · omega
  · intro e _; rfl

theorem ordinaryBeta_tail_scaled (h c D : ℕ) (hh : 1≤h) (hc : 2*h≤c)
    (hD : 1≤D) (hDh : D≤h) :
    c*(∑e∈Icc 2 D,ordinaryBeta c (D-e))≤2*h*ordinaryBeta c (D-1) := by
  rw [sum_Icc_ordinaryBeta_sub c D hD]
  by_cases hd : D=1
  · subst D; simp
  have hs := ordinaryBeta_partial_sum h c (D-2) hh hc (by omega)
  have he : D-2+1=D-1 := by omega
  rw [he] at hs
  have hr := ordinaryBeta_recurrence c (D-2) (by omega)
  rw [he] at hr
  have hp := Nat.mul_le_mul_left c hs
  have hc' : c*ordinaryBeta c (D-2)≤(D-1)*ordinaryBeta c (D-1) := by nlinarith
  have hmul := Nat.mul_le_mul_right (ordinaryBeta c (D-1)) (show D-1≤h by omega)
  nlinarith

end SumsetRanges
