import SumsetRanges.OrdinaryDenseStep

namespace SumsetRanges

@[simp] theorem ordinaryWeight_zero (c b : ℕ) : ordinaryWeight c b 0=1 := by simp [ordinaryWeight,ordinaryBeta]
@[simp] theorem ordinaryWeight_one (c b : ℕ) (_hc : 1≤c) : ordinaryWeight c b 1=c+b := by
  simp [ordinaryWeight,ordinaryBeta]

theorem ordinaryWeight_nonneg (c b D : ℕ) : 0≤ordinaryWeight c b D := by
  unfold ordinaryWeight
  split_ifs <;> positivity

theorem ordinaryBeta_previous (h c D : ℕ) (hc : 1≤c) (hD : 1≤D) (hDh : D≤h) :
    ordinaryBeta c D≤(c+h)*ordinaryBeta c (D-1) := by
  have hr := ordinaryBeta_recurrence c (D-1) hc
  have he : D-1+1=D := by omega
  rw [he] at hr
  have h1 := Nat.le_mul_of_pos_left (ordinaryBeta c D) hD
  have h2 := Nat.mul_le_mul_right (ordinaryBeta c (D-1)) (show c+(D-1)≤c+h by omega)
  nlinarith

theorem ordinaryWeight_adjacent (h c b D : ℕ) (hc : h≤c) (hc0 : 1≤c)
    (hD : 1≤D) (hDh : D≤h) :
    ordinaryWeight c b D≤2*((c+b : ℕ):ℤ)*ordinaryWeight c b (D-1) := by
  by_cases he : D=1
  · subst D
    rw [ordinaryWeight_one c b hc0,ordinaryWeight_zero]
    push_cast
    nlinarith
  · have hD0 : D≠0 := by omega
    have hD1 : D-1≠0 := by omega
    simp only [ordinaryWeight,ite_eq_right hD0,ite_eq_right hD1]
    have ha : (ordinaryBeta c D : ℤ)≤((c+h:ℕ):ℤ)*ordinaryBeta c (D-1) := by
      exact_mod_cast ordinaryBeta_previous h c D hc0 hD hDh
    have hb : (ordinaryBeta c (D-1) : ℤ)≤((c+h:ℕ):ℤ)*ordinaryBeta c (D-1-1) := by
      exact_mod_cast ordinaryBeta_previous h c (D-1) hc0 (by omega) (by omega)
    have hm := mul_le_mul_of_nonneg_left hb (Int.natCast_nonneg b)
    have hcb : ((c+h:ℕ):ℤ)≤2*((c+b:ℕ):ℤ) := by omega
    have hw : 0≤(ordinaryBeta c (D-1):ℤ)+(b:ℤ)*ordinaryBeta c (D-1-1) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcb hw
    nlinarith

theorem ordinaryBeta_dense_previous (h c : ℕ) (hh : 3≤h) (hc : h≤c) :
    ordinaryBeta c (h-2)≤2*c*ordinaryBeta c (h-3) := by
  have he := ordinaryBeta_previous h c (h-2) (by omega) (by omega) (by omega)
  have hs : h-2-1=h-3 := by omega
  rw [hs] at he
  have hm := Nat.mul_le_mul_right (ordinaryBeta c (h-3)) (show c+h≤2*c by omega)
  exact he.trans hm

theorem ordinaryValue_top_linear_step (h c b x : ℕ) (r u : ℕ → ℕ)
    (hh : 3≤h) (hn : ordinaryNonfreeSize h r u+2≤c) :
    ordinaryValue h c b r u x-ordinaryValue h c b (Function.update r (h-1) (r (h-1)+1)) u x=1 := by
  have hm : h-1∈Finset.Icc 2 (h-1) := by simp; omega
  have he := series_coefficient_step_product _ _ _ (ordinarySeries (denseSet (b-1) x)) h (h-1+1)
    (by omega) (ordinary_sparse_linear_step h c (h-1) r u hm hn)
  change ordinaryValue h c b r u x-ordinaryValue h c b (Function.update r (h-1) (r (h-1)+1)) u x=_ at he
  have hz : h-(h-1+1)=0 := by omega
  simpa [hz,PowerSeries.coeff_zero_eq_constantCoeff] using he

end SumsetRanges
