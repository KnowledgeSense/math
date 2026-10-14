import Fan.FanCoefficientExtraction

noncomputable section
open scoped BigOperators
namespace Fan
open PowerSeries

theorem geometricSeries_coeff {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    coeff n (geometricSeries c)=c^n := by
  simpa using geometricSeries_pow_coeff c 0 n

theorem fanQBase_coeff {R : Type*} [CommRing R] (n : ℕ) (hn : 0<n) :
    coeff n ((1-X)*geometricSeries (2:R))=2^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [sub_mul,one_mul,map_sub,coeff_succ_X_mul,geometricSeries_coeff,geometricSeries_coeff]
  simp only [Nat.succ_sub_one,pow_succ]
  ring

theorem fanQCandidate_polynomial_sum (N : ℕ) (hN : 0<N) :
    (N : Polynomial ℝ)*coeff N (fanQCandidate Polynomial.X)=
      ∑ r∈Finset.range (N+1),if 2*r<N then
        Polynomial.C ((N.choose r:ℝ)*(N-2*r:ℕ)*2^(N-2*r-1))*Polynomial.X^r else 0 := by
  have h := fanLagrange_coeff_sum (Polynomial.X : Polynomial ℝ)
    ((1-X)*geometricSeries (2 : Polynomial ℝ)) N hN
  rw [← fanQCandidate_eq_subst] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : 2*r<N
  · rw [ite_eq_left hr,ite_eq_left hr,fanQBase_coeff _ (by omega)]
    simp only [map_mul,map_natCast,map_pow,map_ofNat]
    ring
  · rw [ite_eq_right hr,ite_eq_right hr]

theorem fanQCandidate_scaled_coeff (N j : ℕ) (hN : 0<N) :
    (N:ℝ)*(coeff N (fanQCandidate (Polynomial.X : Polynomial ℝ))).coeff j=
      if 2*j<N then (N.choose j:ℝ)*(N-2*j:ℕ)*2^(N-2*j-1) else 0 := by
  have h := congrArg (fun P : Polynomial ℝ => P.coeff j) (fanQCandidate_polynomial_sum N hN)
  rw [show (N : Polynomial ℝ)=Polynomial.C (N:ℝ) by simp,Polynomial.coeff_C_mul] at h
  rw [h,Polynomial.finsetSum_coeff]
  have he (r : ℕ) : (if 2*r<N then
      Polynomial.C ((N.choose r:ℝ)*(N-2*r:ℕ)*2^(N-2*r-1))*Polynomial.X^r else 0).coeff j =
      if r=j then (if 2*j<N then (N.choose j:ℝ)*(N-2*j:ℕ)*2^(N-2*j-1) else 0) else 0 := by
    by_cases hr : r=j
    · subst r
      simp only [ite_true]
      split_ifs
      · rw [Polynomial.coeff_C_mul]
        simp
      · rfl
    · by_cases hh : 2*r<N
      · simp only [ite_eq_left hh,ite_eq_right hr,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow]
        simp [Ne.symm hr]
      · simp only [ite_eq_right hh,ite_eq_right hr,Polynomial.coeff_zero]
  simp only [he]
  by_cases hj : j<N+1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro r _ hr; simp [hr]
    · simp [hj]
  · have hn : ¬2*j<N := by omega
    rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro r hr
    have hne : r≠j := by have := Finset.mem_range.mp hr; omega
    simp [hne]

theorem fanQCandidate_coeff (N j : ℕ) (hN : 0<N) :
    (coeff N (fanQCandidate (Polynomial.X : Polynomial ℝ))).coeff j=
      if 2*j<N then ((N-2*j:ℕ):ℝ)/N*(N.choose j:ℝ)*2^(N-2*j-1) else 0 := by
  have h := fanQCandidate_scaled_coeff N j hN
  have hn : (N:ℝ)≠0 := by positivity
  by_cases hj : 2*j<N
  · rw [ite_eq_left hj] at h ⊢
    apply (mul_left_cancel₀ hn)
    calc
      (N:ℝ)*(coeff N (fanQCandidate (Polynomial.X : Polynomial ℝ))).coeff j = _ := h
      _ = _ := by field_simp
  · rw [ite_eq_right hj] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left hn

/-- The candidate Q coefficient has the original strict half-degree support. -/
theorem fanQCandidate_high_coeff (N j : ℕ) (hN : 0<N) (hj : N ≤ 2*j) :
    (coeff N (fanQCandidate (Polynomial.X : Polynomial ℝ))).coeff j=0 := by
  rw [fanQCandidate_coeff N j hN,ite_eq_right (by omega)]

end Fan
