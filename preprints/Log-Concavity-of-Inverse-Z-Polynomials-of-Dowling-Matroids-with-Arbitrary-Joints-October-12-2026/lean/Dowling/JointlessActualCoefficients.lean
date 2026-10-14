import Dowling.JointlessActualCoefficientsUnraised

noncomputable section
namespace Dowling
open PowerSeries Finset

theorem jointlessRaisedWeight_eq_raising (a : ℝ) (n : ℕ) :
    jointlessRaisedWeight a n=(fun j => a*(jointlessUnraisedWeight a n j/(n+a-2*j)-
      if j=0 then 0 else jointlessUnraisedWeight a n (j-1)/(n+a-2*(j-1)))) := by
  funext j
  cases j with
  | zero =>
    simp only [jointlessRaisedWeight,Nat.cast_zero,mul_zero,sub_zero,ite_true]
    rw [div_div_eq_mul_div]
    ring
  | succ j =>
    simp only [jointlessRaisedWeight,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel_right,
      Nat.cast_add,Nat.cast_one]
    rw [show ((n : ℝ)+a)/2-(j+1)+1=((n : ℝ)+a-2*j)/2 by ring,
      show ((n : ℝ)+a)/2-(j+1)=((n : ℝ)+a-2*(j+1))/2 by ring,
      div_div_eq_mul_div,div_div_eq_mul_div]
    have he : (n : ℝ)+a-2*((j+1)-1)=(n : ℝ)+a-2*j := by ring
    rw [he]
    ring

theorem jointlessSeries_raised_coeff (m : ℝ) (hm : 0<m) (n k : ℕ)
    (hn : (n : ℝ)+m⁻¹-1≠0) :
    (coeff n (jointlessSeries m)).coeff k=m^n*
      quadraticWeightedRow (jointlessRaisedWeight m⁻¹ n) (m⁻¹+1) n k := by
  rw [jointlessSeries_unraised_coeff m (ne_of_gt hm) n k hn,
    quadraticWeightedRow_raise (inv_pos.mpr hm),jointlessRaisedWeight_eq_raising]

variable (G : Type*) [Group G] [Fintype G] [Nontrivial G]

/-- The actual jointless inverse-Z coefficients equal the source raised-weight
row. All residue, tau, factorial and fixed-total raising identities are proved. -/
theorem jointless_actual_coeff (n k : ℕ) (hn : 2≤n) :
    ((configurationY (G := G) (∅ : Set (Fin n))).coeff k : ℝ)=
      (n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
        quadraticWeightedRow (jointlessRaisedWeight (Fintype.card G : ℝ)⁻¹ n)
          ((Fintype.card G : ℝ)⁻¹+1) n k := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff k) (jointlessSeries_actual G n hn)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map] at h
  have hm : (0 : ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hd : (n : ℝ)+(Fintype.card G : ℝ)⁻¹-1≠0 := by
    have hnr : (2 : ℝ)≤n := by exact_mod_cast hn
    have hi := inv_pos.mpr hm
    linarith
  rw [jointlessSeries_raised_coeff _ hm n k hd] at h
  simpa only [mul_assoc,Int.coe_castRingHom] using h.symm

/-- The literal supported finite sum, in the original source's index convention. -/
theorem jointless_actual_coeff_sum (n k : ℕ) (hn : 2≤n) (hk : k≤n) :
    ((configurationY (G := G) (∅ : Set (Fin n))).coeff k : ℝ)=
      (n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
        ∑ j∈range (min k (n-k)+1),jointlessRaisedWeight (Fintype.card G : ℝ)⁻¹ n j*
          dowlingBinomialWeight ((Fintype.card G : ℝ)⁻¹+1) (k-j)*
          dowlingBinomialWeight ((Fintype.card G : ℝ)⁻¹+1) (n-k-j) := by
  rw [jointless_actual_coeff G n k hn,quadraticWeightedRow,ite_eq_left hk]

end Dowling
