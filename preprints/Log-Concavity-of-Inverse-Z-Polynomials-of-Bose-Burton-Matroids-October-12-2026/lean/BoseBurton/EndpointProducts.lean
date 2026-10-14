import BoseBurton.PositiveWeights

noncomputable section
namespace BoseBurton
open Finset

theorem prod_range_shift_cleared (f : ℕ→ℝ) (n : ℕ) :
    (∏ i∈range n,f i)*f n=f 0*(∏ i∈range n,f (i+1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [prod_range_succ,prod_range_succ,← mul_assoc,ih]

theorem endpointFactor_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s : ℕ) (hsr : s<r) :
    endpointFactor z r s/positiveWeight z r s 0=
      ∏ i∈range s,(1-z^(r-s+1+i)) := by
  rw [positiveWeight_zero z hz0 hz1 r s (by omega)]
  have hc := (one_sub_pow_pos z hz0 hz1 (r-s) (by omega)).ne'
  have hr := (one_sub_pow_pos z hz0 hz1 r (by omega)).ne'
  have h := prod_range_shift_cleared (fun i=>1-z^(r-s+i)) s
  rw [show r-s+s=r by omega] at h
  simp only [Nat.add_zero] at h
  have he : (∏ i∈range s,(1-z^(r-s+(i+1))))=
      ∏ i∈range s,(1-z^(r-s+1+i)) := by
    apply prod_congr rfl
    intro i _
    congr 2
    omega
  rw [he] at h
  unfold endpointFactor
  field_simp
  exact h

theorem endpointFactor_reserve (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s : ℕ) (hsr : s<r) (hs : 1≤s) :
    z^(r-s+1)≤1-endpointFactor z r s/positiveWeight z r s 0 := by
  rw [endpointFactor_ratio z hz0.le hz1 r s hsr]
  have hprod : (∏ i∈range s,(1-z^(r-s+1+i)))≤1-z^(r-s+1) := by
    have h0 : 0∈range s := by simp; omega
    rw [← prod_erase_mul _ _ h0]
    have hle : (∏ i∈(range s).erase 0,(1-z^(r-s+1+i)))≤1 := by
      calc
        _ ≤ ∏ _i∈(range s).erase 0,(1:ℝ) := by
          apply prod_le_prod₀
          · intro i _
            have := pow_le_one₀ hz0.le hz1.le (n:=r-s+1+i)
            linarith
          · intro i _
            have := pow_nonneg hz0.le (r-s+1+i)
            linarith
        _ = 1 := by simp
    simpa only [Nat.add_zero,one_mul] using mul_le_mul_of_nonneg_right hle
      (one_sub_pow_pos z hz0.le hz1 (r-s+1) (by omega)).le
  linarith

end BoseBurton
