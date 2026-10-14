import BoseBurton.GaussianIdentities

noncomputable section
namespace BoseBurton
open Finset

theorem gaussian_partial_alternating (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (n b : ℕ) (hb : b≤n) :
    (∑ i∈range (b+1),(-1:ℝ)^i*z^(i.choose 2)*gaussian z (n+1) i)=
      (-1:ℝ)^b*z^((b+1).choose 2)*gaussian z n b := by
  induction b with
  | zero => simp [gaussian_zero_right z hz0 hz1]
  | succ b ih =>
    rw [sum_range_succ,ih (by omega),gaussian_pascal_succ z hz0 hz1 n b]
    have he : (b+1+1).choose 2=(b+1).choose 2+(b+1) := by
      rw [Nat.choose_succ_succ]; simp; omega
    simp only [he,pow_add,pow_one]
    ring

theorem gaussian_full_alternating (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n : ℕ) :
    (∑ i∈range (n+2),(-1:ℝ)^i*z^(i.choose 2)*gaussian z (n+1) i)=0 := by
  rw [show n+2=(n+1)+1 by omega,sum_range_succ,
    gaussian_partial_alternating z hz0 hz1 n n le_rfl,
    gaussian_self z hz0 hz1 n,gaussian_self z hz0 hz1 (n+1),pow_succ (-1:ℝ) n]
  ring

end BoseBurton
