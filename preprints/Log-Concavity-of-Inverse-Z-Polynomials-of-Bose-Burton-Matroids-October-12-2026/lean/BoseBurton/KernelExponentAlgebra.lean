import BoseBurton.ScalarDefinitions

noncomputable section
namespace BoseBurton

theorem choose_pair_square (h : ℕ) : h.choose 2+(h+1).choose 2=h*h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have h1 : (h+1).choose 2=h+h.choose 2 := by rw [Nat.choose_succ_succ]; simp
    have h2 : (h+1+1).choose 2=(h+1)+(h+1).choose 2 := by rw [Nat.choose_succ_succ]; simp
    rw [h1] at ih
    rw [h2,h1]
    nlinarith

theorem twice_choose_two (h : ℕ) (hh : 1≤h) : h.choose 2+h.choose 2=h*(h-1) := by
  have h := choose_pair_square h
  rw [Nat.choose_succ_succ] at h
  simp only [Nat.choose_one_right] at h
  nlinarith [Nat.sub_add_cancel hh]

theorem signed_square (h : ℕ) : (-1:ℝ)^h*(-1)^h=1 := by
  rw [← mul_pow]
  norm_num

theorem signed_adjacent (h : ℕ) (hh : 1≤h) : (-1:ℝ)^h*(-1)^(h-1)= -1 := by
  have he : h=(h-1)+1 := by omega
  conv_lhs => lhs; rw [he,pow_succ]
  nlinarith [signed_square (h-1)]

end BoseBurton
