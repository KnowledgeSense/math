import MainTheorems.EulerianPencil.TangentPolynomials

namespace ResearchMain.EulerianPencil

noncomputable def eulerNumber (n : ℕ) : ℝ :=
  iteratedDeriv n (fun x : ℝ => 1 / Real.cos x + Real.tan x) 0

noncomputable def eulerRatio (m : ℕ) : ℝ := eulerNumber (2 * m + 1) / eulerNumber (2 * m - 1)

theorem odd_secant_derivative_zero (m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun x : ℝ => 1 / Real.cos x) 0 = 0 := by
  have h := iteratedDeriv_comp_neg (2 * m + 1) (fun x : ℝ => 1 / Real.cos x) 0
  have he : (fun x : ℝ => 1 / Real.cos (-x)) = (fun x => 1 / Real.cos x) := by
    funext x
    rw [Real.cos_neg]
  rw [he] at h
  norm_num [pow_add, pow_mul] at h
  simp only [one_div]
  linarith

theorem eulerNumber_odd (m : ℕ) : eulerNumber (2 * m + 1) = (oddH m).eval (-2) := by
  have hs : ContDiffAt ℝ (2 * m + 1) (fun x : ℝ => 1 / Real.cos x) 0 :=
    contDiffAt_const.div Real.contDiff_cos.contDiffAt (by simp)
  have ht : ContDiffAt ℝ (2 * m + 1) Real.tan 0 := Real.contDiffAt_tan.mpr (by simp)
  unfold eulerNumber
  rw [iteratedDeriv_fun_add hs ht, odd_secant_derivative_zero, zero_add,
    ← oddH_eq_tangent_derivative]

theorem eulerNumber_odd_positive (m : ℕ) : 0 < eulerNumber (2 * m + 1) := by
  rw [eulerNumber_odd]
  exact oddH_positive_at_neg_two m

theorem eulerRatio_succ (m : ℕ) :
    eulerRatio (m + 1) = (oddH (m + 1)).eval (-2) / (oddH m).eval (-2) := by
  unfold eulerRatio
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, eulerNumber_odd, eulerNumber_odd]

theorem odd_eulerianPencil_splits (m : ℕ) (k : ℝ) :
    (eulerianPencil (2 * m + 3) k).Splits ↔
      k ≤ -(2 * m + 3 : ℝ) * (2 * m + 2) ∨ -eulerRatio (m + 1) ≤ k := by
  rw [odd_eulerianPencil_splits_iff, oddH_ratio_at_two, ← eulerRatio_succ, neg_mul]

theorem even_eulerianPencil_splits (m : ℕ) (k : ℝ) :
    (eulerianPencil (2 * m + 4) k).Splits ↔
      k ≤ -(2 * m + 4 : ℝ) * (2 * m + 3) ∨ -eulerRatio (m + 2) ≤ k := by
  rw [even_eulerianPencil_splits_iff, evenH_ratio_at_two, evenH_ratio_at_neg_two,
    show m + 2 = (m + 1) + 1 by omega, ← eulerRatio_succ, neg_mul]

theorem realRooted_classification {n : ℕ} (hn : 3 ≤ n) (k : ℝ) :
    (eulerianPencil n k).Splits ↔
      k ≤ -(n : ℝ) * (n - 1 : ℝ) ∨ -eulerRatio (n / 2) ≤ k := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    have hd : (2 * m + 4) / 2 = m + 2 := by omega
    rw [hd, even_eulerianPencil_splits]
    push_cast
    ring_nf
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    have hd : (2 * m + 3) / 2 = m + 1 := by omega
    rw [hd, odd_eulerianPencil_splits]
    push_cast
    ring_nf

theorem endpoint_order {n : ℕ} (hn : 3 ≤ n) :
    eulerRatio (n / 2) < (n : ℝ) * (n - 1 : ℝ) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    rw [show (2 * m + 4) / 2 = m + 2 by omega,
      show m + 2 = (m + 1) + 1 by omega, eulerRatio_succ,
      ← evenH_ratio_at_neg_two]
    convert evenH_boundary_order m using 1; push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    rw [show (2 * m + 3) / 2 = m + 1 by omega, eulerRatio_succ]
    convert oddH_boundary_order m using 1; push_cast; ring

end ResearchMain.EulerianPencil
