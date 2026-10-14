import MainTheorems.EulerianPencil.GeneratingFunction

namespace ResearchMain.EulerianPencil

open Polynomial

theorem reciprocalQuadratic_conjugate_factor {r : ℝ} {z : ℂ}
    (hz : z.im ≠ 0) (he : (complexify (reciprocalQuadratic r)).eval z = 0) :
    complexify (reciprocalQuadratic r) = (X - C z) * (X - C (starRingEnd ℂ z)) := by
  have hn := reciprocalQuadratic_nonreal_norm hz he
  have hi := congrArg Complex.im he
  simp [complexify, reciprocalQuadratic, pow_two, Complex.mul_im] at hi
  have hr : r = 2 * z.re := by
    have hp : z.im * (2 * z.re - r) = 0 := by nlinarith
    have h := (mul_eq_zero.mp hp).resolve_left hz
    linarith
  have hs : z + starRingEnd ℂ z = (r : ℂ) := by rw [Complex.add_conj, hr]
  have hp : z * starRingEnd ℂ z = 1 := by rw [Complex.mul_conj, hn]; rfl
  have hf : (X - C z) * (X - C (starRingEnd ℂ z)) =
      X ^ 2 - C (z + starRingEnd ℂ z) * X + C (z * starRingEnd ℂ z) := by
    rw [map_add, map_mul]; ring
  rw [hf, hs, hp]
  simp [complexify, reciprocalQuadratic]

theorem middle_region_complex_pair {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hlo : -(n : ℝ) * (n - 1 : ℝ) < k) (hhi : k < -eulerRatio (n / 2)) :
    ∃ z : ℂ, z.im ≠ 0 ∧ Complex.normSq z = 1 ∧
      ∀ w : ℂ, ((complexify (eulerianPencil n k)).eval w = 0 ∧ w.im ≠ 0) ↔
        w = z ∨ w = starRingEnd ℂ z := by
  obtain ⟨t, q, htlo, hthi, he, hq⟩ := middle_region hn hlo hhi
  obtain ⟨z, hz⟩ := (IsAlgClosed.splits (complexify (reciprocalQuadratic t))).exists_eval_eq_zero
    (by
      rw [degree_eq_natDegree (complexify_ne_zero (reciprocalQuadratic_monic t).ne_zero)]
      simp only [complexify, natDegree_map_eq_of_injective Complex.ofRealHom.injective,
        reciprocalQuadratic_natDegree]
      norm_num)
  have hzim := reciprocalQuadratic_nonreal_roots htlo hthi hz
  have hnorm := reciprocalQuadratic_nonreal_norm hzim hz
  have hf := reciprocalQuadratic_conjugate_factor hzim hz
  refine ⟨z, hzim, hnorm, ?_⟩
  intro w
  rw [he]
  have hm : complexify (reciprocalQuadratic t * q) =
      complexify (reciprocalQuadratic t) * complexify q := Polynomial.map_mul _
  rw [hm, hf]
  constructor
  · rintro ⟨hroot, hwim⟩
    have hqne := complex_eval_ne_zero hq.splits hq.monic.ne_zero hwim
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hroot
    have hp := (mul_eq_zero.mp hroot).resolve_right hqne
    rcases mul_eq_zero.mp hp with hw | hw
    · exact Or.inl (sub_eq_zero.mp hw)
    · exact Or.inr (sub_eq_zero.mp hw)
  · rintro (rfl | rfl)
    · exact ⟨by simp, hzim⟩
    · exact ⟨by simp, by simpa using hzim⟩

theorem middle_region_unit_circle {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hlo : -(n : ℝ) * (n - 1 : ℝ) < k) (hhi : k < -eulerRatio (n / 2))
    {z : ℂ} (hz : (complexify (eulerianPencil n k)).eval z = 0) (hi : z.im ≠ 0) :
    Complex.normSq z = 1 := by
  obtain ⟨w, _, hw, hp⟩ := middle_region_complex_pair hn hlo hhi
  rcases (hp z).mp ⟨hz, hi⟩ with he | he
  · simpa only [he] using hw
  · simpa only [he, Complex.normSq_conj] using hw

theorem middle_region_real_roots {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hlo : -(n : ℝ) * (n - 1 : ℝ) < k) (hhi : k < -eulerRatio (n / 2))
    {x : ℝ} (hx : (eulerianPencil n k).eval x = 0) :
    x < 0 ∧ (derivative (eulerianPencil n k)).eval x ≠ 0 := by
  obtain ⟨t, q, htlo, hthi, he, hq⟩ := middle_region hn hlo hhi
  have hquad := reciprocalQuadratic_no_real_root htlo hthi x
  have hqx : q.eval x = 0 := by
    rw [he, eval_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left hquad
  refine ⟨hq.negative x hqx, ?_⟩
  rw [he, derivative_mul, eval_add, eval_mul, eval_mul, hqx, mul_zero, zero_add]
  exact mul_ne_zero hquad (simpleRoots_of_separable hq.separable x hqx)

end ResearchMain.EulerianPencil
