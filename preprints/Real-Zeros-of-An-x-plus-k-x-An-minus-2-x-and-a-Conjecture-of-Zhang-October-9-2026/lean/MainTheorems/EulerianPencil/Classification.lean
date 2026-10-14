import MainTheorems.EulerianPencil.ComplexPairs

namespace ResearchMain.EulerianPencil

open Polynomial

theorem coprime_of_no_real_roots {f g : ℝ[X]} (hf : ∀ x : ℝ, f.eval x ≠ 0)
    (hs : g.Splits) (hg : g ≠ 0) : IsCoprime f g := by
  rw [← gcd_isUnit_iff, isUnit_iff_degree_eq_zero]
  by_contra he
  obtain ⟨x, hx⟩ := (hs.of_dvd hg (gcd_dvd_right f g)).exists_eval_eq_zero he
  obtain ⟨q, hq⟩ := gcd_dvd_left f g
  exact hf x (by rw [hq, eval_mul, hx, zero_mul])

theorem middle_region_separable {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hlo : -(n : ℝ) * (n - 1 : ℝ) < k) (hhi : k < -eulerRatio (n / 2)) :
    (eulerianPencil n k).Separable := by
  obtain ⟨t, q, htlo, hthi, he, hq⟩ := middle_region hn hlo hhi
  have hf := reciprocalQuadratic_no_real_root htlo hthi
  have hd : (derivative (reciprocalQuadratic t)).Splits :=
    Splits.of_natDegree_le_one (by
      have h := natDegree_derivative_le (reciprocalQuadratic t)
      rw [reciprocalQuadratic_natDegree] at h
      exact h)
  have hdn : derivative (reciprocalQuadratic t) ≠ 0 := by
    intro he
    have hd := congrArg (fun f : ℝ[X] => f.eval 1) he
    rw [reciprocalQuadratic_derivative_eval, eval_zero] at hd
    linarith
  have hs : (reciprocalQuadratic t).Separable := coprime_of_no_real_roots hf hd hdn
  rw [he]
  exact hs.mul hq.separable (coprime_of_no_real_roots hf hq.splits hq.monic.ne_zero)

theorem eulerianPencil_monic_degree {n : ℕ} (hn : 3 ≤ n) (k : ℝ) :
    (eulerianPencil n k).Monic ∧ (eulerianPencil n k).natDegree = n - 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    have h := evenH_interlacingPair m
    have hs := h.splits k
    have hm := h.monic k
    have hd : (evenH (m + 1) + C k * evenH m).natDegree = m + 1 := by
      simpa only [evenH_natDegree] using h.degree k
    have hl : (1 + X : ℝ[X]).Monic := by
      simpa only [add_comm, map_one] using monic_X_add_C (1 : ℝ)
    have hqm : (quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m)).Monic := by
      simpa only [hd] using quadraticLift_monic hs hm
    have hqd : (quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m)).natDegree =
        2 * (m + 1) := by simpa only [hd] using quadraticLift_natDegree hs hm
    rw [even_eulerianPencil]
    refine ⟨hl.mul hqm, ?_⟩
    rw [natDegree_mul hl.ne_zero hqm.ne_zero, hqd]
    have hld : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa only [add_comm, map_one] using natDegree_X_add_C (1 : ℝ)
    rw [hld]
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    have h := oddH_interlacingPair m
    have hs := h.splits k
    have hm := h.monic k
    have hd : (oddH (m + 1) + C k * oddH m).natDegree = m + 1 := by
      simpa only [oddH_natDegree] using h.degree k
    have hqm : (quadraticLift (m + 1) (oddH (m + 1) + C k * oddH m)).Monic := by
      simpa only [hd] using quadraticLift_monic hs hm
    have hqd : (quadraticLift (m + 1) (oddH (m + 1) + C k * oddH m)).natDegree =
        2 * (m + 1) := by simpa only [hd] using quadraticLift_natDegree hs hm
    rw [odd_eulerianPencil]
    refine ⟨hqm, ?_⟩
    rw [hqd]
    omega

theorem classification {n : ℕ} (hn : 3 ≤ n) (k : ℝ) :
    ((eulerianPencil n k).roots.card = n - 1 ∧ (eulerianPencil n k).roots.Nodup) ↔
      k < -(n : ℝ) * (n - 1 : ℝ) ∨ -eulerRatio (n / 2) < k := by
  have hm := (eulerianPencil_monic_degree hn k).1
  have hd := (eulerianPencil_monic_degree hn k).2
  rw [← distinctRealRoots_classification hn]
  constructor
  · rintro ⟨hc, hn⟩
    have hs : (eulerianPencil n k).Splits := splits_iff_card_roots.mpr (by rw [hd]; exact hc)
    exact ⟨hs, (nodup_roots_iff_of_splits hm.ne_zero hs).mp hn⟩
  · intro h
    exact ⟨h.1.natDegree_eq_card_roots.symm.trans hd, nodup_roots h.2⟩

theorem endpoint_other_roots {f q : ℝ[X]} {d e : ℕ} {a x : ℝ}
    (he : f = (X - C a) ^ e * q) (hq : NegativeFactor q d)
    (hx : f.eval x = 0) (hxa : x ≠ a) : x < 0 ∧ (derivative f).eval x ≠ 0 := by
  have hpow : (x - a) ^ e ≠ 0 := pow_ne_zero e (sub_ne_zero.mpr hxa)
  have hqx : q.eval x = 0 := by
    rw [he, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hx
    exact (mul_eq_zero.mp hx).resolve_left hpow
  refine ⟨hq.negative x hqx, ?_⟩
  rw [he, derivative_mul, eval_add, eval_mul, eval_mul, hqx, mul_zero, zero_add,
    eval_pow, eval_sub, eval_X, eval_C]
  exact mul_ne_zero hpow (simpleRoots_of_separable hq.separable x hqx)

theorem lower_endpoint_other_roots {n : ℕ} (hn : 3 ≤ n) {x : ℝ}
    (hx : (eulerianPencil n (-(n : ℝ) * (n - 1 : ℝ))).eval x = 0) (hxa : x ≠ 1) :
    x < 0 ∧ (derivative (eulerianPencil n (-(n : ℝ) * (n - 1 : ℝ)))).eval x ≠ 0 := by
  obtain ⟨q, he, hq⟩ := lower_endpoint_factorization hn
  apply endpoint_other_roots (q := q) (a := 1) (e := 2) (d := n - 3) _ hq hx hxa
  simpa only [map_one] using he

theorem upper_endpoint_other_roots {n : ℕ} (hn : 3 ≤ n) {x : ℝ}
    (hx : (eulerianPencil n (-eulerRatio (n / 2))).eval x = 0) (hxa : x ≠ -1) :
    x < 0 ∧ (derivative (eulerianPencil n (-eulerRatio (n / 2)))).eval x ≠ 0 := by
  obtain ⟨q, he, hq, _⟩ := upper_endpoint_factorization hn
  apply endpoint_other_roots (q := q) (a := -1) (e := 3 - n % 2) (d := n - (4 - n % 2))
    _ hq hx hxa
  simpa only [map_neg, map_one, sub_neg_eq_add] using he

end ResearchMain.EulerianPencil
