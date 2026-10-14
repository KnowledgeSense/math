import MainTheorems.EulerianPencil.NegativeFactors

namespace ResearchMain.EulerianPencil

open Polynomial

theorem NegativeFactor.one_add_X {q : ℝ[X]} {d : ℕ} (h : NegativeFactor q d)
    (hn : q.eval (-1) ≠ 0) : NegativeFactor ((1 + X) * q) (d + 1) := by
  have hl : (1 + X : ℝ[X]).Monic := by
    simpa only [add_comm, map_one] using (monic_X_add_C (1 : ℝ))
  have hd := one_add_X_distinct_iff.mpr ⟨⟨h.splits, h.separable⟩, hn⟩
  refine ⟨hl.mul h.monic, ?_, hd.1, hd.2, ?_⟩
  · rw [natDegree_mul hl.ne_zero h.monic.ne_zero, h.degree]
    have he : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa only [add_comm, map_one] using (natDegree_X_add_C (1 : ℝ))
    rw [he]
    omega
  · intro x hx
    simp only [eval_mul, eval_add, eval_one, eval_X] at hx
    rcases mul_eq_zero.mp hx with hx | hx
    · linarith
    · exact h.negative x hx

theorem odd_lower_endpoint (m : ℕ) : ∃ q : ℝ[X],
    eulerianPencil (2 * m + 3) (-(2 * m + 3 : ℝ) * (2 * m + 2)) = (X - 1) ^ 2 * q ∧
      NegativeFactor q (2 * m) := by
  have h := oddH_interlacingPair m
  obtain ⟨q, he, hq, _⟩ := h.exceptional_factor (fun _ => oddH_roots_lt_neg_two m)
    (by norm_num : (-2 : ℝ) ≤ 2) (h.root_at_boundary
      (fun r hr => (oddH_roots_lt_neg_two m hr).trans (by norm_num)))
  refine ⟨q, ?_, ?_⟩
  · rw [odd_eulerianPencil]
    simpa only [oddH_natDegree, oddH_ratio_at_two, neg_mul,
      reciprocalQuadratic_endpoint_pos, map_one] using he
  · simpa only [oddH_natDegree] using hq

theorem even_lower_endpoint (m : ℕ) : ∃ q : ℝ[X],
    eulerianPencil (2 * m + 4) (-(2 * m + 4 : ℝ) * (2 * m + 3)) = (X - 1) ^ 2 * q ∧
      NegativeFactor q (2 * m + 1) := by
  have h := evenH_interlacingPair m
  obtain ⟨q, he, hq, hn⟩ := h.exceptional_factor (fun _ => evenH_roots_lt_neg_two m)
    (by norm_num : (-2 : ℝ) ≤ 2) (h.root_at_boundary
      (fun r hr => (evenH_roots_lt_neg_two m hr).trans (by norm_num)))
  refine ⟨(1 + X) * q, ?_, ?_⟩
  · rw [even_eulerianPencil]
    have he' : quadraticLift (m + 1)
        (evenH (m + 1) + C (-(2 * m + 4 : ℝ) * (2 * m + 3)) * evenH m) = (X - 1) ^ 2 * q := by
      simpa only [evenH_natDegree, evenH_ratio_at_two, neg_mul,
        reciprocalQuadratic_endpoint_pos, map_one] using he
    rw [he']
    ring
  · simpa only [evenH_natDegree] using hq.one_add_X hn

theorem odd_upper_endpoint (m : ℕ) : ∃ q : ℝ[X],
    eulerianPencil (2 * m + 3) (-eulerRatio (m + 1)) = (X + 1) ^ 2 * q ∧
      NegativeFactor q (2 * m) ∧ q.eval (-1) ≠ 0 := by
  have h := oddH_interlacingPair m
  obtain ⟨q, he, hq, hn⟩ := h.exceptional_factor (fun _ => oddH_roots_lt_neg_two m)
    (le_refl (-2)) (h.root_at_boundary (fun _ => oddH_roots_lt_neg_two m))
  refine ⟨q, ?_, ?_, hn⟩
  · rw [odd_eulerianPencil]
    simpa only [oddH_natDegree, ← eulerRatio_succ, reciprocalQuadratic_endpoint_neg] using he
  · simpa only [oddH_natDegree] using hq

theorem even_upper_endpoint (m : ℕ) : ∃ q : ℝ[X],
    eulerianPencil (2 * m + 4) (-eulerRatio (m + 2)) = (X + 1) ^ 3 * q ∧
      NegativeFactor q (2 * m) ∧ q.eval (-1) ≠ 0 := by
  have h := evenH_interlacingPair m
  obtain ⟨q, he, hq, hn⟩ := h.exceptional_factor (fun _ => evenH_roots_lt_neg_two m)
    (le_refl (-2)) (h.root_at_boundary (fun _ => evenH_roots_lt_neg_two m))
  refine ⟨q, ?_, ?_, hn⟩
  · rw [even_eulerianPencil]
    have he' : quadraticLift (m + 1)
        (evenH (m + 1) + C (-eulerRatio (m + 2)) * evenH m) = (X + 1) ^ 2 * q := by
      simpa only [evenH_natDegree, evenH_ratio_at_neg_two,
        show m + 2 = (m + 1) + 1 by omega, ← eulerRatio_succ,
        reciprocalQuadratic_endpoint_neg] using he
    rw [he']
    ring
  · simpa only [evenH_natDegree] using hq

theorem lower_endpoint_factorization {n : ℕ} (hn : 3 ≤ n) : ∃ q : ℝ[X],
    eulerianPencil n (-(n : ℝ) * (n - 1 : ℝ)) = (X - 1) ^ 2 * q ∧
      NegativeFactor q (n - 3) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    obtain ⟨q, hq, hd⟩ := even_lower_endpoint m
    refine ⟨q, ?_, ?_⟩
    · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        show 2 * (m : ℝ) + 4 - 1 = 2 * m + 3 by ring] using hq
    · convert hd using 1; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    obtain ⟨q, hq, hd⟩ := odd_lower_endpoint m
    refine ⟨q, ?_, ?_⟩
    · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        show 2 * (m : ℝ) + 3 - 1 = 2 * m + 2 by ring] using hq
    · convert hd using 1; omega

theorem lower_endpoint_multiplicity {n : ℕ} (hn : 3 ≤ n) :
    (eulerianPencil n (-(n : ℝ) * (n - 1 : ℝ))).rootMultiplicity 1 = 2 := by
  obtain ⟨q, he, hq⟩ := lower_endpoint_factorization hn
  have hq1 : q.eval 1 ≠ 0 := fun he => by have h := hq.negative 1 he; linarith
  rw [he, mul_comm, show (1 : ℝ[X]) = C (1 : ℝ) by simp,
    rootMultiplicity_mul_X_sub_C_pow hq.monic.ne_zero, rootMultiplicity_eq_zero hq1]

theorem upper_endpoint_factorization {n : ℕ} (hn : 3 ≤ n) : ∃ q : ℝ[X],
    eulerianPencil n (-eulerRatio (n / 2)) = (X + 1) ^ (3 - n % 2) * q ∧
      NegativeFactor q (n - (4 - n % 2)) ∧ q.eval (-1) ≠ 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    have hd : (2 * m + 4) / 2 = m + 2 := by omega
    have hm : (2 * m + 4) % 2 = 0 := by omega
    rw [hd, hm]
    simpa only [Nat.sub_zero, show 2 * m + 4 - 4 = 2 * m by omega] using even_upper_endpoint m
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    have hd : (2 * m + 3) / 2 = m + 1 := by omega
    have hm : (2 * m + 3) % 2 = 1 := by omega
    rw [hd, hm]
    have hdeg : 2 * m + 3 - (4 - 1) = 2 * m := by omega
    simpa only [show 3 - 1 = 2 by decide, hdeg] using odd_upper_endpoint m

theorem upper_endpoint_multiplicity {n : ℕ} (hn : 3 ≤ n) :
    (eulerianPencil n (-eulerRatio (n / 2))).rootMultiplicity (-1) = 3 - n % 2 := by
  obtain ⟨q, he, hq, hnq⟩ := upper_endpoint_factorization hn
  rw [he, mul_comm, show (X + 1 : ℝ[X]) = X - C (-1 : ℝ) by simp,
    rootMultiplicity_mul_X_sub_C_pow hq.monic.ne_zero, rootMultiplicity_eq_zero hnq]
  omega

end ResearchMain.EulerianPencil
