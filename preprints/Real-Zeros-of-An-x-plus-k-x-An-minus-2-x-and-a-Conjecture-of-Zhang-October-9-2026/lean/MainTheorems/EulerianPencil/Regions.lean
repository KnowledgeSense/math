import MainTheorems.EulerianPencil.EndpointRoots

namespace ResearchMain.EulerianPencil

open Polynomial

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem upper_negative_factor (hb : ∀ r : ℝ, g.eval r = 0 → r < -2)
    {k : ℝ} (hk : -(f.eval (-2) / g.eval (-2)) < k) :
    NegativeFactor (quadraticLift (g.natDegree + 1) (f + C k * g))
      (2 * (g.natDegree + 1)) := by
  have hs := h.splits k
  have hm := h.monic k
  have hr := separable_of_simpleRoots hs hm.ne_zero (h.simpleRoots k)
  have hbq := (h.strict_root_bound_iff hb k).mpr (by linarith)
  simpa only [h.degree k] using negative_quadraticLift hs hm hr hbq

theorem lower_factorization (hb : ∀ r : ℝ, g.eval r = 0 → r < -2)
    {k : ℝ} (hk : k < -(f.eval 2 / g.eval 2)) :
    ∃ t : ℝ, ∃ q : ℝ[X], 2 < t ∧
      quadraticLift (g.natDegree + 1) (f + C k * g) = reciprocalQuadratic t * q ∧
      NegativeFactor q (2 * g.natDegree) ∧ q.eval (-1) ≠ 0 := by
  obtain ⟨t, ht, hr⟩ := h.exists_root_above (b := 2)
    (fun r hr => (hb r hr).trans (by norm_num)) k (by linarith)
  obtain ⟨q, he, hq, hn⟩ := h.exceptional_factor hb (by linarith : -2 ≤ t) hr
  exact ⟨t, q, ht, he, hq, hn⟩

theorem middle_factorization (hb : ∀ r : ℝ, g.eval r = 0 → r < -2)
    {k : ℝ} (hlo : -(f.eval 2 / g.eval 2) < k)
    (hhi : k < -(f.eval (-2) / g.eval (-2))) :
    ∃ t : ℝ, ∃ q : ℝ[X], -2 < t ∧ t < 2 ∧
      quadraticLift (g.natDegree + 1) (f + C k * g) = reciprocalQuadratic t * q ∧
      NegativeFactor q (2 * g.natDegree) ∧ q.eval (-1) ≠ 0 := by
  obtain ⟨t, htlo, hthi, hr⟩ := h.middle_root (c := 2) hb (by norm_num) k (by linarith) (by linarith)
  obtain ⟨q, he, hq, hn⟩ := h.exceptional_factor hb htlo.le hr
  exact ⟨t, q, htlo, hthi, he, hq, hn⟩

end InterlacingPair

theorem even_negative_lift (m : ℕ) {k : ℝ} (h : NegativeFactor
    (quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m)) (2 * (m + 1))) :
    NegativeFactor (eulerianPencil (2 * m + 4) k) (2 * m + 3) := by
  have hi := evenH_interlacingPair m
  have hd : (evenH (m + 1) + C k * evenH m).natDegree = m + 1 := by
    simpa only [evenH_natDegree] using hi.degree k
  have he : (quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m)).eval (-1) ≠ 0 := by
    rw [quadraticLift_eval_neg_one hd.le]
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    intro hr
    have ht := (quadraticLift_distinct_iff (hi.splits k) (hi.monic k)
      (separable_of_simpleRoots (hi.splits k) (hi.monic k).ne_zero (hi.simpleRoots k)))
    rw [hd] at ht
    rcases ht.mp ⟨h.splits, h.separable⟩ (-2) hr with hbad | hbad <;> linarith
  rw [even_eulerianPencil]
  simpa only [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] using h.one_add_X he

theorem upper_region {n : ℕ} (hn : 3 ≤ n) {k : ℝ} (hk : -eulerRatio (n / 2) < k) :
    NegativeFactor (eulerianPencil n k) (n - 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    have h := (evenH_interlacingPair m).upper_negative_factor
      (fun _ => evenH_roots_lt_neg_two m)
      (k := k) (by
        simpa only [show (2 * m + 4) / 2 = m + 2 by omega, evenH_ratio_at_neg_two,
          show m + 2 = (m + 1) + 1 by omega, ← eulerRatio_succ] using hk)
    have hh : NegativeFactor (quadraticLift (m + 1)
        (evenH (m + 1) + C k * evenH m)) (2 * (m + 1)) := by
      simpa only [evenH_natDegree] using h
    convert even_negative_lift m hh using 1; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    have h := (oddH_interlacingPair m).upper_negative_factor
      (fun _ => oddH_roots_lt_neg_two m)
      (k := k) (by
        simpa only [show (2 * m + 3) / 2 = m + 1 by omega, ← eulerRatio_succ] using hk)
    rw [odd_eulerianPencil]
    have hh : NegativeFactor (quadraticLift (m + 1)
        (oddH (m + 1) + C k * oddH m)) (2 * (m + 1)) := by
      simpa only [oddH_natDegree] using h
    simpa only [show 2 * m + 3 - 1 = 2 * (m + 1) by omega] using hh

theorem lower_region {n : ℕ} (hn : 3 ≤ n) {k : ℝ} (hk : k < -(n : ℝ) * (n - 1 : ℝ)) :
    ∃ t : ℝ, ∃ q : ℝ[X], 2 < t ∧ eulerianPencil n k = reciprocalQuadratic t * q ∧
      NegativeFactor q (n - 3) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    have h := evenH_interlacingPair m
    have hk' : k < -((evenH (m + 1)).eval 2 / (evenH m).eval 2) := by
      rw [evenH_ratio_at_two, ← neg_mul]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        show 2 * (m : ℝ) + 4 - 1 = 2 * m + 3 by ring] using hk
    obtain ⟨t, q, ht, hq, hd, hq1⟩ := h.lower_factorization (fun _ => evenH_roots_lt_neg_two m) hk'
    refine ⟨t, (1 + X) * q, ht, ?_, ?_⟩
    · rw [even_eulerianPencil]
      have hq' : quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m) =
          reciprocalQuadratic t * q := by simpa only [evenH_natDegree] using hq
      rw [hq']; ring
    · convert hd.one_add_X hq1 using 1; simp only [evenH_natDegree]; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    have h := oddH_interlacingPair m
    have hk' : k < -((oddH (m + 1)).eval 2 / (oddH m).eval 2) := by
      rw [oddH_ratio_at_two, ← neg_mul]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        show 2 * (m : ℝ) + 3 - 1 = 2 * m + 2 by ring] using hk
    obtain ⟨t, q, ht, hq, hd, _⟩ := h.lower_factorization (fun _ => oddH_roots_lt_neg_two m) hk'
    refine ⟨t, q, ht, ?_, ?_⟩
    · rw [odd_eulerianPencil]
      simpa only [oddH_natDegree] using hq
    · convert hd using 1; simp only [oddH_natDegree]; omega

theorem middle_region {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hlo : -(n : ℝ) * (n - 1 : ℝ) < k) (hhi : k < -eulerRatio (n / 2)) :
    ∃ t : ℝ, ∃ q : ℝ[X], -2 < t ∧ t < 2 ∧ eulerianPencil n k = reciprocalQuadratic t * q ∧
      NegativeFactor q (n - 3) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    have h := evenH_interlacingPair m
    have hlo' : -((evenH (m + 1)).eval 2 / (evenH m).eval 2) < k := by
      rw [evenH_ratio_at_two, ← neg_mul]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        show 2 * (m : ℝ) + 4 - 1 = 2 * m + 3 by ring] using hlo
    have hhi' : k < -((evenH (m + 1)).eval (-2) / (evenH m).eval (-2)) := by
      simpa only [show (2 * m + 4) / 2 = m + 2 by omega, evenH_ratio_at_neg_two,
        show m + 2 = (m + 1) + 1 by omega, ← eulerRatio_succ] using hhi
    obtain ⟨t, q, htlo, hthi, hq, hd, hq1⟩ := h.middle_factorization
      (fun _ => evenH_roots_lt_neg_two m) hlo' hhi'
    refine ⟨t, (1 + X) * q, htlo, hthi, ?_, ?_⟩
    · rw [even_eulerianPencil]
      have hq' : quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m) =
          reciprocalQuadratic t * q := by simpa only [evenH_natDegree] using hq
      rw [hq']; ring
    · convert hd.one_add_X hq1 using 1; simp only [evenH_natDegree]; omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    have h := oddH_interlacingPair m
    have hlo' : -((oddH (m + 1)).eval 2 / (oddH m).eval 2) < k := by
      rw [oddH_ratio_at_two, ← neg_mul]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        show 2 * (m : ℝ) + 3 - 1 = 2 * m + 2 by ring] using hlo
    have hhi' : k < -((oddH (m + 1)).eval (-2) / (oddH m).eval (-2)) := by
      simpa only [show (2 * m + 3) / 2 = m + 1 by omega, ← eulerRatio_succ] using hhi
    obtain ⟨t, q, htlo, hthi, hq, hd, _⟩ := h.middle_factorization
      (fun _ => oddH_roots_lt_neg_two m) hlo' hhi'
    refine ⟨t, q, htlo, hthi, ?_, ?_⟩
    · rw [odd_eulerianPencil]
      simpa only [oddH_natDegree] using hq
    · convert hd using 1; simp only [oddH_natDegree]; omega

end ResearchMain.EulerianPencil
