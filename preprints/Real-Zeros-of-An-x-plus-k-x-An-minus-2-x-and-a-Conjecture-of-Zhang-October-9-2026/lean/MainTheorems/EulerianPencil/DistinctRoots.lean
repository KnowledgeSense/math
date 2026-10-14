import MainTheorems.EulerianPencil.EulerNumbers

namespace ResearchMain.EulerianPencil

open Polynomial

def DistinctRealRoots (f : ℝ[X]) : Prop := f.Splits ∧ f.Separable

theorem reciprocalQuadratics_coprime {r s : ℝ} (hrs : r ≠ s) :
    IsCoprime (reciprocalQuadratic r) (reciprocalQuadratic s) := by
  have hn : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have he : C ((s - r)⁻¹) * C (s - r) = (1 : ℝ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hn, map_one]
  refine ⟨C ((s - r)⁻¹) * (C s - X), 1 - C ((s - r)⁻¹) * (C s - X), ?_⟩
  unfold reciprocalQuadratic
  rw [map_sub] at he
  linear_combination (X * (C s - X)) * he

theorem quadraticLift_factor_dvd {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic)
    {r : ℝ} (hr : f.eval r = 0) : reciprocalQuadratic r ∣ quadraticLift f.natDegree f := by
  rw [quadraticLift_eq_quadratic_product hs hm]
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨r, (mem_roots hm.ne_zero).mpr hr, rfl⟩)

theorem quadraticLift_distinct_iff {f : ℝ[X]} (hs : f.Splits) (hm : f.Monic)
    (hr : f.Separable) :
    DistinctRealRoots (quadraticLift f.natDegree f) ↔
      ∀ r : ℝ, f.eval r = 0 → r < -2 ∨ 2 < r := by
  classical
  constructor
  · intro h r hroot
    have hc := (quadraticLift_splits_iff hs hm).mp h.1 r hroot
    have hsep := h.2.of_dvd (quadraticLift_factor_dvd hs hm hroot)
    have he := (reciprocalQuadratic_simpleRoots_iff r).mp (simpleRoots_of_separable hsep)
    rcases hc with hc | hc
    · exact Or.inl (hc.lt_of_ne he.1)
    · exact Or.inr (hc.lt_of_ne he.2.symm)
  · intro h
    have hsplit : (quadraticLift f.natDegree f).Splits :=
      (quadraticLift_splits_iff hs hm).mpr (fun r hr => (h r hr).imp le_of_lt le_of_lt)
    refine ⟨hsplit, ?_⟩
    rw [quadraticLift_eq_quadratic_product hs hm]
    have hn : f.roots.toFinset.val = f.roots := by
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hr)]
    have hp : (f.roots.map reciprocalQuadratic).prod =
        ∏ r ∈ f.roots.toFinset, reciprocalQuadratic r := by
      change _ = (f.roots.toFinset.val.map reciprocalQuadratic).prod
      rw [hn]
    rw [hp]
    apply separable_prod'
    · intro r _ s _ hrs
      exact reciprocalQuadratics_coprime hrs
    · intro r hr
      have hroot : f.eval r = 0 := (mem_roots hm.ne_zero).mp (Multiset.mem_toFinset.mp hr)
      have he := h r hroot
      apply separable_of_simpleRoots
        ((reciprocalQuadratic_splits_iff r).mpr (he.imp le_of_lt le_of_lt))
        (reciprocalQuadratic_monic r).ne_zero
      apply (reciprocalQuadratic_simpleRoots_iff r).mpr
      rcases he with he | he <;> constructor <;> linarith

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem lifted_distinct_iff (hb : ∀ r : ℝ, g.eval r = 0 → r < -2) (k : ℝ) :
    DistinctRealRoots (quadraticLift (g.natDegree + 1) (f + C k * g)) ↔
      k < -(f.eval 2 / g.eval 2) ∨ -(f.eval (-2) / g.eval (-2)) < k := by
  have hs := h.splits k
  have hm := h.monic k
  have hr := separable_of_simpleRoots hs hm.ne_zero (h.simpleRoots k)
  have he := quadraticLift_distinct_iff hs hm hr
  rw [h.degree k] at he
  rw [he]
  exact h.strict_two_ray_root_classification hb (by norm_num) k

end InterlacingPair

theorem quadraticLift_eval_neg_one {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    (quadraticLift m f).eval (-1) = (-1 : ℝ) ^ m * f.eval (-2) := by
  apply Polynomial.induction_with_natDegree_le
    (fun f => (quadraticLift m f).eval (-1) = (-1 : ℝ) ^ m * f.eval (-2)) m
  · simp
  · intro j a _ hj
    rw [quadraticLift_C_mul, quadraticLift_X_pow hj]
    simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
    norm_num
    have he : (-1 : ℝ) ^ m = (-1) ^ (m - j) * (-1) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    have hc : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by
      rw [← mul_pow]
      norm_num
    rw [he, show (-2 : ℝ) ^ j = (-1) ^ j * 2 ^ j by rw [neg_pow]]
    linear_combination -(a * (-1) ^ (m - j) * (2 : ℝ) ^ j) * hc
  · intro f g _ _ ihf ihg
    simp only [quadraticLift_add, eval_add, ihf, ihg, mul_add]
  · exact hf

theorem one_add_X_distinct_iff {f : ℝ[X]} :
    DistinctRealRoots ((1 + X) * f) ↔ DistinctRealRoots f ∧ f.eval (-1) ≠ 0 := by
  have hl : (1 + X : ℝ[X]).Monic := by
    simpa only [add_comm, map_one] using (monic_X_add_C (1 : ℝ))
  have hs : (1 + X : ℝ[X]).Separable := by
    simpa only [add_comm, map_one] using (separable_X_add_C (1 : ℝ))
  have hp : (1 + X : ℝ[X]).Splits := by
    simpa only [add_comm, map_one] using (Splits.X_add_C (1 : ℝ))
  constructor
  · intro h
    refine ⟨⟨(splits_mul_iff_right hl.ne_zero hp).mp h.1, h.2.of_mul_right⟩, ?_⟩
    intro he
    apply simpleRoots_of_separable h.2 (-1) (by simp)
    simp [derivative_mul, he]
  · rintro ⟨h, he⟩
    refine ⟨hp.mul h.1, hs.mul h.2 ?_⟩
    have hc : IsCoprime (X - C (-1 : ℝ)) f :=
      (EuclideanDomain.dvd_or_coprime _ _
        (irreducible_of_degree_eq_one (degree_X_sub_C (-1 : ℝ)))).resolve_left
        (fun hd => he (dvd_iff_isRoot.mp hd))
    simpa only [map_neg, map_one, sub_neg_eq_add, add_comm] using hc

theorem odd_eulerianPencil_distinct (m : ℕ) (k : ℝ) :
    DistinctRealRoots (eulerianPencil (2 * m + 3) k) ↔
      k < -(2 * m + 3 : ℝ) * (2 * m + 2) ∨ -eulerRatio (m + 1) < k := by
  rw [odd_eulerianPencil]
  have he := (oddH_interlacingPair m).lifted_distinct_iff (fun _ => oddH_roots_lt_neg_two m) k
  simp only [oddH_natDegree] at he
  rw [he, oddH_ratio_at_two, ← eulerRatio_succ, neg_mul]

theorem even_eulerianPencil_distinct (m : ℕ) (k : ℝ) :
    DistinctRealRoots (eulerianPencil (2 * m + 4) k) ↔
      k < -(2 * m + 4 : ℝ) * (2 * m + 3) ∨ -eulerRatio (m + 2) < k := by
  rw [even_eulerianPencil, one_add_X_distinct_iff]
  have h := evenH_interlacingPair m
  have he := h.lifted_distinct_iff (fun _ => evenH_roots_lt_neg_two m) k
  have hn : (evenH (m + 1) + C k * evenH m).natDegree = m + 1 := by
    simpa only [evenH_natDegree] using h.degree k
  have hne : DistinctRealRoots (quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m)) →
      (quadraticLift (m + 1) (evenH (m + 1) + C k * evenH m)).eval (-1) ≠ 0 := by
    intro hh
    have hc := (quadraticLift_distinct_iff (h.splits k) (h.monic k)
      (separable_of_simpleRoots (h.splits k) (h.monic k).ne_zero (h.simpleRoots k)))
    rw [hn] at hc
    have hr := hc.mp hh
    rw [quadraticLift_eval_neg_one hn.le]
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    intro hroot
    have hbad := hr (-2) hroot
    rcases hbad with hbad | hbad <;> linarith
  rw [and_iff_left_of_imp hne]
  simpa only [evenH_natDegree, evenH_ratio_at_two, evenH_ratio_at_neg_two,
    show m + 2 = (m + 1) + 1 by omega, ← eulerRatio_succ, neg_mul] using he

theorem distinctRealRoots_classification {n : ℕ} (hn : 3 ≤ n) (k : ℝ) :
    DistinctRealRoots (eulerianPencil n k) ↔
      k < -(n : ℝ) * (n - 1 : ℝ) ∨ -eulerRatio (n / 2) < k := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 4 := ⟨n / 2 - 2, by omega⟩
    rw [show (2 * m + 4) / 2 = m + 2 by omega, even_eulerianPencil_distinct]
    push_cast
    ring_nf
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 3 := ⟨n / 2 - 1, by omega⟩
    rw [show (2 * m + 3) / 2 = m + 1 by omega, odd_eulerianPencil_distinct]
    push_cast
    ring_nf

end ResearchMain.EulerianPencil
