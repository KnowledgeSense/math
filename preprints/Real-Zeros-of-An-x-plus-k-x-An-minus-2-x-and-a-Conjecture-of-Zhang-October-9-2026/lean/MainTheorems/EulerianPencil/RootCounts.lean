import MainTheorems.EulerianPencil.Regions

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def nonrealRootCount (f : ℝ[X]) : ℕ :=
  ((complexify f).roots.filter (fun z => z.im ≠ 0)).card

noncomputable def positiveRootCount (f : ℝ[X]) : ℕ := (f.roots.filter (fun x => 0 < x)).card

noncomputable def negativeRootCount (f : ℝ[X]) : ℕ := (f.roots.filter (fun x => x < 0)).card

theorem nonrealRootCount_mul {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    nonrealRootCount (f * g) = nonrealRootCount f + nonrealRootCount g := by
  simp only [nonrealRootCount, complexify, Polynomial.map_mul]
  rw [roots_mul (mul_ne_zero (map_ne_zero hf) (map_ne_zero hg)), Multiset.filter_add,
    Multiset.card_add]

theorem positiveRootCount_mul {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    positiveRootCount (f * g) = positiveRootCount f + positiveRootCount g := by
  simp only [positiveRootCount]
  rw [roots_mul (mul_ne_zero hf hg), Multiset.filter_add, Multiset.card_add]

theorem negativeRootCount_mul {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    negativeRootCount (f * g) = negativeRootCount f + negativeRootCount g := by
  simp only [negativeRootCount]
  rw [roots_mul (mul_ne_zero hf hg), Multiset.filter_add, Multiset.card_add]

theorem NegativeFactor.nonreal_count {q : ℝ[X]} {d : ℕ} (h : NegativeFactor q d) :
    nonrealRootCount q = 0 := by
  unfold nonrealRootCount
  rw [Multiset.filter_eq_nil.mpr, Multiset.card_zero]
  intro z hz
  exact not_not.mpr ((splits_iff_complex_roots_real h.monic.ne_zero).mp h.splits z
    ((mem_roots (complexify_ne_zero h.monic.ne_zero)).mp hz))

theorem NegativeFactor.positive_count {q : ℝ[X]} {d : ℕ} (h : NegativeFactor q d) :
    positiveRootCount q = 0 := by
  unfold positiveRootCount
  rw [Multiset.filter_eq_nil.mpr, Multiset.card_zero]
  intro x hx
  exact not_lt_of_ge (h.negative x ((mem_roots h.monic.ne_zero).mp hx)).le

theorem NegativeFactor.negative_count {q : ℝ[X]} {d : ℕ} (h : NegativeFactor q d) :
    negativeRootCount q = d := by
  unfold negativeRootCount
  rw [Multiset.filter_eq_self.mpr (fun x hx => h.negative x ((mem_roots h.monic.ne_zero).mp hx)),
    ← h.splits.natDegree_eq_card_roots, h.degree]

theorem reciprocalQuadratic_no_real_root {r : ℝ} (hlo : -2 < r) (hhi : r < 2) (x : ℝ) :
    (reciprocalQuadratic r).eval x ≠ 0 := by
  rw [reciprocalQuadratic_eval]
  intro he
  have hp : 0 < 4 - r ^ 2 := by nlinarith
  nlinarith [sq_nonneg (2 * x - r)]

theorem reciprocalQuadratic_nonreal_roots {r : ℝ} (hlo : -2 < r) (hhi : r < 2)
    {z : ℂ} (hz : (complexify (reciprocalQuadratic r)).eval z = 0) : z.im ≠ 0 := by
  intro he
  have hzre : z = (z.re : ℂ) := by apply Complex.ext <;> simp [he]
  rw [hzre] at hz
  have hreal : (reciprocalQuadratic r).eval z.re = 0 := by
    have hre := congrArg Complex.re hz
    simpa [complexify, reciprocalQuadratic, reciprocalQuadratic_eval, pow_two, Complex.mul_re] using hre
  exact reciprocalQuadratic_no_real_root hlo hhi z.re hreal

theorem reciprocalQuadratic_nonreal_count {r : ℝ} (hlo : -2 < r) (hhi : r < 2) :
    nonrealRootCount (reciprocalQuadratic r) = 2 := by
  unfold nonrealRootCount
  rw [Multiset.filter_eq_self.mpr (fun z hz => reciprocalQuadratic_nonreal_roots hlo hhi
    ((mem_roots (complexify_ne_zero (reciprocalQuadratic_monic r).ne_zero)).mp hz)),
    ← (IsAlgClosed.splits (complexify (reciprocalQuadratic r))).natDegree_eq_card_roots]
  simp only [complexify, natDegree_map_eq_of_injective Complex.ofRealHom.injective,
    reciprocalQuadratic_natDegree]

theorem reciprocalQuadratic_negative_count_middle {r : ℝ} (hlo : -2 < r) (hhi : r < 2) :
    negativeRootCount (reciprocalQuadratic r) = 0 := by
  have he : (reciprocalQuadratic r).roots = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro x hx
    exact reciprocalQuadratic_no_real_root hlo hhi x
      ((mem_roots (reciprocalQuadratic_monic r).ne_zero).mp hx)
  simp [negativeRootCount, he]

theorem reciprocalQuadratic_positive_count {r : ℝ} (hr : 2 < r) :
    positiveRootCount (reciprocalQuadratic r) = 2 := by
  unfold positiveRootCount
  rw [Multiset.filter_eq_self.mpr (fun x hx => reciprocalQuadratic_root_positive hr
    ((mem_roots (reciprocalQuadratic_monic r).ne_zero).mp hx)),
    ← ((reciprocalQuadratic_splits_iff r).mpr (Or.inr hr.le)).natDegree_eq_card_roots,
    reciprocalQuadratic_natDegree]

theorem reciprocalQuadratic_negative_count_lower {r : ℝ} (hr : 2 < r) :
    negativeRootCount (reciprocalQuadratic r) = 0 := by
  unfold negativeRootCount
  rw [Multiset.filter_eq_nil.mpr, Multiset.card_zero]
  intro x hx
  exact not_lt_of_ge (reciprocalQuadratic_root_positive hr
    ((mem_roots (reciprocalQuadratic_monic r).ne_zero).mp hx)).le

theorem middle_region_root_counts {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hlo : -(n : ℝ) * (n - 1 : ℝ) < k) (hhi : k < -eulerRatio (n / 2)) :
    nonrealRootCount (eulerianPencil n k) = 2 ∧ negativeRootCount (eulerianPencil n k) = n - 3 := by
  obtain ⟨t, q, htlo, hthi, he, hq⟩ := middle_region hn hlo hhi
  rw [he, nonrealRootCount_mul (reciprocalQuadratic_monic t).ne_zero hq.monic.ne_zero,
    negativeRootCount_mul (reciprocalQuadratic_monic t).ne_zero hq.monic.ne_zero,
    reciprocalQuadratic_nonreal_count htlo hthi, hq.nonreal_count,
    reciprocalQuadratic_negative_count_middle htlo hthi, hq.negative_count]
  simp

theorem lower_region_root_counts {n : ℕ} (hn : 3 ≤ n) {k : ℝ}
    (hk : k < -(n : ℝ) * (n - 1 : ℝ)) :
    positiveRootCount (eulerianPencil n k) = 2 ∧ negativeRootCount (eulerianPencil n k) = n - 3 := by
  obtain ⟨t, q, ht, he, hq⟩ := lower_region hn hk
  rw [he, positiveRootCount_mul (reciprocalQuadratic_monic t).ne_zero hq.monic.ne_zero,
    negativeRootCount_mul (reciprocalQuadratic_monic t).ne_zero hq.monic.ne_zero,
    reciprocalQuadratic_positive_count ht, hq.positive_count,
    reciprocalQuadratic_negative_count_lower ht, hq.negative_count]
  simp

end ResearchMain.EulerianPencil
