import MainTheorems.Tuza.SparseReduction
import MainTheorems.Tuza.ProfileBounds
import MainTheorems.Tuza.FastCounts

namespace ResearchMain.Tuza

def sparseRows (a b x y : ℕ) : Fin a → ℕ :=
  fun i => if i.val < x then halfUp b else if i.val < halfUp a then y else 0

def sparseProfile (a b x y : ℕ) (hy : y ≤ halfUp b) : FerrersProfile a b where
  degree := sparseRows a b x y
  bound i := by
    have hb := halfUp_le b
    simp only [sparseRows]
    split_ifs <;> omega
  antitone := by
    intro i j hij
    change i.val ≤ j.val at hij
    simp only [sparseRows]
    split_ifs <;> omega

def sparseCoverValue (a b x y : ℕ) : ℕ :=
  let r := halfUp a
  let t := halfUp b
  pairCount r + pairCount (a - r) + pairCount t + pairCount (b - t) + x * t + (r - x) * y

def sparsePackingValue (a b x y : ℕ) : ℕ :=
  let r := halfUp a
  let t := halfUp b
  fastCompleteCount (x + t) + fastFanCount (x + y) (r - x) +
    fastFanCount r (a - r) + fastFanCount t (b - t)

def sparseBaseTest (a b x y : ℕ) : Bool :=
  decide (sparseCoverValue a b x y ≤ 2 * sparsePackingValue a b x y) ||
    decide (sparseCoverValue a b x y ≤ 2 * sparsePackingValue b a y x) ||
    decide (sparseCoverValue a b x y ≤ 2 * (fastCompleteCount a + fastCompleteCount b))

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem sparseRows_le (ha : 0 < a) (i : Fin a) :
    sparseRows a b (d.height (halfUp b)) (d.medianDegree ha) i ≤ d.degree i := by
  simp only [sparseRows]
  split_ifs with hi hir
  · exact (d.lt_height_iff _ i).mp hi
  · exact d.degree_ge_median ha i hir
  · exact Nat.zero_le _

theorem sparseProfile_le (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a) :
    (sparseProfile a b (d.height (halfUp b)) (d.medianDegree ha)
      ((d.median_sparse_iff ha).mp hs).le).graph ≤ d.graph :=
  graph_mono (d.sparseRows_le ha)

theorem sparse_rectangle_bound (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a) :
    rectangleBound a b (sparseRows a b (d.height (halfUp b)) (d.medianDegree ha)) ≤
      packingNumber d.graph := by
  exact (sparseProfile a b _ _ ((d.median_sparse_iff ha).mp hs).le).rectangleBound_le.trans
    (packingNumber_mono (d.sparseProfile_le ha hs))

theorem sparse_cover_value_bound (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a) :
    coverNumber d.graph ≤ sparseCoverValue a b (d.height (halfUp b)) (d.medianDegree ha) := by
  simpa only [sparseCoverValue, pairCount_eq] using d.median_sparse_cover ha hs

theorem sparse_packing_value_bound (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a) :
    sparsePackingValue a b (d.height (halfUp b)) (d.medianDegree ha) ≤ packingNumber d.graph := by
  simpa only [sparsePackingValue, fastCompleteCount_eq, fastFanCount_eq, sparsePackingCount,
    Nat.add_assoc] using d.median_sparse_packing ha hs

theorem sparse_transpose_value_bound (ha : 0 < a) (hb : 0 < b)
    (hs : d.height (halfUp b) < halfUp a) :
    sparsePackingValue b a (d.medianDegree ha) (d.height (halfUp b)) ≤ packingNumber d.graph := by
  have hts : d.transpose.height (halfUp a) < halfUp b := by
    rw [d.transpose_median_height ha]
    exact (d.median_sparse_iff ha).mp hs
  have h := d.transpose.sparse_packing_value_bound hb hts
  rw [d.transpose_medianDegree hb, d.transpose_median_height ha, packingNumber_iso d.transposeIso] at h
  exact h

theorem sparse_base_sound (ha : 0 < a) (hb : 0 < b)
    (hs : d.height (halfUp b) < halfUp a)
    (h : sparseBaseTest a b (d.height (halfUp b)) (d.medianDegree ha) = true) : Inequality d.graph := by
  simp only [sparseBaseTest, Bool.or_eq_true, decide_eq_true_eq] at h
  have hc := d.sparse_cover_value_bound ha hs
  rcases h with (h | h) | h
  · exact hc.trans (h.trans (Nat.mul_le_mul_left 2 (d.sparse_packing_value_bound ha hs)))
  · exact hc.trans (h.trans (Nat.mul_le_mul_left 2 (d.sparse_transpose_value_bound ha hb hs)))
  · simp only [fastCompleteCount_eq] at h
    exact hc.trans (h.trans (Nat.mul_le_mul_left 2 d.complete_bound))

end FerrersProfile

end ResearchMain.Tuza
