import MainTheorems.Tuza.SparsePacking
import MainTheorems.Tuza.SparseCount

namespace ResearchMain.Tuza

theorem halfUp_balanced (n : ℕ) : n - halfUp n ≤ halfUp n ∧ halfUp n ≤ n - halfUp n + 1 := by
  unfold halfUp
  omega

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem median_sparse_packing (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a) :
    sparsePackingCount (halfUp a) (a - halfUp a) (halfUp b) (b - halfUp b)
      (d.height (halfUp b)) (d.medianDegree ha) ≤ packingNumber d.graph := by
  exact d.sparse_packing_bound hs.le (halfUp_le a) ((d.median_sparse_iff ha).mp hs).le (halfUp_le b)
    (fun i hi => (d.lt_height_iff _ i).mp hi) (fun i hi => d.degree_ge_median ha i hi)

theorem sparse_large_oriented (ha : 0 < a) (hb : 0 < b)
    (hs : d.height (halfUp b) < halfUp a)
    (horder : halfUp a + d.medianDegree ha ≤ halfUp b + d.height (halfUp b))
    (hlarge : 84 * (halfUp a + halfUp b) ≤ 3 * ((halfUp a) ^ 2 + (halfUp b) ^ 2)) :
    Inequality d.graph := by
  have hc := d.median_sparse_cover ha hs
  have hp := d.median_sparse_packing ha hs
  have h := sparse_count_large (halfUp a) (a - halfUp a) (halfUp b) (b - halfUp b)
    (d.height (halfUp b)) (d.medianDegree ha) (halfUp_pos ha) (halfUp_pos hb)
    (halfUp_balanced a).1 (halfUp_balanced a).2
    (halfUp_balanced b).1 (halfUp_balanced b).2 hs horder hlarge
  exact hc.trans (h.trans (Nat.mul_le_mul_left 2 hp))

theorem sparse_large_inequality (ha : 0 < a) (hb : 0 < b)
    (hs : d.height (halfUp b) < halfUp a)
    (hlarge : 84 * (halfUp a + halfUp b) ≤ 3 * ((halfUp a) ^ 2 + (halfUp b) ^ 2)) :
    Inequality d.graph := by
  by_cases ho : halfUp a + d.medianDegree ha ≤ halfUp b + d.height (halfUp b)
  · exact d.sparse_large_oriented ha hb hs ho hlarge
  · have hts : d.transpose.height (halfUp a) < halfUp b := by
      rw [d.transpose_median_height ha]
      exact (d.median_sparse_iff ha).mp hs
    have hto : halfUp b + d.transpose.medianDegree hb ≤ halfUp a + d.transpose.height (halfUp a) := by
      rw [d.transpose_medianDegree hb, d.transpose_median_height ha]
      omega
    have htl : 84 * (halfUp b + halfUp a) ≤ 3 * ((halfUp b) ^ 2 + (halfUp a) ^ 2) := by
      simpa only [Nat.add_comm] using hlarge
    exact (inequality_iso d.transposeIso).mp (d.transpose.sparse_large_oriented hb ha hts hto htl)

theorem sparse_unbounded_reduction (ha : 0 < a) (hb : 0 < b)
    (hs : d.height (halfUp b) < halfUp a) (hsize : 111 ≤ a + b) : Inequality d.graph := by
  apply d.sparse_large_inequality ha hb hs
  have hsizes : 56 ≤ halfUp a + halfUp b := by unfold halfUp; omega
  nlinarith [sq_nonneg ((halfUp a : ℤ) - halfUp b)]

end FerrersProfile

end ResearchMain.Tuza
