import MainTheorems.Tuza.DenseFanPacking
import MainTheorems.Tuza.DenseNearPacking
import MainTheorems.Tuza.DenseCount
import MainTheorems.Tuza.SparseReduction

namespace ResearchMain.Tuza.FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem median_dense_degree (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    halfUp b ≤ d.medianDegree ha := by
  have h := d.median_sparse_iff ha
  omega

theorem median_dense_fan (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    denseFanCount (halfUp a) (a - halfUp a) (halfUp b) (b - halfUp b)
      (d.height (halfUp b) - halfUp a) (d.medianDegree ha - halfUp b) ≤ packingNumber d.graph := by
  have hp := d.dense_fan_bound hd (d.height_le _) (d.median_dense_degree ha hd) (d.medianDegree_le ha)
    (fun i hi => (d.lt_height_iff _ i).mp hi) (fun i hi => d.degree_ge_median ha i hi)
  simpa only [denseFanCount, Nat.add_sub_of_le hd] using hp

theorem median_dense_complete (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    denseCompleteCount (halfUp a) (a - halfUp a) (halfUp b) (b - halfUp b)
      (d.height (halfUp b) - halfUp a) (d.medianDegree ha - halfUp b)
      (d.lowerCrossCount (halfUp a) (halfUp b)) ≤ (packingNumber d.graph : ℝ) := by
  have hy := d.median_dense_degree ha hd
  have hx := d.height_le (halfUp b)
  have hyb := d.medianDegree_le ha
  have hp := d.dense_near_bound (halfUp a) (halfUp b) (d.height (halfUp b)) (d.medianDegree ha)
    hd hx hy hyb
    (fun i hi => (d.lt_height_iff _ i).mp hi)
    (fun i hi => d.degree_ge_median ha i hi)
    (fun i hi => d.degree_le_median ha i hi)
    (fun i hi => (d.lt_height_iff _ i).mpr hi)
  have hax : a - d.height (halfUp b) ≤ d.height (halfUp b) := by
    have := (halfUp_balanced a).1
    omega
  have hby : b - d.medianDegree ha ≤ d.medianDegree ha := by
    have := (halfUp_balanced b).1
    omega
  rw [fanCount_saturated hax, fanCount_saturated hby] at hp
  have hsum : halfUp a + halfUp b + (d.height (halfUp b) - halfUp a) +
      (d.medianDegree ha - halfUp b) = d.height (halfUp b) + d.medianDegree ha := by omega
  have hs : a - halfUp a - (d.height (halfUp b) - halfUp a) = a - d.height (halfUp b) := by omega
  have hu : b - halfUp b - (d.medianDegree ha - halfUp b) = b - d.medianDegree ha := by omega
  simpa only [denseCompleteCount, hsum, hs, hu] using hp

theorem dense_large_oriented (ha : 0 < a) (hb : 0 < b)
    (hd : halfUp a ≤ d.height (halfUp b)) (hrt : halfUp a ≤ halfUp b)
    (hsize : 88 ≤ halfUp a + halfUp b) : Inequality d.graph := by
  have hc := d.median_dense_cover hd
  have hf := d.median_dense_fan ha hd
  have hp := d.median_dense_complete ha hd
  have hl := d.complete_bound
  have hy := d.median_dense_degree ha hd
  have hx := d.height_le (halfUp b)
  have hyb := d.medianDegree_le ha
  have hclique : completeCount (halfUp a + (a - halfUp a)) +
      completeCount (halfUp b + (b - halfUp b)) ≤ packingNumber d.graph := by
    simpa only [halfUp_add] using hl
  have h := dense_count_large (halfUp a) (a - halfUp a) (halfUp b) (b - halfUp b)
    (d.height (halfUp b) - halfUp a) (d.medianDegree ha - halfUp b)
    (d.lowerCrossCount (halfUp a) (halfUp b)) (packingNumber d.graph)
    (halfUp_pos ha) (halfUp_pos hb) hrt
    (halfUp_balanced a).1 (halfUp_balanced a).2
    (halfUp_balanced b).1 (halfUp_balanced b).2
    (by omega) (by omega) hsize hf hp hclique
  exact hc.trans h

theorem dense_large_inequality (ha : 0 < a) (hb : 0 < b)
    (hd : halfUp a ≤ d.height (halfUp b)) (hsize : 88 ≤ halfUp a + halfUp b) :
    Inequality d.graph := by
  by_cases hrt : halfUp a ≤ halfUp b
  · exact d.dense_large_oriented ha hb hd hrt hsize
  · have htd : halfUp b ≤ d.transpose.height (halfUp a) := by
      rw [d.transpose_median_height ha]
      exact d.median_dense_degree ha hd
    exact (inequality_iso d.transposeIso).mp
      (d.transpose.dense_large_oriented hb ha htd (le_of_not_ge hrt) (by omega))

theorem dense_unbounded_reduction (ha : 0 < a) (hb : 0 < b)
    (hd : halfUp a ≤ d.height (halfUp b)) (hsize : 175 ≤ a + b) : Inequality d.graph := by
  apply d.dense_large_inequality ha hb hd
  unfold halfUp
  omega

end ResearchMain.Tuza.FerrersProfile
