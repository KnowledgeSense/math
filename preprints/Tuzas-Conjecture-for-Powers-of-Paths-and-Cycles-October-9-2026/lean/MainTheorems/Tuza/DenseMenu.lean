import MainTheorems.Tuza.DenseShape
import MainTheorems.Tuza.SparsePivots

namespace ResearchMain.Tuza

def denseCoverBase (a b : ℕ) : ℕ :=
  let r := halfUp a
  let t := halfUp b
  pairCount r + pairCount (a - r) + pairCount t + pairCount (b - t) + r * t

def densePackingValue (a b x y : ℕ) : ℕ :=
  let r := halfUp a
  let t := halfUp b
  fastFanCount x t + fastFanCount (y - t) r + fastFanCount r (a - r) + fastFanCount t (b - t)

def denseBasicPackingValue (a b x y : ℕ) : ℕ :=
  max (fastCompleteCount a + fastCompleteCount b)
    (max (max (densePackingValue a b x y) (densePackingValue b a y x))
      (max (pivotValue a b x (halfUp b)) (pivotValue b a y (halfUp a))))

def denseFullPackingValue (a b x y : ℕ) : ℕ :=
  max (denseBasicPackingValue a b x y)
    (max ((Finset.range (b + 1)).sup (fun k => pivotValue a b (denseHeight a b x y k) k))
      ((Finset.range (a + 1)).sup (fun k => pivotValue b a (denseTransposeHeight a b x y k) k)))

def denseNearBase (a b x y : ℕ) : ℤ :=
  (fastCompleteCount (x + y) : ℤ) - (x - halfUp a : ℕ) * (y - halfUp b : ℕ) +
    fastFanCount x (a - x) + fastFanCount y (b - y)

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem pivotValue_le (k : ℕ) (hk : k ≤ b) :
    pivotValue a b (d.height k) k ≤ packingNumber d.graph := by
  simpa only [pivotValue, fastCompleteCount_eq, fastFanCount_eq, pivotBound, rowHeight, height]
    using d.pivotBound_le k hk

theorem dense_cover_base_bound (hd : halfUp a ≤ d.height (halfUp b)) :
    coverNumber d.graph ≤ denseCoverBase a b + d.lowerCrossCount (halfUp a) (halfUp b) := by
  simpa only [denseCoverBase, pairCount_eq, Nat.add_assoc] using d.median_dense_cover hd

theorem dense_packing_value_bound (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    densePackingValue a b (d.height (halfUp b)) (d.medianDegree ha) ≤ packingNumber d.graph := by
  simpa only [densePackingValue, fastFanCount_eq, denseFanCount, Nat.add_sub_of_le hd,
    Nat.add_assoc] using d.median_dense_fan ha hd

theorem dense_transpose_value_bound (ha : 0 < a) (hb : 0 < b)
    (hd : halfUp a ≤ d.height (halfUp b)) :
    densePackingValue b a (d.medianDegree ha) (d.height (halfUp b)) ≤ packingNumber d.graph := by
  have htd : halfUp b ≤ d.transpose.height (halfUp a) := by
    rw [d.transpose_median_height ha]
    exact d.median_dense_degree ha hd
  have h := d.transpose.dense_packing_value_bound hb htd
  rw [d.transpose_medianDegree hb, d.transpose_median_height ha, packingNumber_iso d.transposeIso] at h
  exact h

theorem dense_basic_packing_value_bound (ha : 0 < a) (hb : 0 < b)
    (hd : halfUp a ≤ d.height (halfUp b)) :
    denseBasicPackingValue a b (d.height (halfUp b)) (d.medianDegree ha) ≤ packingNumber d.graph := by
  refine max_le ?_ (max_le (max_le (d.dense_packing_value_bound ha hd)
    (d.dense_transpose_value_bound ha hb hd)) (max_le ?_ ?_))
  · simpa only [fastCompleteCount_eq] using d.complete_bound
  · exact d.pivotValue_le _ (halfUp_le b)
  · have h := d.transpose.pivotValue_le (halfUp a) (halfUp_le a)
    rw [d.transpose_median_height ha, packingNumber_iso d.transposeIso] at h
    exact h

theorem dense_full_packing_value_bound (ha : 0 < a) (hb : 0 < b)
    (hd : halfUp a ≤ d.height (halfUp b)) :
    denseFullPackingValue a b (d.height (halfUp b)) (d.medianDegree ha) ≤ packingNumber d.graph := by
  let c := denseProfile a b (d.height (halfUp b)) (d.medianDegree ha)
    (d.median_dense_degree ha hd) (d.medianDegree_le ha)
  have hm : packingNumber c.graph ≤ packingNumber d.graph := packingNumber_mono (d.denseProfile_le ha hd)
  refine max_le (d.dense_basic_packing_value_bound ha hb hd) (max_le ?_ ?_)
  · apply Finset.sup_le
    intro k hk
    have hk' : k ≤ b := by have := Finset.mem_range.mp hk; omega
    have hh := denseHeight_eq a b (d.height (halfUp b)) (d.medianDegree ha) k hd
      (d.height_le _) (d.median_dense_degree ha hd)
    have hp := c.pivotValue_le k hk'
    change rowHeight c.degree k = _ at hh
    change pivotValue a b (rowHeight c.degree k) k ≤ _ at hp
    rw [hh] at hp
    exact hp.trans hm
  · apply Finset.sup_le
    intro k hk
    have hk' : k ≤ a := by have := Finset.mem_range.mp hk; omega
    have hh := denseTransposeHeight_eq a b (d.height (halfUp b)) (d.medianDegree ha) k
      (d.median_dense_degree ha hd) (d.medianDegree_le ha) hk'
    have hp := c.transpose.pivotValue_le k hk'
    rw [hh, packingNumber_iso c.transposeIso] at hp
    exact hp.trans hm

theorem dense_near_base_bound (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b)) :
    denseNearBase a b (d.height (halfUp b)) (d.medianDegree ha) +
      d.lowerCrossCount (halfUp a) (halfUp b) ≤ (packingNumber d.graph : ℤ) := by
  have hp := d.dense_near_bound (halfUp a) (halfUp b) (d.height (halfUp b)) (d.medianDegree ha)
    hd (d.height_le _) (d.median_dense_degree ha hd) (d.medianDegree_le ha)
    (fun i hi => (d.lt_height_iff _ i).mp hi) (fun i hi => d.degree_ge_median ha i hi)
    (fun i hi => d.degree_le_median ha i hi) (fun i hi => (d.lt_height_iff _ i).mpr hi)
  have hi : (completeCount (d.height (halfUp b) + d.medianDegree ha) : ℤ) -
      (d.height (halfUp b) - halfUp a : ℕ) * (d.medianDegree ha - halfUp b : ℕ) +
      d.lowerCrossCount (halfUp a) (halfUp b) + fanCount (d.height (halfUp b)) (a - d.height (halfUp b)) +
      fanCount (d.medianDegree ha) (b - d.medianDegree ha) ≤ (packingNumber d.graph : ℤ) := by
    exact_mod_cast hp
  simp only [denseNearBase, fastCompleteCount_eq, fastFanCount_eq]
  linarith

end FerrersProfile

end ResearchMain.Tuza
