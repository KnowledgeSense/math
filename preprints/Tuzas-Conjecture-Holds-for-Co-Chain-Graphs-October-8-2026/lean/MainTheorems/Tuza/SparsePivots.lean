import MainTheorems.Tuza.SparseMenu

namespace ResearchMain.Tuza

def sparseHeight (a b x y k : ℕ) : ℕ :=
  if k = 0 then a else if k ≤ y then halfUp a else if k ≤ halfUp b then x else 0

def sparseTransposeHeight (a b x y k : ℕ) : ℕ :=
  if k = 0 then b else if k ≤ x then halfUp b else if k ≤ halfUp a then y else 0

def pivotValue (a b p k : ℕ) : ℕ :=
  max (fastCompleteCount a + fastFanCount p k + fastFanCount k (b - k))
    (fastCompleteCount (p + k) + fastFanCount p (a - p) + fastFanCount k (b - k))

theorem sparseHeight_eq (a b x y k : ℕ) (hx : x ≤ halfUp a) (hy : y ≤ halfUp b) :
    rowHeight (sparseRows a b x y) k = sparseHeight a b x y k := by
  by_cases hk : k = 0
  · subst k
    simp [rowHeight, sparseHeight]
  · by_cases hky : k ≤ y
    · have he : Finset.univ.filter (fun i : Fin a => k ≤ sparseRows a b x y i) =
          Finset.univ.filter (fun i : Fin a => i.val < halfUp a) := by
        ext i
        rw [Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        dsimp only [sparseRows]
        split_ifs <;> omega
      simp only [rowHeight, he, sparseHeight, ite_eq_right hk, ite_eq_left hky]
      exact prefix_filter_card a _ (halfUp_le a)
    · by_cases hkt : k ≤ halfUp b
      · have he : Finset.univ.filter (fun i : Fin a => k ≤ sparseRows a b x y i) =
            Finset.univ.filter (fun i : Fin a => i.val < x) := by
          ext i
          rw [Finset.mem_filter, Finset.mem_filter]
          simp only [Finset.mem_univ, true_and]
          dsimp only [sparseRows]
          split_ifs <;> omega
        simp only [rowHeight, he, sparseHeight, ite_eq_right hk, ite_eq_right hky, ite_eq_left hkt]
        exact prefix_filter_card a x (hx.trans (halfUp_le a))
      · have he : Finset.univ.filter (fun i : Fin a => k ≤ sparseRows a b x y i) = ∅ := by
          ext i
          rw [Finset.mem_filter]
          simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          dsimp only [sparseRows]
          split_ifs <;> omega
        simp only [rowHeight, he, sparseHeight, ite_eq_right hk, ite_eq_right hky, ite_eq_right hkt,
          Finset.card_empty]

theorem sparseTransposeHeight_eq (a b x y k : ℕ) (hy : y ≤ halfUp b) (hk : k ≤ a) :
    (sparseProfile a b x y hy).transpose.height k = sparseTransposeHeight a b x y k := by
  by_cases hk0 : k = 0
  · subst k
    simp [FerrersProfile.height, sparseTransposeHeight]
  · rw [(sparseProfile a b x y hy).transpose_height k (by omega) hk]
    change sparseRows a b x y ⟨k - 1, _⟩ = sparseTransposeHeight a b x y k
    simp only [sparseRows, sparseTransposeHeight, ite_eq_right hk0]
    split_ifs <;> omega

def sparsePivotTest (a b x y : ℕ) : Bool :=
  (List.range (b + 1)).any (fun k =>
    decide (sparseCoverValue a b x y ≤ 2 * pivotValue a b (sparseHeight a b x y k) k)) ||
  (List.range (a + 1)).any (fun k =>
    decide (sparseCoverValue a b x y ≤ 2 * pivotValue b a (sparseTransposeHeight a b x y k) k))

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem sparse_pivot_value_bound (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a)
    (k : ℕ) (hk : k ≤ b) :
    pivotValue a b (sparseHeight a b (d.height (halfUp b)) (d.medianDegree ha) k) k ≤
      packingNumber d.graph := by
  let c := sparseProfile a b (d.height (halfUp b)) (d.medianDegree ha)
    ((d.median_sparse_iff ha).mp hs).le
  have hp := c.pivotBound_le k hk
  have hh := sparseHeight_eq a b (d.height (halfUp b)) (d.medianDegree ha) k hs.le
    ((d.median_sparse_iff ha).mp hs).le
  change pivotBound a b (sparseRows a b (d.height (halfUp b)) (d.medianDegree ha)) k ≤ _ at hp
  simp only [pivotBound, hh] at hp
  have hv : pivotValue a b (sparseHeight a b (d.height (halfUp b)) (d.medianDegree ha) k) k ≤
      packingNumber c.graph := by
    simpa only [pivotValue, fastCompleteCount_eq, fastFanCount_eq] using hp
  exact hv.trans (packingNumber_mono (d.sparseProfile_le ha hs))

theorem sparse_transpose_pivot_value_bound (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a)
    (k : ℕ) (hk : k ≤ a) :
    pivotValue b a (sparseTransposeHeight a b (d.height (halfUp b)) (d.medianDegree ha) k) k ≤
      packingNumber d.graph := by
  let c := sparseProfile a b (d.height (halfUp b)) (d.medianDegree ha)
    ((d.median_sparse_iff ha).mp hs).le
  have hp := c.transpose.pivotBound_le k hk
  have hh := sparseTransposeHeight_eq a b (d.height (halfUp b)) (d.medianDegree ha) k
    ((d.median_sparse_iff ha).mp hs).le hk
  change pivotBound b a c.transpose.degree k ≤ _ at hp
  change rowHeight c.transpose.degree k = _ at hh
  simp only [pivotBound, hh] at hp
  have hv : pivotValue b a (sparseTransposeHeight a b (d.height (halfUp b)) (d.medianDegree ha) k) k ≤
      packingNumber c.transpose.graph := by
    simpa only [pivotValue, fastCompleteCount_eq, fastFanCount_eq] using hp
  rw [packingNumber_iso c.transposeIso] at hv
  exact hv.trans (packingNumber_mono (d.sparseProfile_le ha hs))

theorem sparsePivotTest_sound (ha : 0 < a) (hs : d.height (halfUp b) < halfUp a)
    (h : sparsePivotTest a b (d.height (halfUp b)) (d.medianDegree ha) = true) : Inequality d.graph := by
  simp only [sparsePivotTest, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  have hc := d.sparse_cover_value_bound ha hs
  rcases h with ⟨k, hk, hsize⟩ | ⟨k, hk, hsize⟩
  · have hkb : k ≤ b := by have := List.mem_range.mp hk; omega
    exact hc.trans (hsize.trans (Nat.mul_le_mul_left 2 (d.sparse_pivot_value_bound ha hs k hkb)))
  · have hka : k ≤ a := by have := List.mem_range.mp hk; omega
    exact hc.trans (hsize.trans (Nat.mul_le_mul_left 2 (d.sparse_transpose_pivot_value_bound ha hs k hka)))

end FerrersProfile

end ResearchMain.Tuza
