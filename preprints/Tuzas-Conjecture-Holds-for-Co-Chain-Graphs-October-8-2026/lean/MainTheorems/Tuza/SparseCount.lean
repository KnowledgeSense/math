import MainTheorems.Tuza.CountBounds
import MainTheorems.Tuza.SparseQuadratic

namespace ResearchMain.Tuza

def sparsePackingCount (r s t u x y : ℕ) : ℕ :=
  completeCount (x + t) + fanCount (x + y) (r - x) + fanCount r s + fanCount t u

def sparseCoverCount (r s t u x y : ℕ) : ℕ :=
  r.choose 2 + s.choose 2 + t.choose 2 + u.choose 2 + x * t + (r - x) * y

theorem sparse_count_margin (r s t u x y : ℕ) (hr : 0 < r) (ht : 0 < t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1) (hxr : x < r) :
    sparseMargin r t x y ≤
      6 * (sparsePackingCount r s t u x y : ℝ) - 3 * (sparseCoverCount r s t u x y : ℝ) := by
  have hC := complete_count_real_bound (x + t)
  have hJ := fan_count_real_lower (x + y) (r - x) (by omega)
  have hB := balanced_fan_difference r s t u hr ht hsr hrs hut htu
  simp only [Nat.cast_add, Nat.cast_sub hxr.le] at hC hJ
  simp only [sparseMargin, sparsePackingCount, sparseCoverCount, Nat.cast_add,
    Nat.cast_mul, Nat.cast_sub hxr.le]
  nlinarith

theorem sparse_count_large (r s t u x y : ℕ) (hr : 0 < r) (ht : 0 < t)
    (hsr : s ≤ r) (hrs : r ≤ s + 1) (hut : u ≤ t) (htu : t ≤ u + 1)
    (hxr : x < r) (horder : r + y ≤ t + x)
    (hlarge : 84 * (r + t) ≤ 3 * (r ^ 2 + t ^ 2)) :
    sparseCoverCount r s t u x y ≤ 2 * sparsePackingCount r s t u x y := by
  have hm := sparse_count_margin r s t u x y hr ht hsr hrs hut htu hxr
  have ho : (r : ℝ) + y ≤ (t : ℝ) + x := by exact_mod_cast horder
  have hl : 84 * ((r : ℝ) + t) ≤ 3 * ((r : ℝ) ^ 2 + (t : ℝ) ^ 2) := by exact_mod_cast hlarge
  have hp := sparse_margin_positive r t x y (by positivity) (by positivity)
    (by positivity) (by positivity) (by exact_mod_cast hxr.le) ho hl
  have h : (sparseCoverCount r s t u x y : ℝ) ≤ 2 * (sparsePackingCount r s t u x y : ℝ) := by
    linarith
  exact_mod_cast h

end ResearchMain.Tuza
