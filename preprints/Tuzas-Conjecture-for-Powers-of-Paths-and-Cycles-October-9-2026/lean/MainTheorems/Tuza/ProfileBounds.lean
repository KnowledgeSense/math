import MainTheorems.Tuza.FerrersCuts
import MainTheorems.Tuza.OrderedCuts
import MainTheorems.Tuza.CliquePacking

namespace ResearchMain.Tuza

def rowHeight {a : ℕ} (f : Fin a → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => k ≤ f i)).card

def rowTranspose (a b : ℕ) (f : Fin a → ℕ) : Fin b → ℕ :=
  fun j => rowHeight f (j.val + 1)

def pivotBound (a b : ℕ) (f : Fin a → ℕ) (k : ℕ) : ℕ :=
  max (completeCount a + fanCount (rowHeight f k) k + fanCount k (b - k))
    (completeCount (rowHeight f k + k) + fanCount (rowHeight f k) (a - rowHeight f k) +
      fanCount k (b - k))

def oneSideBound (a b : ℕ) (f : Fin a → ℕ) : ℕ :=
  (Finset.range (b + 1)).sup (pivotBound a b f)

def rectangleBound (a b : ℕ) (f : Fin a → ℕ) : ℕ :=
  max (completeCount a + completeCount b)
    (max (oneSideBound a b f) (oneSideBound b a (rowTranspose a b f)))

def cutCount (a b : ℕ) (f : Fin a → ℕ) (r t : ℕ) (flip : Bool) : ℕ :=
  r.choose 2 + (a - r).choose 2 + t.choose 2 + (b - t).choose 2 +
    ∑ i : Fin a, if (decide (i.val < r)) != flip then min (f i) t else f i - t

def cutTest (a b : ℕ) (f : Fin a → ℕ) : Bool :=
  let L := rectangleBound a b f
  (List.range (a + 1)).any fun r => (List.range (b + 1)).any fun t =>
    [false, true].any fun flip => decide (cutCount a b f r t flip ≤ 2 * L)

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem pivotBound_le (k : ℕ) (hk : k ≤ b) :
    pivotBound a b d.degree k ≤ packingNumber d.graph := by
  exact max_le (d.rectangle_left_bound k hk) (d.rectangle_top_bound k hk)

theorem oneSideBound_le : oneSideBound a b d.degree ≤ packingNumber d.graph := by
  apply Finset.sup_le
  intro k hk
  exact d.pivotBound_le k (by have := Finset.mem_range.mp hk; omega)

theorem rectangleBound_le : rectangleBound a b d.degree ≤ packingNumber d.graph := by
  apply max_le (d.complete_bound)
  apply max_le d.oneSideBound_le
  have h := d.transpose.oneSideBound_le
  rw [packingNumber_iso d.transposeIso] at h
  exact h

theorem cutTest_sound (h : cutTest a b d.degree = true) : Inequality d.graph := by
  simp only [cutTest, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨r, hr, t, ht, flip, _, hsize⟩ := h
  have hra : r ≤ a := by have := List.mem_range.mp hr; omega
  have htb : t ≤ b := by have := List.mem_range.mp ht; omega
  exact (d.ordered_cut_bound r t flip hra htb).trans
    (hsize.trans (Nat.mul_le_mul_left 2 d.rectangleBound_le))

end FerrersProfile

end ResearchMain.Tuza
