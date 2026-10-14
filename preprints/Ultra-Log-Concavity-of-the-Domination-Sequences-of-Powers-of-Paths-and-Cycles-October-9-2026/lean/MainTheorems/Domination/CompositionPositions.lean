import MainTheorems.Domination.CompositionSelection
import MainTheorems.Domination.PathCoverage

namespace ResearchMain.Domination

theorem interior_prefix_bounds {n : ℕ} (c : Composition (n + 1)) (i : ℕ)
    (hi0 : 1 ≤ i) (hic : i < c.length) :
    1 ≤ c.sizeUpTo i ∧ c.sizeUpTo i ≤ n := by
  have hlo := c.boundary.strictMono
    (show (0 : Fin (c.length + 1)) < ⟨i, by omega⟩ by
      change 0 < i
      omega)
  rw [c.boundary_zero] at hlo
  change 0 < c.sizeUpTo i at hlo
  have hhi := c.boundary.strictMono
    (show (⟨i, by omega⟩ : Fin (c.length + 1)) < Fin.last c.length by exact hic)
  rw [c.boundary_last] at hhi
  change c.sizeUpTo i < n + 1 at hhi
  omega

def compositionPositions {n k : ℕ} (c : Composition (n + 1)) (hlen : c.length = k + 2)
    (i : Fin (k + 1)) : Fin n :=
  ⟨c.sizeUpTo (i.val + 1) - 1, by
    have h := interior_prefix_bounds c (i.val + 1) (by omega) (by have := i.isLt; omega)
    omega⟩

@[simp] theorem compositionPositions_val {n k : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) (i : Fin (k + 1)) :
    (compositionPositions c hlen i).val = c.sizeUpTo (i.val + 1) - 1 := rfl

theorem compositionPositions_strictMono {n k : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) : StrictMono (compositionPositions c hlen) := by
  intro i j hij
  have hi := interior_prefix_bounds c (i.val + 1) (by omega) (by have := i.isLt; omega)
  have hpre := c.boundary.strictMono
    (show (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (c.length + 1)) <
      ⟨j.val + 1, by have := j.isLt; omega⟩ by
      change i.val + 1 < j.val + 1
      exact Nat.succ_lt_succ hij)
  change c.sizeUpTo (i.val + 1) < c.sizeUpTo (j.val + 1) at hpre
  change c.sizeUpTo (i.val + 1) - 1 < c.sizeUpTo (j.val + 1) - 1
  omega

theorem selectedVertices_image {n k : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    selectedVertices c = Finset.univ.image (compositionPositions c hlen) := by
  classical
  ext v
  rw [mem_selectedVertices]
  simp only [Composition.boundaries, Finset.mem_map, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨i, hi⟩
    have hsize := congrArg Fin.val hi
    change c.sizeUpTo i.val = v.val + 1 at hsize
    have hi0 : 1 ≤ i.val := by
      by_contra h
      have heq : i.val = 0 := by omega
      rw [heq, c.sizeUpTo_zero] at hsize
      omega
    have hic : i.val < c.length := by
      by_contra h
      rw [c.sizeUpTo_ofLength_le i.val (by omega)] at hsize
      have := v.isLt
      omega
    let j : Fin (k + 1) := ⟨i.val - 1, by omega⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    rw [compositionPositions_val]
    change c.sizeUpTo (i.val - 1 + 1) - 1 = v.val
    rw [Nat.sub_add_cancel hi0, hsize]
    omega
  · rintro ⟨j, hj⟩
    refine ⟨⟨j.val + 1, by have := j.isLt; omega⟩, ?_⟩
    apply Fin.ext
    change c.sizeUpTo (j.val + 1) = v.val + 1
    have hp := congrArg Fin.val hj
    rw [compositionPositions_val] at hp
    have hlo := interior_prefix_bounds c (j.val + 1) (by omega) (by have := j.isLt; omega)
    omega

theorem compositionPositions_first {n k : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    (compositionPositions c hlen 0).val =
      c.blocksFun ⟨0, by omega⟩ - 1 := by
  rw [compositionPositions_val]
  simp only [Fin.val_zero, zero_add]
  have h := c.sizeUpTo_succ' ⟨0, by omega⟩
  simp only [zero_add, Composition.sizeUpTo_zero] at h
  rw [h]

theorem compositionPositions_last {n k : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) :
    n - (compositionPositions c hlen (Fin.last k)).val =
      c.blocksFun ⟨k + 1, by omega⟩ := by
  rw [compositionPositions_val, Fin.val_last]
  have h := c.sizeUpTo_succ' ⟨k + 1, by omega⟩
  change c.sizeUpTo (k + 2) = c.sizeUpTo (k + 1) + c.blocksFun ⟨k + 1, by omega⟩ at h
  rw [← hlen, c.sizeUpTo_length] at h
  have hlo := interior_prefix_bounds c (k + 1) (by omega) (by omega)
  omega

theorem compositionPositions_step {n k : ℕ} (c : Composition (n + 1))
    (hlen : c.length = k + 2) (i : Fin k) :
    (compositionPositions c hlen i.succ).val =
      (compositionPositions c hlen i.castSucc).val +
        c.blocksFun ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  simp only [compositionPositions_val, Fin.val_succ, Fin.val_castSucc]
  have h := c.sizeUpTo_succ' ⟨i.val + 1, by have := i.isLt; omega⟩
  change c.sizeUpTo (i.val + 1 + 1) = c.sizeUpTo (i.val + 1) +
    c.blocksFun ⟨i.val + 1, by have := i.isLt; omega⟩ at h
  have hlo := interior_prefix_bounds c (i.val + 1) (by omega) (by have := i.isLt; omega)
  omega

end ResearchMain.Domination
