import GenericValueSemigroups.Bidiagonal
import Mathlib.Data.Nat.Choose.Basic

namespace GenericValueSemigroups
open Matrix Finset

def pascalStage (N k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j ≤ i then ((min i.val k).choose (i.val-j.val) : ℝ) else 0

def lowerStep (N k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (1 : Matrix (Fin N) (Fin N) ℝ) +
    (Matrix.of fun i j : Fin N => if i.val = j.val + 1 ∧ k ≤ i.val then (1 : ℝ) else 0)

theorem lowerStep_band {N k : ℕ} (i j : Fin N) (h : lowerStep N k i j ≠ 0) :
    j.val ≤ i.val ∧ i.val ≤ j.val+1 := by
  simp only [lowerStep, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply] at h
  split_ifs at h <;> simp_all

theorem lowerStep_totallyNonneg (N k : ℕ) : (lowerStep N k).IsTotallyNonneg := by
  apply totallyNonneg_of_lower_bidiagonal
  · intro i j
    simp only [lowerStep, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
    split_ifs <;> norm_num
  · exact lowerStep_band

theorem lowerStep_mul_zero {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (hi : i.val = 0) : (lowerStep N k * A) i j = A i j := by
  rw [lowerStep, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  have hz : ((Matrix.of fun i j : Fin N => if i.val = j.val+1 ∧ k ≤ i.val then (1:ℝ) else 0)*A) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    simp [show ¬(i.val=a.val+1 ∧ k ≤ i.val) by omega]
  rw [hz, add_zero]

theorem lowerStep_mul_pos {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) (hi : 0 < i.val) :
    (lowerStep N k * A) i j = A i j +
      if k ≤ i.val then A ⟨i.val-1, by omega⟩ j else 0 := by
  rw [lowerStep, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i.val-1, by omega⟩ : Fin N)]
  · change (if i.val=i.val-1+1 ∧ k ≤ i.val then (1:ℝ) else 0) * _ = _
    have he : (i.val=i.val-1+1 ∧ k ≤ i.val) ↔ k ≤ i.val := by omega
    simp only [he, ite_mul, one_mul, zero_mul]
  · intro b _ hb
    have hb' : i.val ≠ b.val+1 := by
      intro he
      apply hb
      apply Fin.ext
      change b.val = i.val - 1
      omega
    simp [hb']
  · simp

@[simp] theorem pascalStage_zero (N : ℕ) : pascalStage N 0 = 1 := by
  ext i j
  simp only [pascalStage, Nat.min_zero, Matrix.one_apply]
  by_cases h : i = j
  · subst j; simp
  · have hval : i.val ≠ j.val := fun he => h (Fin.ext he)
    by_cases hji : j ≤ i
    · have hp : 0 < i.val-j.val := by omega
      simp [h, hji, Nat.choose_eq_zero_of_lt hp]
    · simp [h, hji]

theorem lowerStep_mul_pascalStage (N k : ℕ) :
    lowerStep N (k+1) * pascalStage N k = pascalStage N (k+1) := by
  ext i j
  by_cases hi : i.val = 0
  · rw [lowerStep_mul_zero _ i j hi]
    simp [pascalStage, hi]
  · have hip : 0 < i.val := by omega
    rw [lowerStep_mul_pos _ i j hip]
    by_cases hk : k+1 ≤ i.val
    · rw [ite_eq_left hk]
      have hmin : min i.val k = k := Nat.min_eq_right (by omega)
      have hmin' : min (i.val-1) k = k := Nat.min_eq_right (by omega)
      have hmin'' : min i.val (k+1) = k+1 := Nat.min_eq_right hk
      by_cases hji : j < i
      · have hle : j ≤ i := le_of_lt hji
        have hle' : j ≤ (⟨i.val-1, by omega⟩ : Fin N) := by
          change j.val ≤ i.val-1; omega
        simp only [pascalStage, ite_eq_left hle, ite_eq_left hle',
          hmin, hmin', hmin'']
        have hd : i.val-j.val = (i.val-1-j.val)+1 := by omega
        rw [hd, Nat.choose_succ_succ', Nat.cast_add]
        exact add_comm _ _
      · by_cases he : j = i
        · subst j
          have hnot : ¬ i ≤ (⟨i.val-1, by omega⟩ : Fin N) := by
            change ¬i.val ≤ i.val-1; omega
          simp [pascalStage, hnot]
        · have hn : ¬j ≤ i := by omega
          have hn' : ¬j ≤ (⟨i.val-1, by omega⟩ : Fin N) := by
            change ¬j.val ≤ i.val-1; omega
          simp [pascalStage, hn, hn']
    · rw [ite_eq_right hk, add_zero]
      have hmin : min i.val k = i.val := Nat.min_eq_left (by omega)
      have hmin' : min i.val (k+1) = i.val := Nat.min_eq_left (by omega)
      simp [pascalStage, hmin, hmin']

theorem pascalStage_totallyNonneg (N k : ℕ) : (pascalStage N k).IsTotallyNonneg := by
  induction k with
  | zero => rw [pascalStage_zero]; exact Matrix.IsTotallyNonneg.one
  | succ k ih =>
    rw [← lowerStep_mul_pascalStage]
    exact totallyNonneg_mul (lowerStep_totallyNonneg N (k+1)) ih

/-- Every feasible minor of a partial Pascal product is strictly positive. -/
theorem pascalStage_minor_pos {N q : ℕ} (k : ℕ) (rows cols : Fin q → Fin N)
    (hr : StrictMono rows) (hc : StrictMono cols)
    (hle : ∀ i, cols i ≤ rows i) (hgap : ∀ i, (rows i).val ≤ (cols i).val+k) :
    0 < ((pascalStage N k).submatrix rows cols).det := by
  induction k generalizing rows with
  | zero =>
    have he : rows = cols := by
      funext i
      apply le_antisymm
      · have := hgap i; change (rows i).val ≤ (cols i).val; omega
      · exact hle i
    rw [he, pascalStage_zero, Matrix.submatrix_one _ hc.injective, Matrix.det_one]
    exact zero_lt_one
  | succ k ih =>
    let mid : Fin q → Fin N := fun i => ⟨min (rows i).val ((cols i).val+k),
      lt_of_le_of_lt (Nat.min_le_left _ _) (rows i).isLt⟩
    have hm : StrictMono mid := by
      intro i j hij
      have hr' : (rows i).val < (rows j).val := hr hij
      have hc' : (cols i).val < (cols j).val := hc hij
      change min (rows i).val ((cols i).val+k) < min (rows j).val ((cols j).val+k)
      omega
    have hcm : ∀ i, cols i ≤ mid i := by
      intro i
      have h := hle i
      change (cols i).val ≤ min (rows i).val ((cols i).val+k)
      exact Nat.le_min.mpr ⟨h, Nat.le_add_right _ _⟩
    have hmg : ∀ i, (mid i).val ≤ (cols i).val+k := fun i => Nat.min_le_right _ _
    have hb := ih mid hm hcm hmg
    have ha : 0 < ((lowerStep N (k+1)).submatrix rows mid).det := by
      rw [det_submatrix_lower_bidiagonal _ lowerStep_band rows mid hr hm]
      apply Finset.prod_pos
      intro i _
      have hg := hgap i
      have hmval : (mid i).val = min (rows i).val ((cols i).val+k) := rfl
      by_cases he : rows i = mid i
      · simp only [lowerStep, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, he]
        simp
      · have hv : (rows i).val = (mid i).val+1 := by
          have hn : (rows i).val ≠ (mid i).val := fun h => he (Fin.ext h)
          omega
        have hk : k ≤ (mid i).val := by omega
        simp [lowerStep, he, hv, hk]
    rw [← lowerStep_mul_pascalStage]
    exact det_product_submatrix_pos (lowerStep_totallyNonneg N (k+1))
      (pascalStage_totallyNonneg N k) rows cols mid hr hc ha hb

end GenericValueSemigroups
