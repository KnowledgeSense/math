import GenericValueSemigroups.ExponentialMatrix
import Mathlib.RingTheory.PowerSeries.Exp

namespace GenericValueSemigroups
open Matrix Finset

noncomputable def seriesMatrix (N : ℕ) (f : PowerSeries ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j ≤ i then PowerSeries.coeff (i.val-j.val) f else 0

theorem seriesMatrix_mul (N : ℕ) (f g : PowerSeries ℝ) :
    seriesMatrix N (f*g) = seriesMatrix N f * seriesMatrix N g := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : j ≤ i
  · simp only [seriesMatrix, ite_eq_left hij, PowerSeries.coeff_mul]
    have he : (∑ k : Fin N,
        (if k ≤ i then PowerSeries.coeff (i.val-k.val) f else 0) *
        (if j ≤ k then PowerSeries.coeff (k.val-j.val) g else 0)) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin N => j ≤ k ∧ k ≤ i),
          PowerSeries.coeff (i.val-k.val) f * PowerSeries.coeff (k.val-j.val) g := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp_all
    rw [he]
    symm
    apply Finset.sum_bij (fun k _ => (i.val-k.val, k.val-j.val))
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      apply Finset.mem_antidiagonal.mpr
      have h1 : j.val ≤ k.val := hk.1
      have h2 : k.val ≤ i.val := hk.2
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      apply Fin.ext
      have h := congrArg Prod.fst hab
      have h1 : a.val ≤ i.val := ha.2
      have h2 : b.val ≤ i.val := hb.2
      omega
    · intro a ha
      have ha' := Finset.mem_antidiagonal.mp ha
      let k : Fin N := ⟨j.val+a.2, by have := i.isLt; omega⟩
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · change j.val ≤ j.val+a.2; omega
        · change j.val+a.2 ≤ i.val
          have hij' : j.val ≤ i.val := hij
          omega
      · apply Prod.ext <;> dsimp [k] <;> omega
    · intro a _; rfl
  · simp only [seriesMatrix, ite_eq_right hij]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k ≤ i
    · have hjk : ¬j ≤ k := fun h => hij (h.trans hki)
      simp [hjk]
    · simp [hki]

theorem exponentialMatrix_eq_seriesMatrix (N : ℕ) (s : ℝ) :
    exponentialMatrix N s = seriesMatrix N (PowerSeries.rescale s (PowerSeries.exp ℝ)) := by
  ext i j
  simp only [exponentialMatrix, seriesMatrix]
  congr 1
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv, mul_comm]

theorem exponentialMatrix_add (N : ℕ) (s t : ℝ) :
    exponentialMatrix N (s+t) = exponentialMatrix N s * exponentialMatrix N t := by
  simp only [exponentialMatrix_eq_seriesMatrix, ← PowerSeries.exp_mul_exp_eq_exp_add,
    seriesMatrix_mul]

end GenericValueSemigroups
