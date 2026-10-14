import Dowling.ActualApexWeightsRatio

noncomputable section
namespace Dowling
open Finset

def shiftedQuadraticWeight (h : ℕ) (v : ℕ→ℝ) (j : ℕ) : ℝ := if h≤j then v (j-h) else 0

theorem quadraticWeightedRow_shift (h : ℕ) (v : ℕ→ℝ) (a : ℝ) (n k : ℕ) (hn : 2*h≤n) :
    quadraticWeightedRow (shiftedQuadraticWeight h v) a n k=
      if h≤k ∧ k+h≤n then quadraticWeightedRow v a (n-2*h) (k-h) else 0 := by
  by_cases hk : k≤n
  · rw [quadraticWeightedRow,ite_eq_left hk]
    simp only [shiftedQuadraticWeight,ite_mul,zero_mul]
    by_cases hg : h≤k ∧ k+h≤n
    · rw [ite_eq_left hg,quadraticWeightedRow,ite_eq_left (by omega)]
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun j _ => j-h)
      · intro j hj
        have hj' := Finset.mem_filter.mp hj
        have hjr := Finset.mem_range.mp hj'.1
        apply Finset.mem_range.mpr
        omega
      · intro j hj l hl he
        have hj' := (Finset.mem_filter.mp hj).2
        have hl' := (Finset.mem_filter.mp hl).2
        omega
      · intro l hl
        have hl' := Finset.mem_range.mp hl
        refine ⟨l+h,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩,by omega⟩
      · intro j hj
        have hj' := Finset.mem_filter.mp hj
        have hjr := Finset.mem_range.mp hj'.1
        rw [show k-h-(j-h)=k-j by omega,
          show n-2*h-(k-h)-(j-h)=n-k-j by omega]
    · rw [ite_eq_right hg]
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [ite_eq_right (by omega)]
  · rw [quadraticWeightedRow,ite_eq_right hk,ite_eq_right (by omega)]

theorem quadraticWeightedRow_sum {ι : Type*} (S : Finset ι) (v : ι→ℕ→ℝ)
    (a : ℝ) (n k : ℕ) :
    quadraticWeightedRow (fun j => ∑ i∈S,v i j) a n k=
      ∑ i∈S,quadraticWeightedRow (v i) a n k := by
  by_cases hk : k≤n
  · simp only [quadraticWeightedRow,ite_eq_left hk,Finset.sum_mul]
    rw [Finset.sum_comm]
  · simp [quadraticWeightedRow,hk]

theorem quadraticWeightedRow_congr_support (v w : ℕ→ℝ) (a : ℝ) (n k : ℕ)
    (h : ∀ j,2*j≤n → v j=w j) : quadraticWeightedRow v a n k=quadraticWeightedRow w a n k := by
  by_cases hk : k≤n
  · simp only [quadraticWeightedRow,ite_eq_left hk]
    apply sum_congr rfl
    intro j hj
    rw [h j (by have := mem_range.mp hj; omega)]
  · simp [quadraticWeightedRow,hk]

end Dowling
