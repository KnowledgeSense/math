import Dowling.DowlingWeightedMixturePointwise

noncomputable section
namespace Dowling
open Finset

def weightedMixtureCoefficient (W : ℕ→ℝ) (p : ℝ) (n k : ℕ) : ℝ :=
  if k≤n then ∑ j∈range (min k (n-k)+1),W j*dowlingBinomialWeight p (k-j)*
    dowlingBinomialWeight p (n-k-j) else 0

theorem weightedMixtureFunction_nonneg {W : ℕ→ℝ} {p : ℝ} (n k : ℕ)
    (hW : ∀ j,2*j≤n→0<W j) (hp : 1<p) (j : ℤ) : 0≤weightedMixtureFunction W p n k j := by
  by_cases hj : j<0
  · simp [weightedMixtureFunction,hj]
  · rw [weightedMixtureFunction,ite_eq_right hj]
    exact weightedMixtureTerm_nonneg n k j.toNat hW hp

theorem weightedMixtureFunction_support (W : ℕ→ℝ) (p : ℝ) (n k : ℕ) (j : ℤ)
    (hj : j < 0 ∨ (n : ℤ) < j) : weightedMixtureFunction W p n k j=0 := by
  rcases hj with hj | hj
  · simp [weightedMixtureFunction,hj]
  · rw [weightedMixtureFunction,ite_eq_right (by omega),weightedMixtureTerm,
      ite_eq_right (by omega)]

theorem weightedMixtureFunction_sum (W : ℕ→ℝ) (p : ℝ) (n k : ℕ) :
    (∑ j ∈ range (n+1),weightedMixtureFunction W p n k j)=weightedMixtureCoefficient W p n k := by
  simp only [weightedMixtureFunction,Int.natCast_nonneg,not_lt,ite_eq_right,
    Int.toNat_natCast]
  by_cases hk : k≤n
  · rw [weightedMixtureCoefficient,ite_eq_left hk]
    symm
    calc
      _ = ∑ j ∈ range (min k (n-k)+1),weightedMixtureTerm W p n k j := by
        apply sum_congr rfl
        intro j hj
        rw [weightedMixtureTerm,ite_eq_left (by have := mem_range.mp hj; omega)]
      _ = _ := by
        apply sum_subset
        · intro j hj
          apply mem_range.mpr
          have := mem_range.mp hj
          omega
        · intro j hj hnot
          rw [weightedMixtureTerm,ite_eq_right (by simp only [mem_range] at hnot; omega)]
  · rw [weightedMixtureCoefficient,ite_eq_right hk]
    apply sum_eq_zero
    intro j hj
    rw [weightedMixtureTerm,ite_eq_right (by omega)]

theorem weightedMixtureFunction_sum_pos {W : ℕ→ℝ} {p : ℝ} (n k : ℕ) (hW : ∀ j,2*j≤n→0<W j)
    (hp : 1<p) (hk : k≤n) :
    0<∑ j ∈ range (n+1),weightedMixtureFunction W p n k j := by
  apply sum_pos'
  · intro j hj
    exact weightedMixtureFunction_nonneg n k hW hp j
  · refine ⟨0,mem_range.mpr (by omega),?_⟩
    simp only [Nat.cast_zero,weightedMixtureFunction,lt_self_iff_false,ite_false,Int.toNat_zero]
    exact weightedMixtureTerm_pos n k 0 hW hp (by omega)

theorem weightedMixtureFunction_midpoint_strict {W : ℕ→ℝ} {p : ℝ} (n k : ℕ)
    (hW : ∀ j,2*j≤n→0<W j)
    (hmid : ∀ i j,2*i≤n→2*j≤n→W i*W j≤W ((i+j)/2)*W ((i+j+1)/2))
    (hp : 1<p) (hk : 1≤k) (hkn : k<n) (i j : ℤ)
    (hpos : 0<weightedMixtureFunction W p n (k-1) i*weightedMixtureFunction W p n (k+1) j) :
    weightedMixtureFunction W p n (k-1) i*weightedMixtureFunction W p n (k+1) j <
      weightedMixtureFunction W p n k ((i+j)/2)*weightedMixtureFunction W p n k ((i+j+1)/2) := by
  have hi : ¬i<0 := by
    intro hi
    simp [weightedMixtureFunction,hi] at hpos
  have hj : ¬j<0 := by
    intro hj
    simp [weightedMixtureFunction,hj] at hpos
  have hi' : i.toNat≤k-1 ∧ k-1+i.toNat≤n := by
    by_contra hh
    have hz : weightedMixtureFunction W p n (k-1) i=0 := by
      rw [weightedMixtureFunction,ite_eq_right hi,weightedMixtureTerm,ite_eq_right hh]
    rw [hz,zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hj' : j.toNat≤k+1 ∧ k+1+j.toNat≤n := by
    by_contra hh
    have hz : weightedMixtureFunction W p n (k+1) j=0 := by
      rw [weightedMixtureFunction,ite_eq_right hj,weightedMixtureTerm,ite_eq_right hh]
    rw [hz,mul_zero] at hpos
    exact lt_irrefl _ hpos
  have h := weightedMixtureTerm_midpoint_strict n k i.toNat j.toNat hW hmid hp hk hkn hi' hj'
  have hu : ¬(i+j)/2<0 := by omega
  have hv : ¬(i+j+1)/2<0 := by omega
  have hue : ((i+j)/2).toNat=(i.toNat+j.toNat)/2 := by omega
  have hve : ((i+j+1)/2).toNat=(i.toNat+j.toNat+1)/2 := by omega
  simpa only [weightedMixtureFunction,ite_eq_right hi,ite_eq_right hj,
    ite_eq_right hu,ite_eq_right hv,hue,hve] using h

end Dowling
