import Dowling.DiscreteMidpointTheorem

noncomputable section
namespace Dowling
open Finset

theorem finite_strict_multiplier {ι : Type*} (s : Finset ι) (A B : ι→ℝ)
    (hA : ∀ i,0≤A i) (hB : ∀ i,0≤B i)
    (hstrict : ∀ i∈s,0<A i → A i<B i) :
    ∃ t : ℝ,1<t ∧ ∀ i∈s,t*A i≤B i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨2,by norm_num,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t,ht,hbound⟩ := ih (fun i hi=>hstrict i (mem_insert_of_mem hi))
    by_cases hzero : A a=0
    · refine ⟨t,ht,?_⟩
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simpa [hzero] using hB i
      · exact hbound i hi
    · have hpos : 0<A a := lt_of_le_of_ne (hA a) (Ne.symm hzero)
      have hgap := hstrict a (mem_insert_self _ _) hpos
      let u := (1+B a/A a)/2
      have hu : 1<u := by dsimp [u]; rw [lt_div_iff₀ (by norm_num)];
                                       have := (one_lt_div hpos).mpr hgap; linarith
      have hua : u*A a≤B a := by dsimp [u]; field_simp; nlinarith
      refine ⟨min t u,lt_min ht hu,?_⟩
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hA i)).trans hua
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hA i)).trans (hbound i hi)

/-- A strict finite pointwise margin gives strict midpoint log-concavity. -/
theorem discrete_midpoint_strict (f g h : ℤ→ℝ) (N : ℕ)
    (hf : ∀ i,0≤f i) (hg : ∀ i,0≤g i) (hh : ∀ i,0≤h i)
    (hf0 : ∀ i,i < 0 ∨ (N : ℤ) < i → f i=0)
    (hg0 : ∀ i,i < 0 ∨ (N : ℤ) < i → g i=0)
    (hh0 : ∀ i,i < 0 ∨ (N : ℤ) < i → h i=0)
    (hstrict : ∀ i j,0<f i*g j → f i*g j<h ((i+j)/2)*h ((i+j+1)/2))
    (hpos : 0<(∑ i ∈ range (N+1),f i)*(∑ i ∈ range (N+1),g i)) :
    (∑ i ∈ range (N+1),f i)*(∑ i ∈ range (N+1),g i)<
      (∑ i ∈ range (N+1),h i)^2 := by
  let A : ℕ×ℕ→ℝ := fun ij=>f ij.1*g ij.2
  let B : ℕ×ℕ→ℝ := fun ij=>h (((ij.1 : ℤ)+ij.2)/2)*h (((ij.1 : ℤ)+ij.2+1)/2)
  obtain ⟨t,ht,hbound⟩ := finite_strict_multiplier ((range (N+1))×ˢ(range (N+1))) A B
    (fun i=>mul_nonneg (hf _) (hg _)) (fun i=>mul_nonneg (hh _) (hh _))
    (fun i _=>hstrict _ _)
  have hmid (i j : ℤ) : (t*f i)*g j≤h ((i+j)/2)*h ((i+j+1)/2) := by
    by_cases hi : i < 0 ∨ (N : ℤ) < i
    · rw [hf0 i hi,mul_zero,zero_mul]
      exact mul_nonneg (hh _) (hh _)
    by_cases hj : j < 0 ∨ (N : ℤ) < j
    · rw [hg0 j hj,mul_zero]
      exact mul_nonneg (hh _) (hh _)
    have hb := hbound (i.toNat,j.toNat) (mem_product.mpr
      ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩)
    have hi0 : (i.toNat : ℤ)=i := by omega
    have hj0 : (j.toNat : ℤ)=j := by omega
    dsimp [A,B] at hb
    rw [hi0,hj0] at hb
    nlinarith [hb]
  have hw := discrete_midpoint_four_functions (fun i=>t*f i) g h h N
    (fun i=>mul_nonneg (by linarith) (hf i)) hg hh hh hg0 hh0 hh0 hmid
  rw [← Finset.mul_sum] at hw
  nlinarith [hw]

end Dowling
