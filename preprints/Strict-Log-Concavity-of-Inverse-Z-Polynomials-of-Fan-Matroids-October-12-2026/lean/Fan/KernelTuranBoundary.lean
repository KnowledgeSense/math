import Fan.KernelConvolution

noncomputable section
open scoped BigOperators
namespace Fan

def boundaryArray (A B rho : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ i∈Finset.range (a+1),∑ j∈Finset.range (b+1),A i*B j*rho (a+b-i-j)

theorem boundaryArray_zero_left (A B rho : ℕ → ℝ) (b : ℕ) :
    boundaryArray A B rho 0 b=A 0*(∑ j∈Finset.range (b+1),B j*rho (b-j)) := by
  simp [boundaryArray,Finset.mul_sum,mul_assoc]

theorem boundaryArray_zero_right (A B rho : ℕ → ℝ) (a : ℕ) :
    boundaryArray A B rho a 0=B 0*(∑ i∈Finset.range (a+1),A i*rho (a-i)) := by
  simp [boundaryArray,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem boundaryArray_difference (A B C rho : ℕ → ℝ)
    (hA : ∀ n,A n=∑ j∈Finset.range (n+1),B j*rho (n-j))
    (hC : ∀ n,C n=∑ j∈Finset.range (n+1),A j*rho (n-j)) (a b : ℕ) :
    boundaryArray A B rho (a+1) b-boundaryArray A B rho a (b+1) =
      A (a+1)*A b-C a*B (b+1) := by
  unfold boundaryArray
  rw [Finset.sum_range_succ]
  have he : (∑ i∈Finset.range (a+1),∑ j∈Finset.range (b+1+1),
      A i*B j*rho (a+(b+1)-i-j)) =
      (∑ i∈Finset.range (a+1),∑ j∈Finset.range (b+1),A i*B j*rho (a+b+1-i-j))+
        (∑ i∈Finset.range (a+1),A i*B (b+1)*rho (a-i)) := by
    conv_lhs => arg 2; ext i; rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 2
    · apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_range.mp hi
      congr 2 ; omega
  rw [he]
  have hf : (∑ j∈Finset.range (b+1),A (a+1)*B j*rho (a+1+b-(a+1)-j)) =
      A (a+1)*A b := by
    rw [hA b,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_assoc]
  have hg : (∑ i∈Finset.range (a+1),A i*B (b+1)*rho (a-i))=C a*B (b+1) := by
    rw [hC a,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf,hg]
  have hi : a+1+b=a+b+1 := by omega
  rw [hi]
  ring

def zeroExtend (A : ℕ → ℝ) (i : ℤ) : ℝ := if 0 ≤ i then A i.toNat else 0

def boundaryExtended (A B rho : ℕ → ℝ) (a b : ℤ) : ℝ :=
  if 0≤a ∧ 0≤b then boundaryArray A B rho a.toNat b.toNat else 0

@[simp] theorem zeroExtend_nat (A : ℕ → ℝ) (i : ℕ) : zeroExtend A i=A i := by simp [zeroExtend]
@[simp] theorem boundaryExtended_nat (A B rho : ℕ → ℝ) (a b : ℕ) :
    boundaryExtended A B rho a b=boundaryArray A B rho a b := by simp [boundaryExtended]

theorem boundaryExtended_difference (A B C rho : ℕ → ℝ)
    (hA : ∀ n,A n=∑ j∈Finset.range (n+1),B j*rho (n-j))
    (hC : ∀ n,C n=∑ j∈Finset.range (n+1),A j*rho (n-j)) (a b : ℤ) :
    zeroExtend A a*zeroExtend A b-zeroExtend C (a-1)*zeroExtend B (b+1) =
      boundaryExtended A B rho a b-boundaryExtended A B rho (a-1) (b+1) := by
  by_cases ha : 0≤a
  · lift a to ℕ using ha
    cases a with
    | zero =>
      by_cases hb : 0≤b
      · lift b to ℕ using hb
        simp [zeroExtend,boundaryExtended,boundaryArray_zero_left,← hA]
      · simp [zeroExtend,boundaryExtended,hb]
    | succ a =>
      have he : ((a+1:ℕ):ℤ)-1=a := by omega
      rw [he]
      by_cases hb : 0≤b
      · lift b to ℕ using hb
        have hb' : (b:ℤ)+1=(b+1:ℕ) := by omega
        rw [hb']
        simp only [zeroExtend_nat,boundaryExtended_nat]
        exact (boundaryArray_difference A B C rho hA hC a b).symm
      · by_cases hb' : b= -1
        · subst b
          simp [zeroExtend,boundaryExtended,boundaryArray_zero_right,← hC,mul_comm]
        · have hbn : ¬0≤b+1 := by omega
          simp [zeroExtend,boundaryExtended,hb,hbn]
  · have ha' : ¬1≤a := by omega
    simp [zeroExtend,boundaryExtended,ha,ha']

end Fan
