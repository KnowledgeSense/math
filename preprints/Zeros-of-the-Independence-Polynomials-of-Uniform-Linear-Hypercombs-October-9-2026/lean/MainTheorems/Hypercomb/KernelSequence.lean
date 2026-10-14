import MainTheorems.Hypercomb.Continuants

namespace ResearchMain.Hypercomb

variable {K : Type*} [CommRing K]

def kernelSequence (A B z q : K) (n : ℕ) : K := q ^ n * boundaryContinuant A B z n

theorem kernelSequence_zero (A B z q : K) : kernelSequence A B z q 0 = 1 := by
  simp [kernelSequence, boundaryContinuant]

theorem kernelSequence_first {A B z q c : K} (hcq : c * q = -1) :
    (A + z) * kernelSequence A B z q 0 + c * kernelSequence A B z q 1 = 0 := by
  simp only [kernelSequence, boundaryContinuant, pow_zero, mul_one, pow_one]
  calc
    (A + z) + c * (q * (A + z)) = (1 + c * q) * (A + z) := by ring
    _ = 0 := by rw [hcq]; ring

theorem kernelSequence_middle {A B z q c : K} (hcq : c * q = -1)
    (hBq : B * q ^ 2 = -1) (n : ℕ) :
    c * kernelSequence A B z q n + A * kernelSequence A B z q (n + 1) +
      c * kernelSequence A B z q (n + 2) = 0 := by
  have h₁ : c + c * q ^ 2 * B = 0 := by
    calc
      c + c * q ^ 2 * B = c * (1 + B * q ^ 2) := by ring
      _ = 0 := by rw [hBq]; ring
  have h₂ : A * q + c * q ^ 2 * A = 0 := by
    calc
      A * q + c * q ^ 2 * A = A * q * (1 + c * q) := by ring
      _ = 0 := by rw [hcq]; ring
  simp only [kernelSequence]
  rw [boundaryContinuant]
  calc
    _ = q ^ n * ((c + c * q ^ 2 * B) * boundaryContinuant A B z n +
      (A * q + c * q ^ 2 * A) * boundaryContinuant A B z (n + 1)) := by
        simp only [pow_add, pow_one]
        ring
    _ = 0 := by rw [h₁, h₂]; ring

theorem kernelSequence_last {A B z q c : K} (hBq : B * q = c)
    (n : ℕ) (hroot : boundaryContinuant A B z (n + 2) +
      z * boundaryContinuant A B z (n + 1) = 0) :
    c * kernelSequence A B z q n + (A + z) * kernelSequence A B z q (n + 1) = 0 := by
  have hid : c * kernelSequence A B z q n + (A + z) * kernelSequence A B z q (n + 1) =
      q ^ (n + 1) * (boundaryContinuant A B z (n + 2) + z * boundaryContinuant A B z (n + 1)) := by
    simp only [kernelSequence, pow_succ, boundaryContinuant]
    rw [← hBq]
    ring
  rw [hid, hroot, mul_zero]

theorem kernel_coefficients {K : Type*} [Field K] (B c : K) (hc : c ≠ 0) (hsq : c ^ 2 = -B) :
    c * (-c⁻¹) = -1 ∧ B * (-c⁻¹) ^ 2 = -1 ∧ B * (-c⁻¹) = c := by
  have hB : B = -c ^ 2 := by linear_combination hsq
  refine ⟨by simp [hc], ?_, ?_⟩
  · rw [hB]
    field_simp
  · rw [hB]
    field_simp

end ResearchMain.Hypercomb
