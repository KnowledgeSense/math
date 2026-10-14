import ChowlaCosine.FourierPolynomial
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Order.Compact

/-! The exact passage from arbitrary positive integer frequencies to a symmetric support. -/
namespace ChowlaCosine

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

/-- The original real cosine sum, with no restriction on the frequency gaps or sizes. -/
noncomputable def cosineSum {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ j, s j * Real.cos (2 * Real.pi * (a j : ℝ) * x)

/-- The corresponding real continuous function on the circle. -/
noncomputable def cosineCircle {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ)
    (x : Circle) : ℝ := ∑ j, s j * (fourier (a j) x).re

/-- The finite symmetric support `{a_j,-a_j}`. -/
def symmetricSupport {N : ℕ} (a : Fin N → ℤ) : Finset ℤ :=
  Finset.univ.image a ∪ Finset.univ.image (fun j => -a j)

/-- Extend the given real weights to both signs, without discretizing the coefficients. -/
noncomputable def symmetricWeight {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) (m : ℤ) : ℝ :=
  ∑ j, ((if a j = m then s j else 0) + (if a j = -m then s j else 0))

@[simp] theorem mem_symmetricSupport {N : ℕ} (a : Fin N → ℤ) (m : ℤ) :
    m ∈ symmetricSupport a ↔ (∃ j, a j = m) ∨ (∃ j, -a j = m) := by
  simp [symmetricSupport]

theorem symmetricSupport_neg {N : ℕ} (a : Fin N → ℤ) (m : ℤ) :
    -m ∈ symmetricSupport a ↔ m ∈ symmetricSupport a := by
  simp only [mem_symmetricSupport]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact Or.inr ⟨j, by omega⟩
    · exact Or.inl ⟨j, by omega⟩
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact Or.inr ⟨j, by omega⟩
    · exact Or.inl ⟨j, by omega⟩

theorem symmetricSupport_nonempty {N : ℕ} (a : Fin N → ℤ) (hN : 0 < N) :
    (symmetricSupport a).Nonempty := by
  refine ⟨a ⟨0, hN⟩, ?_⟩
  exact (mem_symmetricSupport a _).2 (Or.inl ⟨⟨0, hN⟩, rfl⟩)

theorem zero_not_mem_symmetricSupport {N : ℕ} {a : Fin N → ℤ}
    (hpos : ∀ j, 0 < a j) : 0 ∉ symmetricSupport a := by
  intro h
  rcases (mem_symmetricSupport a 0).mp h with ⟨j, hj⟩ | ⟨j, hj⟩ <;>
    have hp := hpos j <;> omega

theorem symmetricSupport_disjoint {N : ℕ} {a : Fin N → ℤ}
    (hpos : ∀ j, 0 < a j) :
    Disjoint (Finset.univ.image a) (Finset.univ.image (fun j => -a j)) := by
  apply Finset.disjoint_left.mpr
  intro m hm hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hn
  have hpi := hpos i
  have hpj := hpos j
  omega

/-- Positive and negative frequencies give exactly `2N` distinct support elements. -/
theorem symmetricSupport_card {N : ℕ} {a : Fin N → ℤ}
    (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j) :
    (symmetricSupport a).card = 2*N := by
  have hneg : Function.Injective (fun j => -a j) := fun i j hij => hinj (neg_injective hij)
  rw [symmetricSupport, Finset.card_union_of_disjoint (symmetricSupport_disjoint hpos),
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hneg]
  simp [two_mul]

@[simp] theorem symmetricWeight_neg {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) (m : ℤ) :
    symmetricWeight a s (-m) = symmetricWeight a s m := by
  unfold symmetricWeight
  apply Finset.sum_congr rfl
  intro j hj
  simp [add_comm]

theorem symmetricWeight_at_positive {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j) (j : Fin N) :
    symmetricWeight a s (a j) = s j := by
  have hneq : ∀ i, a i ≠ -a j := by
    intro i h
    have hi := hpos i
    have hj := hpos j
    omega
  simp [symmetricWeight, hinj.eq_iff, hneq]

theorem symmetricWeight_at_negative {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j) (j : Fin N) :
    symmetricWeight a s (-a j) = s j := by
  rw [symmetricWeight_neg, symmetricWeight_at_positive s hinj hpos]

/-- Every original real coefficient is transported unchanged to both signs. -/
theorem symmetricWeight_mem_Icc {N : ℕ} {a : Fin N → ℤ} {s : Fin N → ℝ} {α β : ℝ}
    (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hs : ∀ j, s j ∈ Set.Icc α β) :
    ∀ m ∈ symmetricSupport a, symmetricWeight a s m ∈ Set.Icc α β := by
  intro m hm
  rcases (mem_symmetricSupport a m).mp hm with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [symmetricWeight_at_positive s hinj hpos]
    exact hs j
  · rw [symmetricWeight_at_negative s hinj hpos]
    exact hs j

/-- The real part of the circle character is the original cosine. -/
theorem fourier_real_part (m : ℤ) (x : ℝ) :
    (fourier m (x : Circle)).re = Real.cos (2*Real.pi*(m : ℝ)*x) := by
  rw [fourier_coe_apply]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

theorem cosineCircle_coe {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) (x : ℝ) :
    cosineCircle a s (x : Circle) = cosineSum a s x := by
  simp only [cosineCircle, cosineSum, fourier_real_part]

theorem continuous_cosineCircle {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) :
    Continuous (cosineCircle a s) := by
  apply continuous_finsetSum
  intro j hj
  exact (Complex.continuous_re.comp (fourier (a j)).continuous).const_mul (s j)

/-- The exact symmetric-polynomial identity on the circle. -/
theorem symmetric_polynomial_eq_twice_cosineCircle {N : ℕ} {a : Fin N → ℤ}
    (s : Fin N → ℝ) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j) (x : Circle) :
    polynomial (symmetricSupport a) (symmetricWeight a s) x =
      (2 : ℂ) * (cosineCircle a s x : ℂ) := by
  have hneg : Function.Injective (fun j => -a j) := fun i j hij => hinj (neg_injective hij)
  rw [polynomial_apply, symmetricSupport,
    Finset.sum_union (symmetricSupport_disjoint hpos),
    Finset.sum_image (fun i hi j hj hij => hinj hij),
    Finset.sum_image (fun i hi j hj hij => hneg hij)]
  simp only [symmetricWeight_at_positive s hinj hpos,
    symmetricWeight_at_negative s hinj hpos, fourier_neg]
  rw [← Finset.sum_add_distrib]
  simp only [cosineCircle, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The exact identity used to pass back to the original real cosine sum. -/
theorem symmetric_polynomial_eq_twice_cosineSum {N : ℕ} {a : Fin N → ℤ}
    (s : Fin N → ℝ) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j) (x : ℝ) :
    polynomial (symmetricSupport a) (symmetricWeight a s) (x : Circle) =
      (2 : ℂ) * (cosineSum a s x : ℂ) := by
  rw [symmetric_polynomial_eq_twice_cosineCircle s hinj hpos, cosineCircle_coe]

/-- Every continuous real function on the circle attains a global minimum. -/
theorem circle_minimum_exists {f : Circle → ℝ} (hf : Continuous f) :
    ∃ x₀ : Circle, ∀ x : Circle, f x₀ ≤ f x := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set Circle).Nonempty) hf.continuousOn
  exact ⟨x₀, fun x => hmin (Set.mem_univ x)⟩

/-- Every original cosine sum attains its global minimum within the first real period. -/
theorem cosineSum_minimum_exists {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1, ∀ x : ℝ, cosineSum a s x₀ ≤ cosineSum a s x := by
  obtain ⟨z, hz⟩ := circle_minimum_exists (continuous_cosineCircle a s)
  let r := AddCircle.equivIco (1 : ℝ) 0 z
  refine ⟨r.val, ?_, ?_⟩
  · simpa using r.property
  · intro x
    have hr : (r.val : Circle) = z := AddCircle.coe_equivIco
    have h := hz (x : Circle)
    rw [← hr, cosineCircle_coe, cosineCircle_coe] at h
    exact h

/-- The real cosine sum is genuinely one-periodic. -/
theorem cosineSum_periodic {N : ℕ} (a : Fin N → ℤ) (s : Fin N → ℝ) :
    Function.Periodic (cosineSum a s) 1 := by
  intro x
  rw [← cosineCircle_coe, ← cosineCircle_coe, AddCircle.coe_add_period]

/-- A circle minimum has a representative in the first half-open real period. -/
theorem circle_minimum_representative {f : Circle → ℝ} (hf : Continuous f) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1, ∀ z : Circle, f (x₀ : Circle) ≤ f z := by
  obtain ⟨z₀, hz₀⟩ := circle_minimum_exists hf
  let r := AddCircle.equivIco (1 : ℝ) 0 z₀
  refine ⟨r.val, ?_, ?_⟩
  · simpa using r.property
  · intro z
    have hr : (r.val : Circle) = z₀ := AddCircle.coe_equivIco
    rw [hr]
    exact hz₀ z

/-- The real part of every finite circle polynomial has an attained real-period minimum. -/
theorem polynomial_minimum_exists (A : Finset ℤ) (s : ℤ → ℝ) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1, ∀ z : Circle,
      (polynomial A s (x₀ : Circle)).re ≤ (polynomial A s z).re :=
  circle_minimum_representative (Complex.continuous_re.comp (polynomial A s).continuous)

/-- A minimum of the original sum supplies exactly the `K` used in the symmetric theorem. -/
theorem cosine_minimum_bridge {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1, ∃ K : ℝ,
      K = -2*cosineSum a s x₀ ∧
      (∀ z : Circle, -K ≤ (polynomial (symmetricSupport a) (symmetricWeight a s) z).re) ∧
      (∀ x : ℝ, cosineSum a s x₀ ≤ cosineSum a s x) := by
  obtain ⟨x₀, hx₀, hmin⟩ :=
    polynomial_minimum_exists (symmetricSupport a) (symmetricWeight a s)
  let K := -(polynomial (symmetricSupport a) (symmetricWeight a s) (x₀ : Circle)).re
  have heq (x : ℝ) :
      (polynomial (symmetricSupport a) (symmetricWeight a s) (x : Circle)).re =
        2*cosineSum a s x := by
    rw [symmetric_polynomial_eq_twice_cosineSum s hinj hpos]
    simp
  refine ⟨x₀, hx₀, K, ?_, ?_, ?_⟩
  · dsimp [K]
    rw [heq]
    ring
  · intro z
    simpa [K] using hmin z
  · intro x
    have h := hmin (x : Circle)
    rw [heq, heq] at h
    linarith

end ChowlaCosine
