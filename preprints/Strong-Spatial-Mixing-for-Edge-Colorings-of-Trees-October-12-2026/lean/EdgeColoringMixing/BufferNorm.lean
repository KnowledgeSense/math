import EdgeColoringMixing.MessageDomain
import EdgeColoringMixing.ScalarTransfer
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

/-! The arcsine tangent norm with the paper's zero-coordinate convention, and its
uniform conversion bounds after the two exact recursion levels. -/
namespace EdgeColoringMixing
open Finset Matrix

/-- Division by zero is zero, so the sum agrees with the restriction to `0 < A < 1`.
The tangent condition at coordinates zero and one is stated separately. -/
noncomputable def arcsineNormSq {q : ℕ} (A ξ : Fin q → ℝ) : ℝ :=
  ∑ c, ξ c ^ 2 / (A c * (1 - A c))

noncomputable def arcsineNorm {q : ℕ} (A ξ : Fin q → ℝ) : ℝ :=
  Real.sqrt (arcsineNormSq A ξ)

def EndpointTangent {q : ℕ} (A ξ : Fin q → ℝ) : Prop :=
  ∀ c, A c = 0 ∨ A c = 1 → ξ c = 0

namespace arcsineNorm
variable {q : ℕ} {A ξ : Fin q → ℝ}

theorem square_nonneg (hA0 : ∀ c, 0 ≤ A c) (hA1 : ∀ c, A c ≤ 1) :
    0 ≤ arcsineNormSq A ξ :=
  sum_nonneg (fun c _ => div_nonneg (sq_nonneg _) (mul_nonneg (hA0 c) (by linarith [hA1 c])))

theorem nonneg : 0 ≤ arcsineNorm A ξ := Real.sqrt_nonneg _

theorem sq (hA0 : ∀ c, 0 ≤ A c) (hA1 : ∀ c, A c ≤ 1) :
    arcsineNorm A ξ ^ 2 = arcsineNormSq A ξ := Real.sq_sqrt (square_nonneg hA0 hA1)

/-- The exact zero-extended sum is the sum over the nonsingular coordinates. -/
theorem square_eq_interior (hA0 : ∀ c, 0 ≤ A c) (hA1 : ∀ c, A c ≤ 1) :
    arcsineNormSq A ξ = ∑ c ∈ univ.filter (fun c => 0 < A c ∧ A c < 1),
      ξ c ^ 2 / (A c * (1 - A c)) := by
  classical
  symm
  apply sum_subset (filter_subset _ _)
  intro c _ hc
  have hnot : ¬(0 < A c ∧ A c < 1) := by simpa using hc
  have he : A c = 0 ∨ A c = 1 := by
    by_cases h0 : A c = 0
    · exact Or.inl h0
    · exact Or.inr (le_antisymm (hA1 c) (not_lt.mp (fun h1 => hnot ⟨lt_of_le_of_ne (hA0 c) (Ne.symm h0), h1⟩)))
  rcases he with h | h <;> simp [h]

/-- A uniform speed and the two buffer gaps control the actual arcsine norm. -/
theorem buffer_square_bound {I : Finset (Fin q)} {a b M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hlo : ∀ c ∈ I, a ≤ A c) (hhi : ∀ c ∈ I, A c ≤ 1 - b)
    (hzero : ∀ c ∉ I, ξ c = 0) (hspeed : ∀ c, |ξ c| ≤ M) :
    arcsineNormSq A ξ ≤ (q : ℝ) * M ^ 2 / (a * b) := by
  have hab : 0 < a * b := mul_pos ha hb
  calc
    _ ≤ ∑ _c : Fin q, M ^ 2 / (a * b) := by
      apply sum_le_sum
      intro c _
      by_cases hc : c ∈ I
      · have hAc : 0 < A c := ha.trans_le (hlo c hc)
        have hBc : b ≤ 1 - A c := by linarith [hhi c hc]
        have hprod : a * b ≤ A c * (1 - A c) :=
          mul_le_mul (hlo c hc) hBc hb.le hAc.le
        have hsq : ξ c ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs (ξ c), hspeed c, abs_nonneg (ξ c)]
        exact (div_le_div_of_nonneg_right hsq (hab.le.trans hprod)).trans
          (div_le_div_of_nonneg_left (sq_nonneg M) hab hprod)
      · simp [hzero c hc, div_nonneg (sq_nonneg M) hab.le]
    _ = _ := by simp; ring

theorem buffer_bound {I : Finset (Fin q)} {a b M : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 ≤ M)
    (hlo : ∀ c ∈ I, a ≤ A c) (hhi : ∀ c ∈ I, A c ≤ 1 - b)
    (hzero : ∀ c ∉ I, ξ c = 0) (hspeed : ∀ c, |ξ c| ≤ M) :
    arcsineNorm A ξ ≤ Real.sqrt q * M / Real.sqrt (a * b) := by
  unfold arcsineNorm
  calc
    _ ≤ Real.sqrt ((q : ℝ) * M ^ 2 / (a * b)) :=
      Real.sqrt_le_sqrt (buffer_square_bound ha hb hM hlo hhi hzero hspeed)
    _ = _ := by
      rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)),
        Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

/-- Tangency at endpoints makes the pointwise Euclidean-to-arcsine conversion valid. -/
theorem euclidean_square_bound (hA0 : ∀ c, 0 ≤ A c) (hA1 : ∀ c, A c ≤ 1)
    (htan : EndpointTangent A ξ) :
    (∑ c, ξ c ^ 2) ≤ arcsineNormSq A ξ / 4 := by
  rw [arcsineNormSq, Finset.sum_div]
  apply sum_le_sum
  intro c _
  by_cases he : A c = 0 ∨ A c = 1
  · simp [htan c he]
  · have h0 : 0 < A c := lt_of_le_of_ne (hA0 c) (Ne.symm (fun h => he (Or.inl h)))
    have h1 : A c < 1 := lt_of_le_of_ne (hA1 c) (fun h => he (Or.inr h))
    have hv : 0 < A c * (1 - A c) := mul_pos h0 (by linarith)
    have hv4 : A c * (1 - A c) ≤ 1 / 4 := by nlinarith [sq_nonneg (A c - 1 / 2)]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    apply (le_div_iff₀ hv).mpr
    nlinarith [mul_le_mul_of_nonneg_left hv4 (sq_nonneg (ξ c))]

/-- The observed-edge conversion with the original factor `sqrt q / 2`. -/
theorem l1_bound (hA0 : ∀ c, 0 ≤ A c) (hA1 : ∀ c, A c ≤ 1)
    (htan : EndpointTangent A ξ) :
    (∑ c, |ξ c|) ≤ Real.sqrt q / 2 * arcsineNorm A ξ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin q))
    (fun _ => (1 : ℝ)) (fun c => |ξ c|)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  have hb := euclidean_square_bound hA0 hA1 htan
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ arcsineNorm A ξ := nonneg
  have hs : 0 ≤ ∑ c, |ξ c| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hr : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hsq := sq hA0 hA1 (ξ := ξ)
  have hqsq := Real.sq_sqrt hq
  have hh := mul_le_mul_of_nonneg_left hb hq
  have heq : (Real.sqrt q / 2 * arcsineNorm A ξ)^2 =
      (q : ℝ) * arcsineNormSq A ξ / 4 := by
    rw [mul_pow, div_pow, hsq, hqsq]
    ring
  have hright : 0 ≤ Real.sqrt q / 2 * arcsineNorm A ξ := mul_nonneg (div_nonneg hr (by norm_num)) hn
  nlinarith

end arcsineNorm
end EdgeColoringMixing
