import MainTheorems.Chollet.PencilClosure
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Matrix
open scoped ComplexOrder

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

def border (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ) : Matrix (Unit ⊕ I) (Unit ⊕ I) ℂ :=
  fromBlocks (fun _ _ => (a : ℂ)) (fun _ j => star (z j)) (fun i _ => z i) B

def normalizedBorder (a : ℝ) (z : I → ℂ) : I → ℂ := fun i => z i / (Real.sqrt a : ℂ)

omit [Fintype I] in
theorem comparison_border (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ) :
    comparison (border a z B) =
      fromBlocks (diagonal (fun _ : Unit => a))
        (fun (_ : Unit) j => -‖z j‖) (fun i (_ : Unit) => -‖z i‖) (comparison B) := by
  ext i j
  cases i with
  | inl u =>
    cases j with
    | inl v => cases u; cases v; change (a : ℂ).re = a; rfl
    | inr v => change -‖star (z v)‖ = -‖z v‖; rw [norm_star]
  | inr u =>
    cases j with
    | inl v => rfl
    | inr v =>
      change (if Sum.inr u = (Sum.inr v : Unit ⊕ I) then (B u u).re else -‖B u v‖) = _
      simp only [Sum.inr.injEq]
      rfl

theorem border_comparison_schur {a : ℝ} {z : I → ℂ} {B : Matrix I I ℂ}
    (hA : ComparisonPSD (border a z B)) (ha : 0 < a) :
    (comparison B - vecMulVec (fun i => ‖normalizedBorder a z i‖)
      (fun i => ‖normalizedBorder a z i‖)).PosSemidef := by
  let P : Matrix Unit Unit ℝ := diagonal (fun _ => a)
  let R : Matrix Unit I ℝ := fun _ j => -‖z j‖
  have hP : P.PosDef := PosDef.diagonal (fun _ => ha)
  let := hP.isUnit.invertible
  have hblk : (fromBlocks P R R.conjTranspose (comparison B)).PosSemidef := by
    convert hA.2 using 1
    rw [comparison_border]
    rfl
  have hS := (PosDef.fromBlocks₁₁ R (comparison B) hP).mp hblk
  have he : R.conjTranspose * P⁻¹ * R =
      vecMulVec (fun i => ‖normalizedBorder a z i‖) (fun i => ‖normalizedBorder a z i‖) := by
    let : Invertible (fun _ : Unit => a) :=
      ⟨(fun _ => a⁻¹), by funext u; exact inv_mul_cancel₀ ha.ne',
        by funext u; exact mul_inv_cancel₀ ha.ne'⟩
    have hinv : Ring.inverse (fun _ : Unit => a) = (fun _ => a⁻¹) := by
      rw [Ring.inverse_invertible]
      rfl
    funext i j
    have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    have hs2 := Real.sq_sqrt ha.le
    change (∑ u : Unit, (∑ v : Unit, star (R v i) * P⁻¹ v u) * R u j) = _
    simp only [P, inv_diagonal, R,
      Finset.univ_unique, Finset.sum_singleton, star_trivial, diagonal_apply, hinv, ite_true,
      vecMulVec_apply,
      normalizedBorder, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr ha)]
    field_simp [hs, ha.ne']
    rw [hs2]
    ring
  rw [he] at hS
  exact hS

theorem border_pencil_closure {a : ℝ} {z : I → ℂ} {B : Matrix I I ℂ}
    (hA : ComparisonPSD (border a z B)) (ha : 0 < a) (t : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ComparisonPSD (pencil B (normalizedBorder a z) (t - 1)) := by
  have hB : B.IsHermitian := by
    change (border a z B).submatrix Sum.inr Sum.inr |>.IsHermitian
    exact hA.1.submatrix Sum.inr
  exact pencil_closure hB (normalizedBorder a z) (border_comparison_schur hA ha)
    (t - 1) (abs_le.mpr ⟨by linarith, by linarith⟩)

end ResearchMain.Chollet
