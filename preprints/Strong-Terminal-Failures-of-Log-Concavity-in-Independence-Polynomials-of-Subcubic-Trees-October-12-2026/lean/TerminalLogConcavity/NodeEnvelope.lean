import TerminalLogConcavity.CoefficientOrder

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

theorem node_envelope_step {A₁ A₂ B₁ B₂ P₁ P₂ : ℕ[X]} {d₁ d₂ : ℕ}
    (hA₁ : CoeffLE A₁ P₁) (hA₂ : CoeffLE A₂ P₂)
    (hB₁ : CoeffLE B₁ (C d₁ * P₁)) (hB₂ : CoeffLE B₂ (C d₂ * P₂)) :
    let d := (1 + d₁) * (1 + d₂)
    let P := P₁ * P₂ * (1 + C d * X)
    CoeffLE (A₁ * A₂ + X * (A₁ + B₁) * (A₂ + B₂)) P ∧
      CoeffLE ((A₁ + B₁) * (A₂ + B₂)) (C d * P) := by
  dsimp
  have h₁ : CoeffLE (A₁ + B₁) (C (1 + d₁) * P₁) := by
    convert hA₁.add hB₁ using 1 ; simp only [map_add, map_one] ; ring
  have h₂ : CoeffLE (A₂ + B₂) (C (1 + d₂) * P₂) := by
    convert hA₂.add hB₂ using 1 ; simp only [map_add, map_one] ; ring
  have hprod : CoeffLE ((A₁ + B₁) * (A₂ + B₂))
      (C ((1 + d₁) * (1 + d₂)) * (P₁ * P₂)) := by
    convert h₁.mul h₂ using 1 ; simp only [map_mul] ; ring
  constructor
  · have h := (hA₁.mul hA₂).add ((CoeffLE.refl X).mul hprod)
    convert h using 1 <;> ring
  · exact hprod.trans (by
      convert CoeffLE.le_mul_one_add
        (C ((1 + d₁) * (1 + d₂)) * (P₁ * P₂))
        (C ((1 + d₁) * (1 + d₂)) * X) using 1 ; ring)

end TerminalLogConcavity
