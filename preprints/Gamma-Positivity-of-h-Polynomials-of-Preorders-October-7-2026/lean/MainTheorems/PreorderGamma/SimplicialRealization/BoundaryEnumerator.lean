import MainTheorems.PreorderGamma.SimplicialRealization.ConePartition
import MainTheorems.PreorderGamma.SimplicialRealization.QuotientSeries
import MainTheorems.PreorderGamma.ConeGeneratingFunctions

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem quotientEhrhartSeries_boundary_faces (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (hcoarse : ∀ s ∈ boundaryVertexFaces height, IsCoarseFace s) :
    quotientEhrhartSeries (E := E) = coneFaceSeries (boundaryVertexFaces height) Finset.card := by
  ext t
  rw [quotientEhrhartSeries_coeff, quotientLatticeCount_boundary_faces
    height hheight hsimp hcoarse t, coneFaceSeries_coeff, Nat.cast_sum]

theorem boundaryHPolynomial_map (height : QuotientIndex E → ℝ) :
    (boundaryHPolynomial height).map (Int.castRingHom ℚ) =
      coneFaceNumerator (Fintype.card E) (boundaryVertexFaces height) Finset.card := by
  classical
  simp only [boundaryHPolynomial, coneFaceNumerator, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X]

theorem actual_boundaryHPolynomial (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (hcoarse : ∀ s ∈ boundaryVertexFaces height, IsCoarseFace s) :
    boundaryHPolynomial height = (supportPolynomial (E := E)).map (Nat.castRingHom ℤ) := by
  have hseries := quotient_ehrhart_numerator (E := E)
  rw [quotientEhrhartSeries_boundary_faces height hheight hsimp hcoarse,
    coneFaceSeries_numerator (Fintype.card E) (boundaryVertexFaces height) Finset.card
      (fun s hs => boundary_face_card_le_dimension height hheight hsimp s hs),
    ← boundaryHPolynomial_map] at hseries
  have hpoly : (boundaryHPolynomial height).map (Int.castRingHom ℚ) =
      (supportPolynomial (E := E)).map (Nat.castRingHom ℚ) :=
    Polynomial.coe_injective ℚ hseries
  apply Polynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
  calc
    _ = (supportPolynomial (E := E)).map (Nat.castRingHom ℚ) := hpoly
    _ = ((supportPolynomial (E := E)).map (Nat.castRingHom ℤ)).map (Int.castRingHom ℚ) := by
      ext k
      simp [Polynomial.coeff_map]

theorem preorder_actual_simplicial_realization :
    ∃ height : QuotientIndex E → ℝ, (∀ v, 0 < height v) ∧
      Module.finrank ℝ (affineSpan ℝ (projectivePolytope height)).direction = Fintype.card E ∧
      HasSimplicialBoundary height ∧
      boundaryHPolynomial height = (supportPolynomial (E := E)).map (Nat.castRingHom ℤ) := by
  obtain ⟨height, hheight, hsimp, hcoarse⟩ := exists_simplicial_coarse_height (E := E)
  exact ⟨height, hheight, projectivePolytope_dimension height hheight, hsimp,
    actual_boundaryHPolynomial height hheight hsimp hcoarse⟩

end ResearchMain.PreorderGamma.SimplicialRealization
