import MainTheorems.PreorderGamma.SimplicialRealization.RadialCones
import MainTheorems.PreorderGamma.SimplicialRealization.CoarseConeLattice
import MainTheorems.PreorderGamma.SimplicialRealization.RootProjectionFibers

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

abbrev BoundaryFaceIndex (height : QuotientIndex E → ℝ) :=
  {s : Finset (QuotientIndex E) // s ∈ boundaryVertexFaces height}

abbrev BoundaryCoefficientPoints (height : QuotientIndex E → ℝ) (t : ℕ) :=
  Σ s : BoundaryFaceIndex height, PositiveCoefficients s.val t

noncomputable def boundaryCoefficientPoint (height : QuotientIndex E → ℝ) (t : ℕ) :
    BoundaryCoefficientPoints height t → QuotientPoints (E := E) t :=
  fun p => ⟨integralCombination p.1.val p.2.val,
    integralCombination_quotientIntegerPoint p.1.val t p.2.val p.2.property.2⟩

theorem integralCombination_in_open_cone (s : Finset (QuotientIndex E))
    (t : ℕ) (c : PositiveCoefficients s t) :
    InOpenBoundaryCone s (fun i => (integralCombination s c.val i : ℝ)) := by
  refine ⟨fun v => (c.val v : ℝ), ?_, (integralCombination_cast s c.val).symm⟩
  intro v
  change (0 : ℝ) < (c.val v : ℝ)
  exact_mod_cast c.property.1 v

theorem boundaryCoefficientPoint_injective (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height) (t : ℕ) :
    Function.Injective (boundaryCoefficientPoint height t) := by
  rintro ⟨s, c⟩ ⟨r, d⟩ h
  have hcomb : integralCombination s.val c.val = integralCombination r.val d.val :=
    congrArg Subtype.val h
  have hcast := congrArg (fun z : E → ℤ => fun i => (z i : ℝ)) hcomb
  have hface : s.val = r.val := by
    apply open_boundary_cones_unique height hheight s.val r.val s.property r.property
      (fun i => (integralCombination s.val c.val i : ℝ))
    · exact integralCombination_in_open_cone s.val t c
    · rw [hcast]
      exact integralCombination_in_open_cone r.val t d
  have hsr : s = r := Subtype.ext hface
  cases hsr
  have hcd : c = d := by
    apply Subtype.ext
    exact integralCombination_injective s.val
      (boundary_face_original_linearIndependent height hheight hsimp s.val s.property) hcomb
  cases hcd
  rfl

theorem boundaryCoefficientPoint_surjective (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (hcoarse : ∀ s ∈ boundaryVertexFaces height, IsCoarseFace s) (t : ℕ) :
    Function.Surjective (boundaryCoefficientPoint height t) := by
  intro z
  obtain ⟨s, hs, c, hc, hsum⟩ := every_point_in_open_boundary_cone height hheight hsimp
    (fun i => (z.val i : ℝ))
  obtain ⟨a, ha, haz⟩ := boundary_positive_coordinates_integral height hheight hsimp
    s hs z.val c hc hsum
  have hbound : (∑ v, a v) ≤ t := by
    apply coarseCombination_mass_le s (hcoarse s hs) t a
    rw [haz]
    exact z.property
  refine ⟨⟨⟨s, hs⟩, ⟨a, fun v => (ha v).1, hbound⟩⟩, ?_⟩
  exact Subtype.ext haz

noncomputable def boundaryCoefficientEquiv (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (hcoarse : ∀ s ∈ boundaryVertexFaces height, IsCoarseFace s) (t : ℕ) :
    BoundaryCoefficientPoints height t ≃ QuotientPoints (E := E) t :=
  Equiv.ofBijective (boundaryCoefficientPoint height t)
    ⟨boundaryCoefficientPoint_injective height hheight hsimp t,
      boundaryCoefficientPoint_surjective height hheight hsimp hcoarse t⟩

theorem quotientLatticeCount_boundary_faces (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (hcoarse : ∀ s ∈ boundaryVertexFaces height, IsCoarseFace s) (t : ℕ) :
    quotientLatticeCount (E := E) t =
      ∑ s ∈ boundaryVertexFaces height, Nat.choose t s.card := by
  classical
  calc
    _ = Nat.card (BoundaryCoefficientPoints height t) :=
      (Nat.card_congr (boundaryCoefficientEquiv height hheight hsimp hcoarse t)).symm
    _ = ∑ s : BoundaryFaceIndex height, Nat.card (PositiveCoefficients s.val t) := Nat.card_sigma
    _ = ∑ s ∈ boundaryVertexFaces height, Nat.choose t s.card := by
      simp only [positiveCoefficients_count, Fintype.card_coe]
      rw [Finset.sum_coe_sort (boundaryVertexFaces height) (fun s => Nat.choose t s.card)]

end ResearchMain.PreorderGamma.SimplicialRealization
