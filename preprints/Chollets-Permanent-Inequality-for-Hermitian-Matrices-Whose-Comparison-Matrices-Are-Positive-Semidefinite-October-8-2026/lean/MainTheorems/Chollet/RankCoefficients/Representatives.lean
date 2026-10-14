import MainTheorems.Chollet.RankCoefficients.LinearAction
import MainTheorems.Chollet.RankCoefficients.RootStates
import MainTheorems.Chollet.RankCoefficients.QuotientPermanent

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

def RootedPartition.representative (p : RootedPartition I) (t : p.parts) : I :=
  Classical.choose (p.nonempty t.val t.property)

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.representative_mem (p : RootedPartition I) (t : p.parts) :
    p.representative t ∈ t.val := Classical.choose_spec (p.nonempty t.val t.property)

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.representative_phase_ne (p : RootedPartition I) (t : p.parts) :
    p.phase t.val (p.representative t) ≠ 0 := by
  intro h
  have hu := p.unit t.val t.property (p.representative t) (p.representative_mem t)
  rw [h, norm_zero] at hu
  norm_num at hu

def RootedPartition.representativeVariable (p : RootedPartition I) (t : p.parts) : SquareFree I :=
  scalar ((p.phase t.val (p.representative t))⁻¹) * rowVariable (p.representative t)

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.representativeVariable_sq (p : RootedPartition I) (t : p.parts) :
    p.representativeVariable t ^ 2 = 0 := by
  rw [RootedPartition.representativeVariable, mul_pow, variable_sq, mul_zero]

omit [Fintype I] in
theorem RootedPartition.rooted_representative (p : RootedPartition I) (t : p.parts) :
    rooted t.val (p.phase t.val) * p.representativeVariable t = monomial t.val := by
  unfold RootedPartition.representativeVariable
  calc
    rooted t.val (p.phase t.val) *
        (scalar ((p.phase t.val (p.representative t))⁻¹) * rowVariable (p.representative t)) =
      scalar ((p.phase t.val (p.representative t))⁻¹) *
        (rowVariable (p.representative t) * rooted t.val (p.phase t.val)) := by ring
    _ = _ := by
      rw [variable_rooted t.val (p.phase t.val) (p.representative_mem t), ← mul_assoc,
        ← scalar_mul, inv_mul_cancel₀ (p.representative_phase_ne t), scalar_one, one_mul]

omit [Fintype I] in
theorem RootedPartition.polynomial_representative (p : RootedPartition I) (t : p.parts) :
    p.polynomial * p.representativeVariable t = p.closedPolynomial t.val := by
  unfold RootedPartition.representativeVariable
  calc
    p.polynomial *
        (scalar ((p.phase t.val (p.representative t))⁻¹) * rowVariable (p.representative t)) =
      scalar ((p.phase t.val (p.representative t))⁻¹) *
        (rowVariable (p.representative t) * p.polynomial) := by ring
    _ = _ := by
      rw [p.variable_open t.val t.property (p.representative t) (p.representative_mem t),
        ← mul_assoc, ← scalar_mul, inv_mul_cancel₀ (p.representative_phase_ne t),
        scalar_one, one_mul]

def RootedPartition.contraction (p : RootedPartition I) (x : I → ℂ) (t : p.parts) : ℂ :=
  ∑ i ∈ t.val, p.phase t.val i * x i

theorem RootedPartition.linear_representatives (p : RootedPartition I) (x : I → ℂ) :
    p.polynomial * linearForm x = p.polynomial *
      ∑ t : p.parts, scalar (p.contraction x t) * p.representativeVariable t := by
  rw [mul_comm p.polynomial (linearForm x), p.linear_action x, Finset.mul_sum]
  have he : (∑ t : p.parts, p.polynomial *
      (scalar (p.contraction x t) * p.representativeVariable t)) =
      ∑ t : p.parts, scalar (p.contraction x t) * p.closedPolynomial t.val := by
    apply Finset.sum_congr rfl
    intro t _
    calc
      p.polynomial * (scalar (p.contraction x t) * p.representativeVariable t) =
        scalar (p.contraction x t) * (p.polynomial * p.representativeVariable t) := by ring
      _ = _ := by rw [p.polynomial_representative t]
  rw [he]
  change (∑ s ∈ p.parts, scalar (∑ i ∈ s, p.phase s i * x i) * p.closedPolynomial s) =
    ∑ t : p.parts, scalar (∑ i ∈ t.val, p.phase t.val i * x i) * p.closedPolynomial t.val
  exact Finset.sum_subtype p.parts (fun _ => Iff.rfl) _

theorem RootedPartition.product_representatives (p : RootedPartition I) :
    p.polynomial * (∏ t : p.parts, p.representativeVariable t) =
      monomial (Finset.univ : Finset I) := by
  have hp : (∏ t : p.parts, rooted t.val (p.phase t.val)) =
      ∏ t ∈ p.parts, rooted t (p.phase t) := by
    exact (Finset.prod_subtype p.parts (fun _ => Iff.rfl)
      (fun t => rooted t (p.phase t))).symm
  calc
    p.polynomial * (∏ t : p.parts, p.representativeVariable t) =
        monomial p.closed * ∏ t : p.parts,
          rooted t.val (p.phase t.val) * p.representativeVariable t := by
      rw [Finset.prod_mul_distrib, hp]
      unfold RootedPartition.polynomial
      ring
    _ = monomial p.closed * ∏ t : p.parts, monomial t.val := by
      congr 1
      apply Finset.prod_congr rfl
      intro t _
      exact p.rooted_representative t
    _ = p.statePolynomial p.parts := by
      unfold RootedPartition.statePolynomial
      congr 1
      rw [← Finset.prod_subtype p.parts (fun _ => Iff.rfl) monomial]
      apply Finset.prod_congr rfl
      intro t ht
      rw [RootedPartition.stateFactor, ite_eq_left ht]
    _ = _ := p.state_all

def RootedPartition.evaluateRepresentatives (p : RootedPartition I) :
    MvPolynomial p.parts ℂ →+* SquareFree I :=
  MvPolynomial.eval₂Hom scalarHom p.representativeVariable

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.squareIdeal_evaluate_zero (p : RootedPartition I)
    (P : MvPolynomial p.parts ℂ) (hP : P ∈ squareIdeal p.parts) :
    p.evaluateRepresentatives P = 0 := by
  have hle : squareIdeal p.parts ≤ RingHom.ker p.evaluateRepresentatives := by
    apply Ideal.span_le.mpr
    rintro P ⟨t, rfl⟩
    change p.evaluateRepresentatives (MvPolynomial.X t ^ 2) = 0
    simp only [RootedPartition.evaluateRepresentatives, map_pow, MvPolynomial.eval₂Hom_X']
    exact p.representativeVariable_sq t
  exact hle hP

def RootedPartition.representativeHom (p : RootedPartition I) :
    SquareFree p.parts →+* SquareFree I :=
  Ideal.Quotient.lift (squareIdeal p.parts) p.evaluateRepresentatives
    p.squareIdeal_evaluate_zero

end ResearchMain.Chollet.RankCoefficients

