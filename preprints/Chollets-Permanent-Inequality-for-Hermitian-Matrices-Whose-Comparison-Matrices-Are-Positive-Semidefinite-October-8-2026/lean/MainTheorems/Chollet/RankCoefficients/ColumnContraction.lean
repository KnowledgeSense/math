import MainTheorems.Chollet.RankCoefficients.Representatives

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

theorem multiplication_transfer_prod {R J : Type*} [CommRing R]
    (s : Finset J) (p : R) (f g : J → R) (h : ∀ j ∈ s, p * f j = p * g j) :
    p * (∏ j ∈ s, f j) = p * (∏ j ∈ s, g j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert j s hjs ih =>
    intro h
    rw [Finset.prod_insert hjs, Finset.prod_insert hjs]
    have hj := h j (Finset.mem_insert_self _ _)
    have hs := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    calc
      p * (f j * ∏ k ∈ s, f k) = (p * f j) * ∏ k ∈ s, f k := by ring
      _ = g j * (p * ∏ k ∈ s, f k) := by rw [hj]; ring
      _ = p * (g j * ∏ k ∈ s, g k) := by rw [hs]; ring

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.representativeHom_scalar (p : RootedPartition I) (c : ℂ) :
    p.representativeHom (scalar c) = scalar c := by
  change p.evaluateRepresentatives (MvPolynomial.C c) = scalar c
  simp only [RootedPartition.evaluateRepresentatives, MvPolynomial.eval₂Hom_C]
  rfl

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.representativeHom_variable (p : RootedPartition I) (t : p.parts) :
    p.representativeHom (rowVariable t) = p.representativeVariable t := by
  change p.evaluateRepresentatives (MvPolynomial.X t) = _
  simp only [RootedPartition.evaluateRepresentatives, MvPolynomial.eval₂Hom_X']

omit [Fintype I] [DecidableEq I] in
theorem RootedPartition.representativeHom_full (p : RootedPartition I) :
    p.representativeHom (monomial (Finset.univ : Finset p.parts)) =
      ∏ t : p.parts, p.representativeVariable t := by
  simp only [monomial, map_prod, p.representativeHom_variable]

def RootedPartition.contractionMatrix (p : RootedPartition I) (Q : Matrix I p.parts ℂ) :
    Matrix p.parts p.parts ℂ := fun t j => p.contraction (fun i => Q i j) t

theorem RootedPartition.column_contraction (p : RootedPartition I) (Q : Matrix I p.parts ℂ) :
    p.polynomial * (∏ j : p.parts, linearForm (fun i => Q i j)) =
      scalar (p.contractionMatrix Q).permanent * monomial (Finset.univ : Finset I) := by
  let C := p.contractionMatrix Q
  let f : p.parts → SquareFree I := fun j => linearForm (fun i => Q i j)
  let g : p.parts → SquareFree I := fun j =>
    ∑ t : p.parts, scalar (C t j) * p.representativeVariable t
  have hf : ∀ j ∈ (Finset.univ : Finset p.parts), p.polynomial * f j = p.polynomial * g j := by
    intro j _
    exact p.linear_representatives (fun i => Q i j)
  have ht := multiplication_transfer_prod Finset.univ p.polynomial f g hf
  have he : p.representativeHom (Ideal.Quotient.mk (squareIdeal p.parts) (columnProduct C)) =
      ∏ j : p.parts, g j := by
    change p.evaluateRepresentatives (columnProduct C) = _
    simp only [columnProduct, map_prod, map_sum, map_mul,
      RootedPartition.evaluateRepresentatives, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X']
    rfl
  have hq := congrArg p.representativeHom (quotient_columnProduct C)
  rw [he, map_mul, p.representativeHom_scalar, p.representativeHom_full] at hq
  calc
    p.polynomial * (∏ j : p.parts, linearForm (fun i => Q i j)) =
        p.polynomial * ∏ j : p.parts, g j := ht
    _ = p.polynomial * (scalar C.permanent * ∏ t : p.parts, p.representativeVariable t) := by rw [hq]
    _ = scalar C.permanent * monomial (Finset.univ : Finset I) := by
      rw [mul_left_comm, p.product_representatives]

end ResearchMain.Chollet.RankCoefficients
