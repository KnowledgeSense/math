import FourGeneratedSemigroups.SingleRelationInvariants
import Mathlib.Algebra.MonoidAlgebra.Ideal

noncomputable section
namespace FourGeneratedSemigroups

/-- A monomial in a monomial ideal modulo one binomial is divisible by one of
the proposed monomial generators in the actual exponent congruence. -/
theorem monomial_mem_singleRelation_implies (K : Type*) [Field K]
    (A : ℕ) (p a : Factorization) (B : Set Factorization)
    (h : MvPolynomial.monomial a (1:K) ∈
      Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) '' B) ⊔
      Ideal.span {MvPolynomial.monomial (Finsupp.single 3 A) 1-MvPolynomial.monomial p 1}) :
    ∃b∈B, ∃r : Factorization, topRelation A p a (r+b) := by
  classical
  let C := topRelation A p
  let J : Ideal (AddMonoidAlgebra K C.Quotient) :=
    Ideal.span (AddMonoidAlgebra.of' K C.Quotient '' (C.mk' '' B))
  have hle : Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) '' B) ⊔
      Ideal.span {MvPolynomial.monomial (Finsupp.single 3 A) 1-MvPolynomial.monomial p 1}
      ≤ J.comap (congruenceAlgebraMap K C) := by
    apply sup_le
    · rw [Ideal.span_le]
      rintro f ⟨b,hb,rfl⟩
      change congruenceAlgebraMap K C (MvPolynomial.monomial b 1)∈J
      rw [congruenceAlgebraMap_monomial]
      exact Ideal.subset_span ⟨C.mk' b,⟨b,hb,rfl⟩,rfl⟩
    · rw [Ideal.span_le]
      rintro f rfl
      change congruenceAlgebraMap K C (_-_)∈J
      have he : C.mk' (Finsupp.single 3 A)=C.mk' p :=
        C.eq.mpr (AddConGen.Rel.of _ _ ⟨rfl,rfl⟩)
      simp [he]
  have hh := hle h
  change congruenceAlgebraMap K C (MvPolynomial.monomial a 1)∈J at hh
  rw [congruenceAlgebraMap_monomial] at hh
  obtain ⟨b,⟨b,hb,rfl⟩,d,hd⟩ :=
    (AddMonoidAlgebra.mem_ideal_span_of'_image.mp hh) (C.mk' a) (by simp)
  obtain ⟨r,hr⟩ := C.mk'_surjective d
  refine ⟨b,hb,r,C.eq.mp ?_⟩
  change C.mk' a=C.mk' (r+b)
  rw [map_add,hr]
  exact hd

end FourGeneratedSemigroups
