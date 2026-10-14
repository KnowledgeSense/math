import FourGeneratedSemigroups.Definitions
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section
namespace FourGeneratedSemigroups

/-- The actual monomial-curve map to the polynomial ring over an arbitrary field. -/
def curveMap (K : Type*) [Field K] (d : Fin 4 → ℕ) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval (fun i => Polynomial.X^(d i))

/-- The actual defining ideal of the four-generated monomial curve. -/
def definingIdeal (K : Type*) [Field K] (d : Fin 4 → ℕ) :
    Ideal (MvPolynomial (Fin 4) K) := RingHom.ker (curveMap K d)

/-- The semigroup ring as the image of its four monomial generators. -/
def semigroupRing (K : Type*) [Field K] (d : Fin 4 → ℕ) :
    Subalgebra K (Polynomial K) := (curveMap K d).range

@[simp] theorem curveMap_monomial (K : Type*) [Field K] (d : Fin 4 → ℕ)
    (c : Factorization) :
    curveMap K d (MvPolynomial.monomial c 1) = Polynomial.X^(factorizationMap d c) := by
  classical
  rw [curveMap,MvPolynomial.aeval_monomial]
  simp only [map_one,one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)

/-- Polynomial binomial relations agree exactly with equal semigroup factorizations. -/
theorem binomial_mem_definingIdeal_iff (K : Type*) [Field K] (d : Fin 4 → ℕ)
    (a b : Factorization) :
    MvPolynomial.monomial a (1 : K) - MvPolynomial.monomial b 1 ∈ definingIdeal K d ↔
      factorizationMap d a = factorizationMap d b := by
  rw [definingIdeal,RingHom.mem_ker,map_sub,sub_eq_zero,curveMap_monomial,curveMap_monomial]
  constructor
  · intro h
    have hh := congrArg Polynomial.natDegree h
    simpa using hh
  · intro h
    rw [h]

/-- The quotient is isomorphic to the actual semigroup-ring image. -/
noncomputable def definingQuotientEquivSemigroupRing (K : Type*) [Field K] (d : Fin 4 → ℕ) :
    (MvPolynomial (Fin 4) K ⧸ definingIdeal K d) ≃ₐ[K] semigroupRing K d :=
  Ideal.quotientKerEquivRange (curveMap K d)

end FourGeneratedSemigroups
