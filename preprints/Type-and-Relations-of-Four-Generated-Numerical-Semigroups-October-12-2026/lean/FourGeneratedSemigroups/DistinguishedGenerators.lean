import FourGeneratedSemigroups.BoundaryRedundancy
import FourGeneratedSemigroups.BoundaryCardinality

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma zero_variable_not_redundant (K : Type*) [Field K] (p : Factorization) (hp2 : 0<p 2) :
    MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∉
      omittedBoundaryIdeal G K p (Finsupp.single 0 1) := by
  intro h
  have hne : Finsupp.single 0 1≠topPower G := by
    intro he
    have hh := congrArg (fun a : Factorization => a 0) he
    simp [topPower] at hh
  have hle := redundant_boundary_ge_replacement G K p _ (zero_variable_mem_boundary G) hne h
  have hh := hle 2
  simp at hh
  omega

lemma distinguished_binomial_not_redundant (K : Type*) [Field K]
    (p : Factorization) (hp : p∈staircase G) :
    MvPolynomial.monomial (topPower G) (1:K)-MvPolynomial.monomial p 1∉
      Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) ''
        (staircaseBoundary G \ {topPower G})) := by
  classical
  intro h
  have hne : topPower G≠p := by
    intro he
    apply (top_power_mem_boundary G).1
    change topPower G∈staircase G
    rw [he]
    exact hp
  have hsupport : p∈(MvPolynomial.monomial (topPower G) (1:K)-MvPolynomial.monomial p 1).support := by
    rw [MvPolynomial.mem_support_iff]
    simp [MvPolynomial.coeff_monomial,hne]
  obtain ⟨b,hb,hbp⟩ := (MvPolynomial.mem_ideal_span_monomial_image.mp h) p hsupport
  exact hb.1.1 (staircase_lower G hp hbp)

end FourGeneratedSemigroups
