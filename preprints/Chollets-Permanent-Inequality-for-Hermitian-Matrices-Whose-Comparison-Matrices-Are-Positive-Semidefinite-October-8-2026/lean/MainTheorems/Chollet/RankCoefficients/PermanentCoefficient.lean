import MainTheorems.Chollet.RankCoefficients.Coefficient
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Fintype.EquivFin

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

open MvPolynomial

variable {I J : Type*} [Fintype I] [Fintype J] [instI : DecidableEq I] [DecidableEq J]

def selectionExponent (f : J → I) : I →₀ ℕ := ∑ j, Finsupp.single (f j) 1

def columnProduct (Q : Matrix I J ℂ) : MvPolynomial I ℂ :=
  ∏ j, ∑ i, C (Q i j) * X i

omit instI in
theorem columnProduct_expand (Q : Matrix I J ℂ) :
    columnProduct Q = ∑ f : J → I,
      MvPolynomial.monomial (selectionExponent f) (∏ j, Q (f j) j) := by
  unfold columnProduct selectionExponent
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [X, C_mul_monomial, mul_one, ← monomial_sum_prod]

omit [Fintype J] [DecidableEq J] in
theorem selectionExponent_full_iff (f : I → I) :
    selectionExponent f = exponent (Finset.univ : Finset I) ↔ Function.Bijective f := by
  constructor
  · intro h
    have hs : Function.Surjective f := by
      intro i
      by_contra! hn
      have hz : selectionExponent f i = 0 := by
        simp [selectionExponent, Finsupp.finsetSum_apply, hn]
      have hi := congrArg (fun d : I →₀ ℕ => d i) h
      rw [hz, exponent_apply, ite_eq_left (Finset.mem_univ i)] at hi
      omega
    exact (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs, rfl⟩
  · intro hf
    let e : Equiv.Perm I := Equiv.ofBijective f hf
    unfold selectionExponent exponent
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)

omit [Fintype J] [DecidableEq J] in
theorem permanent_coefficient (Q : Matrix I I ℂ) :
    (columnProduct Q).coeff (exponent (Finset.univ : Finset I)) = Q.permanent := by
  classical
  let : DecidableEq I := instI
  rw [columnProduct_expand, coeff_sum]
  simp only [coeff_monomial, selectionExponent_full_iff]
  rw [← Finset.sum_filter]
  unfold Matrix.permanent
  apply Finset.sum_bij
    (fun f hf => Equiv.ofBijective f (Finset.mem_filter.mp hf).2)
  · intro f hf
    exact Finset.mem_univ _
  · intro f hf g hg hfg
    exact congrArg (fun e : Equiv.Perm I => (e : I → I)) hfg
  · intro e _
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.bijective⟩,
      Equiv.ext (fun _ => rfl)⟩
  · intro f _
    rfl

end ResearchMain.Chollet.RankCoefficients


