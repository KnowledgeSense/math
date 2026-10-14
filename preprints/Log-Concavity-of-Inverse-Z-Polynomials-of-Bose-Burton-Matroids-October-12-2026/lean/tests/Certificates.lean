import BoseBurton

noncomputable section
open BoseBurton Module Polynomial
variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

-- Whole original theorem, with no extra finiteness or invariant hypotheses.
example (W : Submodule K V) (hs : 1 ≤ finrank K W) (h : finrank K W < finrank K V) :=
  bose_burton_inverseZ_main W hs h

example (W : Submodule K V) (h : finrank K W < finrank K V) (k : ℕ) :=
  boseBurtonY_coefficient_formula W h k

example (W : Submodule K V) (h : finrank K W < finrank K V) (k : ℕ)
    (hk : finrank K V < k) : (boseBurtonY W).coeff k = 0 :=
  boseBurtonY_coeff_above W h k hk

example (W : Submodule K V) (h : finrank K W < finrank K V) :=
  boseBurtonY_natDegree W h

example (W : Submodule K V) (h : finrank K W < finrank K V) :
    0 < (boseBurtonY W).coeff 0 := boseBurtonY_coeff_positive W h 0 (Nat.zero_le _)

example (W : Submodule K V) (h : finrank K W < finrank K V) :
    0 < (boseBurtonY W).coeff (finrank K V) := boseBurtonY_coeff_positive W h _ le_rfl

-- Rank two, including the smallest field, lies within the same actual-object theorem.
example (W : Submodule K V) (hr : finrank K V = 2) (hs : finrank K W = 1) :
    (boseBurtonY W).coeff 0 * (boseBurtonY W).coeff 2 < ((boseBurtonY W).coeff 1)^2 := by
  simpa using boseBurtonY_strict_logConcave W (by omega) (by omega) 1 (by omega) (by omega)

-- All affine geometries (deleted hyperplanes) and one-point deletions.
example (W : Submodule K V) (hr : 2 ≤ finrank K V)
    (hs : finrank K W + 1 = finrank K V) :=
  bose_burton_inverseZ_main W (by omega) (by omega)

example (W : Submodule K V) (hr : 2 ≤ finrank K V) (hs : finrank K W = 1) :=
  bose_burton_inverseZ_main W (by omega) (by omega)

section FiniteModel
variable [Finite V]
example (W : Submodule K V) (hW : W ≠ ⊤) := actual_inverseZ_eq_spanY W hW
example (W : Submodule K V) (U : Submodule K V) (hU : ¬ U ≤ W) := pointsIn_span W U hU
example (W : Submodule K V) := flatSpanOrderIso W
example (k : ℕ) := subspace_count_gaussian_all K V k
example := projectiveP_eq_one K V
example := projectiveY_eq_projectiveRow K V
example (W : Submodule K V) (hW : W ≠ ⊤) := actual_inverseZ_correction W hW
end FiniteModel
