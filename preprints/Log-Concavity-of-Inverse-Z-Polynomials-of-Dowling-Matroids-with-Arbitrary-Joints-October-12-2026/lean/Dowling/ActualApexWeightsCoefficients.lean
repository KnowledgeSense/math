import Dowling.ActualApexWeightsCombination

noncomputable section
namespace Dowling
open Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Subsingleton G] {n : ℕ}

/-- The positive raised weights are the literal coefficients of the actual
partial-apex matroid, with the full factorial normalization retained. -/
theorem apex_actual_coeff_raised (hn : 2≤n) (X : Set (Fin n)) (hX : X.Nonempty) (k : ℕ) :
    ((configurationY (G := G) X).coeff k : ℝ)=
      (n.factorial : ℝ)*quadraticWeightedRow (apexRaisedWeight n X.toFinset.card) 2 n k := by
  have h := congrArg (fun p : Polynomial ℤ => (p.coeff k : ℝ))
    (apex_positive_decomposition_cleared (G := G) hn X hX)
  simp only [coeff_C_mul,coeff_sub,coeff_add,Int.cast_mul,Int.cast_sub,Int.cast_add,Int.cast_natCast] at h
  rw [apex_fullY_coeff,apex_missing_coeff,apex_missing_coeff] at h
  have hr : quadraticWeightedRow (apexRaisedWeight n X.toFinset.card) 2 n k=
      (X.toFinset.card : ℝ)/n*quadraticWeightedRow (dowlingBaseWeight 1 n) 2 n k+
      (((n-X.toFinset.card : ℕ) : ℝ)/n)*quadraticWeightedRow (apexMissingWeight n n) 2 n k-
      quadraticWeightedRow (apexMissingWeight n (n-X.toFinset.card)) 2 n k := by
    calc
      _ = quadraticWeightedRow (fun j =>
          1*((X.toFinset.card : ℝ)/n*dowlingBaseWeight 1 n j+
            (((n-X.toFinset.card : ℕ) : ℝ)/n)*apexMissingWeight n n j)+
          (-1)*apexMissingWeight n (n-X.toFinset.card) j) 2 n k := by
        apply quadraticWeightedRow_congr_support
        intro j hj
        rw [apexRaisedWeight_combination n X.toFinset.card j hj]
        ring
      _ = _ := by rw [quadraticWeightedRow_linear,quadraticWeightedRow_linear]; ring
  rw [hr]
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  apply mul_left_cancel₀ hn0
  field_simp
  nlinarith only [h]

end Dowling
