import Dowling.JointlessActualCoefficients
import Dowling.DowlingRetainedNontrivialStrict

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical

theorem quadraticWeightedRow_scalar (c : ℝ) (v : ℕ→ℝ) (a : ℝ) (n k : ℕ) :
    quadraticWeightedRow (fun j => c*v j) a n k=c*quadraticWeightedRow v a n k := by
  by_cases hk : k≤n
  · simp only [quadraticWeightedRow,ite_eq_left hk,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  · simp [quadraticWeightedRow,hk]

theorem quadraticWeightedRow_linear (c d : ℝ) (v w : ℕ→ℝ) (a : ℝ) (n k : ℕ) :
    quadraticWeightedRow (fun j => c*v j+d*w j) a n k=
      c*quadraticWeightedRow v a n k+d*quadraticWeightedRow w a n k := by
  by_cases hk : k≤n
  · simp only [quadraticWeightedRow,ite_eq_left hk,Finset.mul_sum,← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  · simp [quadraticWeightedRow,hk]

variable (G : Type*) [Group G] [Fintype G]

theorem fullY_coeff_base_weight (n k : ℕ) :
    ((fullY G n).coeff k : ℝ)=(n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
      quadraticWeightedRow (dowlingBaseWeight (Fintype.card G : ℝ)⁻¹ n)
        ((Fintype.card G : ℝ)⁻¹+1) n k := by
  have ha : (0 : ℝ)<(Fintype.card G : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos (α := G))
  rw [fullY_coeff_real,dowlingScalarCoefficient_raised ha]
  change _=(n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
    quadraticWeightedRow (fun j => (Fintype.card G : ℝ)⁻¹/(n+(Fintype.card G : ℝ)⁻¹)*
      dowlingQuadraticWeight ((n+(Fintype.card G : ℝ)⁻¹)/2) j) _ n k
  rw [quadraticWeightedRow_scalar]
  rfl

variable [Nontrivial G] {n : ℕ}

theorem retained_nontrivial_interpolation (hn : 2≤n) (X : Set (Fin n)) :
    C (n : ℤ)*configurationY (G := G) X=
      C (X.toFinset.card : ℤ)*fullY G n+
      C ((n-X.toFinset.card : ℕ) : ℤ)*configurationY (G := G) (∅ : Set (Fin n)) := by
  rw [retained_nontrivial_identity hn X,jointless_nontrivial_identity hn]
  have hk : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  rw [Nat.cast_sub hk,map_sub]
  ring

/-- The actual retained row is the coupled full/jointless weight mixture;
strictness is not inferred from arbitrary mixtures of log-concave sequences. -/
theorem retained_actual_coeff_raised (hn : 2≤n) (X : Set (Fin n)) (k : ℕ) :
    ((configurationY (G := G) X).coeff k : ℝ)=
      (n.factorial : ℝ)*(Fintype.card G : ℝ)^n*
        quadraticWeightedRow (fun j =>
          (1-((n-X.toFinset.card : ℕ) : ℝ)/n)*dowlingBaseWeight (Fintype.card G : ℝ)⁻¹ n j+
          (((n-X.toFinset.card : ℕ) : ℝ)/n)*jointlessRaisedWeight (Fintype.card G : ℝ)⁻¹ n j)
          ((Fintype.card G : ℝ)⁻¹+1) n k := by
  have h := congrArg (fun p : Polynomial ℤ => (p.coeff k : ℝ)) (retained_nontrivial_interpolation G hn X)
  simp only [coeff_C_mul,coeff_add,Int.cast_mul,Int.cast_add,Int.cast_natCast] at h
  rw [fullY_coeff_base_weight,jointless_actual_coeff G n k hn] at h
  rw [quadraticWeightedRow_linear]
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hk : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  have hc : ((n-X.toFinset.card : ℕ) : ℝ)=(n : ℝ)-X.toFinset.card := Nat.cast_sub hk
  rw [hc] at h ⊢
  apply (mul_left_cancel₀ hn0)
  field_simp at h ⊢
  nlinarith only [h]

end Dowling
