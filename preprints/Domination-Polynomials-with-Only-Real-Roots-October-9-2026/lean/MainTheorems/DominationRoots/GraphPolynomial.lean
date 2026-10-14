import MainTheorems.Domination.Basic
import MainTheorems.DominationRoots.TraceClassification

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V : Type*} [Fintype V]

noncomputable def allDominatingSets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.powerset.filter (Dominates G)

theorem mem_allDominatingSets (G : SimpleGraph V) (S : Finset V) :
    S ∈ allDominatingSets G ↔ Dominates G S := by
  simp [allDominatingSets]

noncomputable def dominationPolynomial (G : SimpleGraph V) : ℤ[X] :=
  ∑ S ∈ allDominatingSets G, X ^ S.card

theorem dominationPolynomial_coeff (G : SimpleGraph V) (k : ℕ) :
    (dominationPolynomial G).coeff k = (dominationCount G k : ℤ) := by
  have hf : (allDominatingSets G).filter (fun S => S.card = k) = dominatingSets G k := by
    ext S
    simp only [Finset.mem_filter, mem_allDominatingSets, mem_dominatingSets]
    exact and_comm
  unfold dominationPolynomial
  rw [finsetSum_coeff]
  simp_rw [coeff_X_pow, eq_comm (a := k)]
  rw [Finset.sum_boole]
  exact_mod_cast congrArg Finset.card hf

theorem dominationPolynomial_natDegree_le (G : SimpleGraph V) :
    (dominationPolynomial G).natDegree ≤ Fintype.card V := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [dominationPolynomial_coeff, dominationCount_above G k hk]
  rfl

theorem dominationPolynomial_natDegree (G : SimpleGraph V) :
    (dominationPolynomial G).natDegree = Fintype.card V := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (dominationPolynomial_natDegree_le G)
  rw [dominationPolynomial_coeff, dominationCount_full]
  norm_num

theorem dominationPolynomial_monic (G : SimpleGraph V) : (dominationPolynomial G).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (Fintype.card V)
    (dominationPolynomial_natDegree_le G)
  rw [dominationPolynomial_coeff, dominationCount_full]
  norm_num

theorem dominationPolynomial_eval_one (G : SimpleGraph V) :
    (dominationPolynomial G).eval 1 = ((allDominatingSets G).card : ℤ) := by
  simp [dominationPolynomial, eval_finsetSum]

end ResearchMain.DominationRoots
