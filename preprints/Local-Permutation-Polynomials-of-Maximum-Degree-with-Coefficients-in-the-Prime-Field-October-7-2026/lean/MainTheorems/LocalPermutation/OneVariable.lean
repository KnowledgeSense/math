import MainTheorems.LocalPermutation.Moments

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K] [Fintype K]

def inverseFunction (x : Fin 1 → K) : K := (x 0)⁻¹

omit [Fintype K] in
theorem inverseFunction_localPermutation : IsLocalPermutation (inverseFunction (K := K)) := by
  intro i x
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa only [inverseFunction, Function.update_self] using (inv_bijective : Function.Bijective (Inv.inv : K → K))

omit [Fintype K] in
theorem inverseFunction_frobenius (p : ℕ) : FrobeniusEquivariant p (inverseFunction (K := K)) := by
  intro x
  change (x 0 ^ p)⁻¹ = ((x 0)⁻¹) ^ p
  exact (inv_pow (x 0) p).symm

theorem inverseFunction_moment (hq : 2 < Fintype.card K) : weightedMoment (inverseFunction (K := K)) = -1 := by
  unfold weightedMoment inverseFunction
  simp only [Fin.prod_univ_one]
  have he := Equiv.sum_comp (Equiv.funUnique (Fin 1) K) (fun a : K => a⁻¹ * a)
  change (∑ x : Fin 1 → K, (x 0)⁻¹ * x 0) = ∑ a : K, a⁻¹ * a at he
  rw [he]
  have hp (a : K) : a⁻¹ * a = a ^ (Fintype.card K - 1) := by
    rw [← inverse_power hq a, ← pow_succ, show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega]
  simp_rw [hp]
  exact sum_power_last

theorem one_variable_maximum_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 2 < Fintype.card K) : HasMaximumDegree K 1 := by
  apply exists_maximum_degree p hq inverseFunction_localPermutation (inverseFunction_frobenius p)
  rw [inverseFunction_moment hq]
  exact neg_ne_zero.mpr one_ne_zero

end ResearchMain.LocalPermutation
