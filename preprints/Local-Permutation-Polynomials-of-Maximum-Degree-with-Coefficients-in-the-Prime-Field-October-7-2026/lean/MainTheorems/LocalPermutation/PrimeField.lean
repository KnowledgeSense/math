import MainTheorems.LocalPermutation.PermutationPairing
import MainTheorems.LocalPermutation.OneVariable

namespace ResearchMain.LocalPermutation

open Classical

variable {K : Type} [Field K] [Fintype K]

def addFunction {n : ℕ} (e : Equiv.Perm K) (f : (Fin n → K) → K) (x : Fin (n + 1) → K) : K :=
  e (f (Fin.tail x) + (x 0)⁻¹)

omit [Fintype K] in
theorem addFunction_localPermutation {n : ℕ} (e : Equiv.Perm K) {f : (Fin n → K) → K}
    (hf : IsLocalPermutation f) : IsLocalPermutation (addFunction e f) := by
  have he : addFunction e f = extendFunction e (fun x => (f x)⁻¹) := by
    funext x
    simp only [addFunction, extendFunction, inv_inv]
  rw [he]
  apply extendFunction_localPermutation
  exact fun i x => inv_bijective.comp (hf i x)

theorem addFunction_moment {n : ℕ} (e : Equiv.Perm K) (f : (Fin n → K) → K) :
    weightedMoment (addFunction e f) = ∑ z : K, e z * inverseKernel f z := by
  have hsum := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => K))
    (fun x => addFunction e f x * ∏ i, x i)
  change (∑ x : K × (Fin n → K), addFunction e f (Fin.cons x.1 x.2) *
    ∏ i, Fin.cons x.1 x.2 i) = _ at hsum
  unfold weightedMoment
  rw [← hsum, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [addFunction, Fin.tail_cons, Fin.cons_zero, Fin.prod_univ_succ, Fin.cons_succ]
  have hs (x : Fin n → K) : (∑ a : K, e (f x + a⁻¹) * (a * ∏ i, x i)) =
      ∑ z : K, e z * ((∏ i, x i) * (z - f x)⁻¹) := by
    have hi := Equiv.sum_comp (Equiv.inv K) (fun a => e (f x + a⁻¹) * a)
    change (∑ a : K, e (f x + (a⁻¹)⁻¹) * a⁻¹) = ∑ a : K, e (f x + a⁻¹) * a at hi
    simp only [inv_inv] at hi
    have ht := Equiv.sum_comp (Equiv.addLeft (f x)) (fun z : K => e z * (z - f x)⁻¹)
    change (∑ a : K, e (f x + a) * (f x + a - f x)⁻¹) = _ at ht
    simp only [add_sub_cancel_left] at ht
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, ← hi, ht, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    ring
  simp_rw [hs]
  rw [Finset.sum_comm]
  unfold inverseKernel
  simp only [Finset.mul_sum]

theorem exists_localPermutation_nonzero_moment (hq : 3 < Fintype.card K) (h2 : (2 : K) ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) : ∃ f : (Fin n → K) → K, IsLocalPermutation f ∧ weightedMoment f ≠ 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨inverseFunction, inverseFunction_localPermutation, ?_⟩
      rw [inverseFunction_moment (by omega)]
      exact neg_ne_zero.mpr one_ne_zero
    · obtain ⟨f, hf, hm⟩ := ih (by omega)
      obtain ⟨e, he⟩ := exists_permutation_pairing (inverseKernel f) (inverseKernel_nonconstant hq h2 hm)
      exact ⟨addFunction e f, addFunction_localPermutation e hf, by rwa [addFunction_moment]⟩

theorem prime_field_maximum_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 3 < p) (hcard : Fintype.card K = p) {n : ℕ} (hn : 1 ≤ n) : HasMaximumDegree K n := by
  have hq : 3 < Fintype.card K := by omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd
  obtain ⟨f, hf, hm⟩ := exists_localPermutation_nonzero_moment hq h2 hn
  apply exists_maximum_degree p (by omega) hf ?_ hm
  intro x
  have hpow (a : K) : a ^ p = a := by rw [← hcard]; exact FiniteField.pow_card a
  simp only [hpow]

end ResearchMain.LocalPermutation
