import MainTheorems.DominationRoots.IntegerQuadratic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace ResearchMain.DominationRoots

open Polynomial

noncomputable def realPolynomial (f : ℤ[X]) : ℝ[X] := f.map (Int.castRingHom ℝ)

noncomputable def realRoots (f : ℤ[X]) : Multiset ℝ := (realPolynomial f).roots

noncomputable def rootTrace (f : ℤ[X]) : ℝ :=
  ((realRoots f).map (fun x => x ^ 2 - x)).sum

def TotallyPositive (f : ℤ[X]) : Prop :=
  (realPolynomial f).Splits ∧ ∀ x ∈ realRoots f, 0 < x ∧ x ≠ 1

noncomputable def auxiliaryPolynomial : ℤ[X] :=
  X * (X - 1) ^ 2 * (X - C 2) * quadraticPolynomial

theorem auxiliaryPolynomial_eval (x : ℝ) :
    (realPolynomial auxiliaryPolynomial).eval x = auxiliaryQ x := by
  norm_num [realPolynomial, auxiliaryPolynomial, quadraticPolynomial, auxiliaryQ,
    quadratic, map_ofNat]

theorem realRoots_card {f : ℤ[X]} (hf : (realPolynomial f).Splits) :
    (realRoots f).card = f.natDegree := by
  rw [realRoots, ← hf.natDegree_eq_card_roots]
  exact natDegree_map_eq_of_injective Int.cast_injective f

theorem resultant_product {f : ℤ[X]} (hm : f.Monic) (hf : (realPolynomial f).Splits) :
    (f.resultant auxiliaryPolynomial : ℝ) = ((realRoots f).map auxiliaryQ).prod := by
  let φ : ℤ →+* ℝ := Int.castRingHom ℝ
  change φ (f.resultant auxiliaryPolynomial) = _
  rw [← resultant_map_map]
  have hdegree : f.natDegree = (f.map φ).natDegree :=
    (natDegree_map_eq_of_injective Int.cast_injective f).symm
  rw [hdegree, resultant_eq_prod_eval (f.map φ) (auxiliaryPolynomial.map φ)
    auxiliaryPolynomial.natDegree natDegree_map_le hf,
    (hm.map φ).leadingCoeff, one_pow, one_mul]
  congr 1
  exact Multiset.map_congr rfl (fun x _ => auxiliaryPolynomial_eval x)

theorem log_abs_int_nonnegative {z : ℤ} (hz : z ≠ 0) : 0 ≤ Real.log |(z : ℝ)| := by
  apply Real.log_nonneg
  by_cases hpos : 0 < z
  · rw [abs_of_pos (by exact_mod_cast hpos)]
    exact_mod_cast (show 1 ≤ z by omega)
  · rw [abs_of_neg (by exact_mod_cast (show z < 0 by omega))]
    exact_mod_cast (show 1 ≤ -z by omega)

theorem root_log_sum_nonnegative {f : ℤ[X]} (hm : f.Monic)
    (hf : (realPolynomial f).Splits)
    (hQ : ∀ x ∈ realRoots f, auxiliaryQ x ≠ 0) :
    0 ≤ ((realRoots f).map (fun x => Real.log |auxiliaryQ x|)).sum := by
  have hprod : ((realRoots f).map auxiliaryQ).prod ≠ 0 := by
    generalize realRoots f = s at hQ ⊢
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact mul_ne_zero (hQ x (by simp)) (ih (fun y hy => hQ y (by simp [hy])))
  have hres := resultant_product hm hf
  have hz : f.resultant auxiliaryPolynomial ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hres
    exact hprod hres.symm
  have hlog := log_abs_int_nonnegative hz
  rw [Real.log_abs, hres, Real.log_multiset_prod] at hlog
  · simpa only [Multiset.map_map, Function.comp_def, Real.log_abs] using hlog
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    exact hQ x hx

theorem rootTrace_strict {f : ℤ[X]} (hm : f.Monic) (hf : TotallyPositive f)
    (hd : 0 < f.natDegree) (hQ : ∀ x ∈ realRoots f, auxiliaryQ x ≠ 0) :
    2 * (f.natDegree : ℝ) < rootTrace f := by
  have hs := root_log_sum_nonnegative hm hf.1 hQ
  have hcard : (realRoots f).card ≠ 0 := by rw [realRoots_card hf.1]; omega
  have hne : realRoots f ≠ 0 := fun h => hcard (by rw [h]; rfl)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  have hstrict := Multiset.sum_lt_sum
    (s := realRoots f) (f := fun _ => (2 : ℝ))
    (g := fun x => x ^ 2 - x - Real.log |auxiliaryQ x|)
    (fun x hx => (auxiliary_inequality (hf.2 x hx).1 (hQ x hx)).le)
    ⟨x, hx, auxiliary_inequality (hf.2 x hx).1 (hQ x hx)⟩
  have hconst : ((realRoots f).map (fun _ => (2 : ℝ))).sum =
      2 * (f.natDegree : ℝ) := by
    simp [Multiset.map_const', realRoots_card hf.1, mul_comm]
  rw [hconst] at hstrict
  simp only [Multiset.sum_map_sub, rootTrace] at hstrict ⊢
  linarith

end ResearchMain.DominationRoots
