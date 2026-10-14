/-
Adapted from stormj-UH/spivak-lean, TranscendencePi and TranscendencePiAux.
Copyright 2026 Jon-Erik G. Storm. Licensed under Apache-2.0.
Changes: project-local namespace and imports; isolated polynomial reduction.
See THIRD_PARTY_NOTICES.md and LICENSE-APACHE-2.0.md.
-/
/-
# Transcendence of `π`: algebraic preliminaries

Helper lemmas for `SpivakCalculus/TranscendencePi.lean`.

* `sym_int`: a symmetric integer polynomial evaluated at complex numbers whose
  elementary symmetric functions are integers is an integer (via Mathlib's
  fundamental theorem of symmetric polynomials, `MvPolynomial.esymmAlgHom_surjective`).
* `esymm_int_of_roots`: if `P ∈ ℤ[X]` has leading coefficient `a`, the elementary
  symmetric functions of `a·α` (over the complex roots `α` of `P`) are integers (Vieta).
* The generic polynomial `∏_{t ⊆ {1,…,n}} (X − ∑_{j∈t} xⱼ)` and the generic sums
  `∑_{t} h(∑_{j∈t} xⱼ)` have symmetric coefficients.
* Small utilities: enumeration of a multiset, lifting integer-coefficient polynomials
  to `ℤ[X]`, a norm bound for multiset sums, and the algebraicity of `iπ`.
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace OscillatoryRecurrence
namespace TranscendencePi

open Polynomial Finset

/-- `z` is (the image of) a rational integer. -/
def IsInt (z : ℂ) : Prop := ∃ m : ℤ, z = m

theorem aeval_intCast {ι : Type*} (Ψ : MvPolynomial ι ℤ) (m : ι → ℤ) :
    MvPolynomial.aeval (fun i => (m i : ℂ)) Ψ = ((MvPolynomial.eval m Ψ : ℤ) : ℂ) := by
  induction Ψ using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem sym_int {σ : Type*} [Fintype σ] [DecidableEq σ] (Φ : MvPolynomial σ ℤ) (hΦ : Φ.IsSymmetric)
    (x : σ → ℂ) (hx : ∀ k, IsInt ((univ.val.map x).esymm k)) :
    IsInt (MvPolynomial.aeval x Φ) := by
  obtain ⟨Ψ, hΨ⟩ := MvPolynomial.esymmAlgHom_surjective ℤ (σ := σ) (n := Fintype.card σ) le_rfl
    ⟨Φ, hΦ⟩
  have hΦe : Φ = MvPolynomial.aeval (fun i : Fin (Fintype.card σ) =>
      MvPolynomial.esymm σ ℤ (i + 1)) Ψ := by
    rw [← MvPolynomial.esymmAlgHom_apply, hΨ]
  choose m hm using hx
  refine ⟨MvPolynomial.eval (fun i : Fin (Fintype.card σ) => m (i + 1)) Ψ, ?_⟩
  rw [hΦe, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm, hm]
  exact aeval_intCast Ψ _

section generic
variable (n : ℕ)

noncomputable def subsetSum (t : Finset (Fin n)) : MvPolynomial (Fin n) ℤ :=
  ∑ j ∈ t, MvPolynomial.X j

theorem rename_subsetSum (σ : Equiv.Perm (Fin n)) (t : Finset (Fin n)) :
    MvPolynomial.rename σ (subsetSum n t) = subsetSum n (Equiv.finsetCongr σ t) := by
  simp [subsetSum, Finset.sum_map]

theorem aeval_subsetSum (y : Fin n → ℂ) (t : Finset (Fin n)) :
    MvPolynomial.aeval y (subsetSum n t) = ∑ j ∈ t, y j := by
  simp [subsetSum]

noncomputable def genericProd : Polynomial (MvPolynomial (Fin n) ℤ) :=
  ∏ t : Finset (Fin n), (X - C (subsetSum n t))

theorem genericProd_coeff_isSymmetric (k : ℕ) : ((genericProd n).coeff k).IsSymmetric := by
  intro σ
  rw [show MvPolynomial.rename σ ((genericProd n).coeff k) =
      ((genericProd n).map (MvPolynomial.rename σ).toRingHom).coeff k from
      (Polynomial.coeff_map _ _).symm]
  congr 1
  simp only [genericProd, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_subsetSum]
  congr 1
  exact Fintype.prod_equiv (Equiv.finsetCongr σ) _ _ (fun t => rfl)

noncomputable def genericSum (h : ℤ[X]) : MvPolynomial (Fin n) ℤ :=
  ∑ t : Finset (Fin n), Polynomial.aeval (subsetSum n t) h

theorem genericSum_isSymmetric (h : ℤ[X]) : (genericSum n h).IsSymmetric := by
  intro σ
  simp only [genericSum, map_sum, ← Polynomial.aeval_algHom_apply, rename_subsetSum]
  exact Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ (fun t => rfl)

theorem genericProd_map (y : Fin n → ℂ) :
    (genericProd n).map (MvPolynomial.aeval y).toRingHom =
      ∏ t : Finset (Fin n), (X - C (∑ j ∈ t, y j)) := by
  simp [genericProd, Polynomial.map_prod, aeval_subsetSum]

theorem genericSum_aeval (y : Fin n → ℂ) (h : ℤ[X]) :
    MvPolynomial.aeval y (genericSum n h) = ∑ t : Finset (Fin n), aeval (∑ j ∈ t, y j) h := by
  simp only [genericSum, map_sum, ← Polynomial.aeval_algHom_apply, aeval_subsetSum]

end generic

theorem exists_enum (s : Multiset ℂ) : ∃ (n : ℕ) (x : Fin n → ℂ), univ.val.map x = s := by
  refine ⟨s.toList.length, s.toList.get, ?_⟩
  rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]

theorem esymm_int_of_roots (P : ℤ[X]) (hP : P ≠ 0) (k : ℕ) :
    IsInt (((P.aroots ℂ).map (fun z => (P.leadingCoeff : ℂ) * z)).esymm k) := by
  set a := P.leadingCoeff
  set Pc : ℂ[X] := P.map (algebraMap ℤ ℂ) with hPc
  have hinj : Function.Injective (algebraMap ℤ ℂ) := RingHom.injective_int _
  have hdeg : Pc.natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hlc : Pc.leadingCoeff = (a : ℂ) := by
    rw [hPc, leadingCoeff_map_of_injective hinj]; simp [a]
  have hcard : Multiset.card Pc.roots = Pc.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroots : P.aroots ℂ = Pc.roots := rfl
  have hsm := Multiset.pow_smul_esymm (a : ℂ) k (P.aroots ℂ)
  simp only [smul_eq_mul] at hsm
  rw [← hsm, hroots]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; exact ⟨1, by simp [Multiset.esymm]⟩
  by_cases hkd : k ≤ P.natDegree
  · have hv := coeff_eq_esymm_roots_of_card hcard (k := Pc.natDegree - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self (by omega), hlc] at hv
    refine ⟨a ^ (k - 1) * (-1) ^ k * P.coeff (P.natDegree - k), ?_⟩
    have hco : Pc.coeff (Pc.natDegree - k) = (P.coeff (P.natDegree - k) : ℂ) := by
      rw [hPc, coeff_map, hdeg]; simp
    rw [hco] at hv
    push_cast
    rw [hv]
    have hk' : (a : ℂ) ^ k = (a : ℂ) ^ (k - 1) * a := by
      rw [← pow_succ]; congr 1; omega
    rw [hk']
    have : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    linear_combination (-(↑a ^ (k - 1) * ↑a * Pc.roots.esymm k)) * this
  · refine ⟨0, ?_⟩
    have : Pc.roots.esymm k = 0 := by
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard, hdeg]; omega)]
      simp
    rw [this]; simp

theorem exists_lift (q : ℂ[X]) (hq : ∀ k, IsInt (q.coeff k)) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℂ) = q := by
  have : q ∈ lifts (Int.castRingHom ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨m, hm⟩ := hq k
    exact ⟨m, by simp [hm]⟩
  exact (mem_lifts q).mp this

theorem norm_sum_le_card_mul {S : Multiset ℂ} (f : ℂ → ℂ) (B : ℝ)
    (h : ∀ r ∈ S, ‖f r‖ ≤ B) : ‖(S.map f).sum‖ ≤ Multiset.card S * B := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have h1 := h a (Multiset.mem_cons_self _ _)
    have h2 := ih (fun r hr => h r (Multiset.mem_cons_of_mem hr))
    push_cast
    calc ‖f a + (S.map f).sum‖ ≤ ‖f a‖ + ‖(S.map f).sum‖ := norm_add_le _ _
      _ ≤ B + Multiset.card S * B := add_le_add h1 h2
      _ = (Multiset.card S + 1) * B := by ring

theorem exists_int_poly_of_isAlgebraic {x : ℂ} (hx : IsAlgebraic ℚ x) :
    ∃ q : ℤ[X], q ≠ 0 ∧ aeval x q = 0 := by
  obtain ⟨p, hp0, hp⟩ := hx
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) p, ?_, ?_⟩
  · simpa [IsLocalization.integerNormalization_eq_zero_iff] using hp0
  · obtain ⟨b, _, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
    have hmap : aeval x (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) =
        aeval x ((IsLocalization.integerNormalization (nonZeroDivisors ℤ) p).map
          (algebraMap ℤ ℚ)) := by
      simp [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq ℤ ℚ ℂ]
    rw [hmap, hb]
    simp [hp]

theorem isAlgebraic_I_mul_pi (h : IsAlgebraic ℚ Real.pi) :
    IsAlgebraic ℚ (Complex.I * (Real.pi : ℂ)) := by
  have h1 : IsAlgebraic ℚ ((Real.pi : ℝ) : ℂ) := by
    have := h.algebraMap (A := ℂ)
    simpa using this
  exact (Complex.isIntegral_I ℚ).isAlgebraic.mul h1

theorem exists_eval_zero_ne (q : ℤ[X]) (hq : q ≠ 0) :
    ∃ (m : ℕ) (q' : ℤ[X]), q' ≠ 0 ∧ q'.eval 0 ≠ 0 ∧ q = X ^ m * q' := by
  have key := pow_mul_divByMonic_rootMultiplicity_eq q (0 : ℤ)
  have hne := eval_divByMonic_pow_rootMultiplicity_ne_zero (0 : ℤ) hq
  rw [C_0, sub_zero] at key hne
  refine ⟨q.rootMultiplicity 0, q /ₘ X ^ q.rootMultiplicity 0, ?_, hne, key.symm⟩
  intro hc
  rw [hc, mul_zero] at key
  exact hq key.symm


end TranscendencePi
end OscillatoryRecurrence
