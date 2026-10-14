import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Order.Sublattice
import Mathlib.Tactic

namespace ResearchMain.WishartBlocks

open MeasureTheory Bornology
open scoped BigOperators Pointwise Topology

theorem integerGrid_mem_iff {n N : ℕ} [NeZero N] (x : Fin n → ℝ) :
    x ∈ (N : ℝ)⁻¹ •
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ)) ↔
      ∀ i, (N : ℝ) * x i ∈ Set.range (algebraMap ℤ ℝ) := by
  have h := BoxIntegral.unitPartition.mem_smul_span_iff (n := N) (v := x)
  change (x ∈ (((N : ℝ)⁻¹ •
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) : Set (Fin n → ℝ))) ↔ _ at h
  exact h

noncomputable def scaledIntegerLattice (n N : ℕ) [NeZero N] : Sublattice (Fin n → ℝ) where
  carrier := (N : ℝ)⁻¹ •
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ))
  supClosed' := by
    intro x hx y hy
    rw [integerGrid_mem_iff] at hx hy ⊢
    intro i
    change (N : ℝ) * max (x i) (y i) ∈ Set.range (algebraMap ℤ ℝ)
    rcases le_total (x i) (y i) with h | h
    · simpa only [max_eq_right h] using hy i
    · simpa only [max_eq_left h] using hx i
  infClosed' := by
    intro x hx y hy
    rw [integerGrid_mem_iff] at hx hy ⊢
    intro i
    change (N : ℝ) * min (x i) (y i) ∈ Set.range (algebraMap ℤ ℝ)
    rcases le_total (x i) (y i) with h | h
    · simpa only [min_eq_left h] using hx i
    · simpa only [min_eq_right h] using hy i

theorem bounded_grid_finite {n N : ℕ} [NeZero N] (s : Sublattice (Fin n → ℝ))
    (hs : IsBounded (s : Set (Fin n → ℝ))) :
    Set.Finite ((s ⊓ scaledIntegerLattice n N : Sublattice (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  change Set.Finite ((s : Set (Fin n → ℝ)) ∩
    (N : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ)))
  rw [← Submodule.coe_pointwise_smul,
    ZSpan.smul (Pi.basisFun ℝ (Fin n)) (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)))]
  exact ZSpan.setFinite_inter _ hs

theorem finite_sublattice_fkg {E : Type*} [DistribLattice E] (s : Sublattice E) [Fintype s]
    {μ F G : E → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hmF : Monotone F) (hmG : Monotone G)
    (hM : ∀ x y, μ x * μ y ≤ μ (x ⊓ y) * μ (x ⊔ y)) :
    (∑ x : s, μ x * F x) * (∑ x : s, μ x * G x) ≤
      (∑ x : s, μ x) * (∑ x : s, μ x * (F x * G x)) := by
  apply fkg
  · intro x
    exact hμ x
  · intro x
    exact hF x
  · intro x
    exact hG x
  · intro x y h
    exact hmF h
  · intro x y h
    exact hmG h
  · intro x y
    exact hM x y

theorem continuous_fkg_integral {n : ℕ} (s : Sublattice (Fin n → ℝ))
    (hs : IsBounded (s : Set (Fin n → ℝ)))
    (hsM : MeasurableSet (s : Set (Fin n → ℝ)))
    (hsF : volume (frontier (s : Set (Fin n → ℝ))) = 0)
    {μ F G : (Fin n → ℝ) → ℝ}
    (hcμ : Continuous μ) (hcF : Continuous F) (hcG : Continuous G)
    (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hmF : Monotone F) (hmG : Monotone G)
    (hM : ∀ x y, μ x * μ y ≤ μ (x ⊓ y) * μ (x ⊔ y)) :
    (∫ x in (s : Set (Fin n → ℝ)), μ x * F x) *
      (∫ x in (s : Set (Fin n → ℝ)), μ x * G x) ≤
    (∫ x in (s : Set (Fin n → ℝ)), μ x) *
      (∫ x in (s : Set (Fin n → ℝ)), μ x * (F x * G x)) := by
  let A : ℕ → ℝ := fun N =>
    (∑' x : ↑((s : Set (Fin n → ℝ)) ∩ (N : ℝ)⁻¹ •
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ))), μ x * F x) /
      (N : ℝ) ^ n
  let B : ℕ → ℝ := fun N =>
    (∑' x : ↑((s : Set (Fin n → ℝ)) ∩ (N : ℝ)⁻¹ •
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ))), μ x * G x) /
      (N : ℝ) ^ n
  let C : ℕ → ℝ := fun N =>
    (∑' x : ↑((s : Set (Fin n → ℝ)) ∩ (N : ℝ)⁻¹ •
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ))), μ x) /
      (N : ℝ) ^ n
  let D : ℕ → ℝ := fun N =>
    (∑' x : ↑((s : Set (Fin n → ℝ)) ∩ (N : ℝ)⁻¹ •
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) : Set (Fin n → ℝ))),
      μ x * (F x * G x)) / (N : ℝ) ^ n
  have hA : Filter.Tendsto A Filter.atTop
      (𝓝 (∫ x in (s : Set (Fin n → ℝ)), μ x * F x)) := by
    simpa only [A, Fintype.card_fin] using
      tendsto_tsum_div_pow_atTop_integral (s : Set (Fin n → ℝ)) (fun x => μ x * F x)
        (hcμ.mul hcF) hs hsM hsF
  have hB : Filter.Tendsto B Filter.atTop
      (𝓝 (∫ x in (s : Set (Fin n → ℝ)), μ x * G x)) := by
    simpa only [B, Fintype.card_fin] using
      tendsto_tsum_div_pow_atTop_integral (s : Set (Fin n → ℝ)) (fun x => μ x * G x)
        (hcμ.mul hcG) hs hsM hsF
  have hC : Filter.Tendsto C Filter.atTop
      (𝓝 (∫ x in (s : Set (Fin n → ℝ)), μ x)) := by
    simpa only [C, Fintype.card_fin] using
      tendsto_tsum_div_pow_atTop_integral (s : Set (Fin n → ℝ)) μ hcμ hs hsM hsF
  have hD : Filter.Tendsto D Filter.atTop
      (𝓝 (∫ x in (s : Set (Fin n → ℝ)), μ x * (F x * G x))) := by
    simpa only [D, Fintype.card_fin] using
      tendsto_tsum_div_pow_atTop_integral (s : Set (Fin n → ℝ)) (fun x => μ x * (F x * G x))
        (hcμ.mul (hcF.mul hcG)) hs hsM hsF
  apply le_of_tendsto_of_tendsto (hA.mul hB) (hC.mul hD)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  let : NeZero N := ⟨by omega⟩
  let L := s ⊓ scaledIntegerLattice n N
  let : Fintype L := (bounded_grid_finite s hs).fintype
  have hi := finite_sublattice_fkg L hμ hF hG hmF hmG hM
  have hi' : (∑' x : L, μ x * F x) * (∑' x : L, μ x * G x) ≤
      (∑' x : L, μ x) * (∑' x : L, μ x * (F x * G x)) := by
    simpa only [tsum_fintype] using hi
  dsimp [A, B, C, D]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hi' (mul_self_nonneg ((N : ℝ) ^ n))

end ResearchMain.WishartBlocks
