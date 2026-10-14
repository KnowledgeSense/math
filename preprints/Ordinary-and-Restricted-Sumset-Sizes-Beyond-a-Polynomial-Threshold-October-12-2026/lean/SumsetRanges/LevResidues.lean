import SumsetRanges.LevNormalization
import Mathlib.Data.ZMod.Basic

open Finset
namespace SumsetRanges

/-- A normalized set with at least two elements has positive diameter. -/
theorem normalized_diameter_pos (B : Finset ℤ) (d : ℕ)
    (hcard : 2 ≤ B.card) (hbound : ∀ b ∈ B, 0 ≤ b ∧ b ≤ d) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  have hsub : B ⊆ {0} := by
    intro b hb
    have hh := hbound b hb
    simp only [hd0, Nat.cast_zero] at hh
    simpa only [Finset.mem_singleton] using le_antisymm hh.2 hh.1
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  omega

/-- Reduction modulo the diameter is injective after removing the right endpoint. -/
theorem normalized_cast_injOn_erase (B : Finset ℤ) (d : ℕ)
    (hbound : ∀ b ∈ B, 0 ≤ b ∧ b ≤ d) :
    Set.InjOn (Int.castAddHom (ZMod d)) (B.erase (d : ℤ)) := by
  intro x hx y hy he
  obtain ⟨hxd, hxB⟩ := Finset.mem_erase.mp hx
  obtain ⟨hyd, hyB⟩ := Finset.mem_erase.mp hy
  obtain ⟨hx0, hxle⟩ := hbound x hxB
  obtain ⟨hy0, hyle⟩ := hbound y hyB
  have hxlt : x < (d : ℤ) := lt_of_le_of_ne hxle hxd
  have hylt : y < (d : ℤ) := lt_of_le_of_ne hyle hyd
  have hm := (ZMod.intCast_eq_intCast_iff' x y d).mp he
  simpa only [Int.emod_eq_of_lt hx0 hxlt, Int.emod_eq_of_lt hy0 hylt] using hm

/-- Both endpoints are the unique duplicate introduced by reduction modulo the diameter. -/
theorem normalized_cast_image_erase (B : Finset ℤ) (d : ℕ) (hd : 0 < d)
    (hzero : 0 ∈ B) :
    (B.erase (d : ℤ)).image (Int.castAddHom (ZMod d)) =
      B.image (Int.castAddHom (ZMod d)) := by
  apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  by_cases hxd : x = (d : ℤ)
  · subst x
    refine Finset.mem_image.mpr ⟨0, Finset.mem_erase.mpr ⟨?_, hzero⟩, ?_⟩
    · exact_mod_cast (Nat.ne_of_lt hd)
    · simp
  · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxd, hx⟩, rfl⟩

theorem normalized_cast_card (B : Finset ℤ) (d : ℕ)
    (hcard : 2 ≤ B.card) (hzero : 0 ∈ B) (hend : (d : ℤ) ∈ B)
    (hbound : ∀ b ∈ B, 0 ≤ b ∧ b ≤ d) :
    (B.image (Int.castAddHom (ZMod d))).card = B.card-1 := by
  rw [← normalized_cast_image_erase B d (normalized_diameter_pos B d hcard hbound) hzero]
  rw [Finset.card_image_iff.mpr (normalized_cast_injOn_erase B d hbound)]
  exact Finset.card_erase_of_mem hend

/-- GCD-one integer sets generate every residue modulo their diameter. -/
theorem normalized_cast_closure (B : Finset ℤ) (d : ℕ) (hgcd : B.gcd id = 1) :
    AddSubgroup.closure (B.image (Int.castAddHom (ZMod d)) : Set (ZMod d)) = ⊤ := by
  rw [Finset.coe_image, ← AddMonoidHom.map_closure,
    Int.closure_eq_zmultiples_finsetGcd, hgcd, Int.zmultiples_one,
    AddSubgroup.map_top]
  exact AddMonoidHom.range_eq_top.mpr ZMod.intCast_surjective

end SumsetRanges
