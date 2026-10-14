import SumsetRanges.OrdinaryImages
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped Pointwise
namespace SumsetRanges

/-- Translation and division by the common factor preserve every ordinary sumset size. -/
theorem exists_ordinary_normalization (A : Finset ℤ) (hA : 2 ≤ A.card) :
    ∃ B : Finset ℤ, ∃ d : ℕ,
      B.card = A.card ∧
      (∀ q, (ordinarySums B q).card = (ordinarySums A q).card) ∧
      0 ∈ B ∧ (d : ℤ) ∈ B ∧
      (∀ b ∈ B, 0 ≤ b ∧ b ≤ d) ∧ B.gcd id = 1 := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  let a := A.min' hne
  let C := A.image (fun x => x - a)
  have hCcard : C.card = A.card :=
    Finset.card_image_of_injective _ (fun _ _ h => by omega)
  have hCzero : 0 ∈ C := by
    exact Finset.mem_image.mpr ⟨a, A.min'_mem hne, sub_self a⟩
  have hCnonneg : ∀ x ∈ C, 0 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact sub_nonneg.mpr (Finset.min'_le A y hy)
  have hCne : C.Nonempty := ⟨0, hCzero⟩
  have hCnonzero : ∃ x ∈ C, x ≠ 0 := by
    by_contra! hc
    have hsub : C ⊆ {0} := by intro x hx; simpa using hc x hx
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega
  let g := C.gcd id
  have hg0 : g ≠ 0 := by
    intro hg
    obtain ⟨x, hx, hxn⟩ := hCnonzero
    exact hxn ((Finset.gcd_eq_zero_iff.mp hg) x hx)
  have hgnonneg : 0 ≤ g := by
    have hh : |g| = g := by
      rw [Int.abs_eq_normalize]
      exact Finset.normalize_gcd
    exact hh ▸ abs_nonneg g
  have hgpos : 0 < g := lt_of_le_of_ne hgnonneg (Ne.symm hg0)
  obtain ⟨f, hf, hfgcd⟩ := Finset.extract_gcd (s := C) id hCne
  have hfx : ∀ x ∈ C, x = g * f x := hf
  let B := C.image f
  have hf_inj : Set.InjOn f C := by
    intro x hx y hy he
    rw [hfx x hx, hfx y hy, he]
  have hBcard : B.card = C.card := Finset.card_image_iff.mpr hf_inj
  have hfzero : f 0 = 0 := by
    have hz := hfx 0 hCzero
    exact (mul_eq_zero.mp hz.symm).resolve_left hg0
  have hBzero : 0 ∈ B := by
    exact Finset.mem_image.mpr ⟨0, hCzero, hfzero⟩
  have hBnonneg : ∀ b ∈ B, 0 ≤ b := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have hn := hCnonneg x hx
    rw [hfx x hx] at hn
    exact nonneg_of_mul_nonneg_right hn hgpos
  have hBne : B.Nonempty := ⟨0, hBzero⟩
  let d := (B.max' hBne).toNat
  have hd : (d : ℤ) = B.max' hBne := Int.toNat_of_nonneg (hBnonneg _ (B.max'_mem hBne))
  refine ⟨B, d, hBcard.trans hCcard, ?_, hBzero, hd ▸ B.max'_mem hBne, ?_, ?_⟩
  · intro q
    let m : ℤ →+ ℤ :=
      { toFun := fun z => g*z
        map_zero' := mul_zero g
        map_add' := mul_add g }
    have hBC : B.image m = C := by
      ext x
      constructor
      · intro hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        change g * f y ∈ C
        rw [← hfx y hy]
        exact hy
      · intro hx
        exact Finset.mem_image.mpr ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, (hfx x hx).symm⟩
    have hBCs : (ordinarySums B q).card = (ordinarySums C q).card := by
      rw [← hBC, ordinarySums_image]
      symm
      exact Finset.card_image_of_injective _ (fun _ _ he => mul_left_cancel₀ hg0 he)
    have hCeq : C = A.image (fun x => (AddMonoidHom.id ℤ) x + (-a)) := by
      rfl
    rw [hBCs, hCeq, ordinarySums_affine_image]
    exact Finset.card_image_of_injective _ (fun _ _ he => add_right_cancel he)
  · intro b hb
    exact ⟨hBnonneg b hb, hd ▸ Finset.le_max' B b hb⟩
  · simpa only [B, Finset.gcd_image, Function.comp_def, id_eq] using hfgcd

end SumsetRanges
