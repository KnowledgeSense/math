import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Pi
import SumsetRanges.Definitions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SumsetRanges
open Finset

abbrev LinearAtom (m : ℕ) := Fin m ⊕ Fin (m-1)
abbrev LinearIndex (m : ℕ) := Fin m ⊕ Option (Fin (m-1))
abbrev LinearLattice (m : ℕ) := LinearAtom m → ℤ

def linearPoint {m : ℕ} : LinearIndex m → LinearLattice m
  | Sum.inl i => fun a => if a = Sum.inl i then 1 else 0
  | Sum.inr (some j) => fun a => if a = Sum.inr j then 1 else 0
  | Sum.inr none => fun a => match a with
    | Sum.inl _ => 1
    | Sum.inr _ => -1

def linearBlock (m : ℕ) : Finset (LinearLattice m) :=
  Finset.univ.image linearPoint

def alphaIndices (m : ℕ) : Finset (LinearIndex m) :=
  Finset.univ.image Sum.inl

def betaIndices (m : ℕ) : Finset (LinearIndex m) :=
  Finset.univ.image Sum.inr

theorem sum_linearPoint_alpha {m : ℕ} (S : Finset (LinearIndex m)) (i : Fin m) :
    (∑ a ∈ S, linearPoint a) (Sum.inl i) =
      (if Sum.inl i ∈ S then 1 else 0) +
      (if Sum.inr none ∈ S then 1 else 0) := by
  have h : ∀ a : LinearIndex m, linearPoint a (Sum.inl i) =
      (if a = Sum.inl i then (1 : ℤ) else 0) +
      (if a = Sum.inr none then 1 else 0) := by
    intro a
    rcases a with a | (_ | a) <;> simp [linearPoint, eq_comm]
  simp only [Finset.sum_apply, h, Finset.sum_add_distrib]
  simp

theorem sum_linearPoint_beta {m : ℕ} (S : Finset (LinearIndex m)) (j : Fin (m-1)) :
    (∑ a ∈ S, linearPoint a) (Sum.inr j) =
      (if Sum.inr (some j) ∈ S then 1 else 0) -
      (if Sum.inr none ∈ S then 1 else 0) := by
  have h : ∀ a : LinearIndex m, linearPoint a (Sum.inr j) =
      (if a = Sum.inr (some j) then (1 : ℤ) else 0) -
      (if a = Sum.inr none then 1 else 0) := by
    intro a
    rcases a with a | (_ | a) <;> simp [linearPoint, eq_comm]
  simp only [Finset.sum_apply, h, Finset.sum_sub_distrib]
  simp

@[simp] theorem mem_alphaIndices {m : ℕ} (a : LinearIndex m) :
    a ∈ alphaIndices m ↔ ∃ i, a = Sum.inl i := by
  simp [alphaIndices, eq_comm]

@[simp] theorem mem_betaIndices {m : ℕ} (a : LinearIndex m) :
    a ∈ betaIndices m ↔ ∃ j, a = Sum.inr j := by
  simp [betaIndices, eq_comm]

/-- The only collision of subset sums in one relation block is the defining
 equality between all alpha points and all beta points. -/
theorem linearBlock_subset_collision {m : ℕ} (S T : Finset (LinearIndex m))
    (he : ∑ a ∈ S, linearPoint a = ∑ a ∈ T, linearPoint a) :
    S = T ∨ (S = alphaIndices m ∧ T = betaIndices m) ∨
      (S = betaIndices m ∧ T = alphaIndices m) := by
  have ha (i : Fin m) := congrFun he (Sum.inl i)
  have hb (j : Fin (m-1)) := congrFun he (Sum.inr j)
  simp only [sum_linearPoint_alpha] at ha
  simp only [sum_linearPoint_beta] at hb
  by_cases hS : Sum.inr none ∈ S <;> by_cases hT : Sum.inr none ∈ T
  · left
    ext a
    rcases a with i | (_ | j)
    · have h := ha i
      simp only [ite_eq_left hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
    · simp [hS, hT]
    · have h := hb j
      simp only [ite_eq_left hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
  · right; right
    constructor <;> ext a <;> rcases a with i | (_ | j)
    · have h := ha i
      simp only [ite_eq_left hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
    · simp [hS]
    · have h := hb j
      simp only [ite_eq_left hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
    · have h := ha i
      simp only [ite_eq_left hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
    · simp [hT]
    · have h := hb j
      simp only [ite_eq_left hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
  · right; left
    constructor <;> ext a <;> rcases a with i | (_ | j)
    · have h := ha i
      simp only [ite_eq_right hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
    · simp [hS]
    · have h := hb j
      simp only [ite_eq_right hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
    · have h := ha i
      simp only [ite_eq_right hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
    · simp [hT]
    · have h := hb j
      simp only [ite_eq_right hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
  · left
    ext a
    rcases a with i | (_ | j)
    · have h := ha i
      simp only [ite_eq_right hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
    · simp [hS, hT]
    · have h := hb j
      simp only [ite_eq_right hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all

@[simp] theorem card_alphaIndices (m : ℕ) : (alphaIndices m).card = m := by
  rw [alphaIndices, Finset.card_image_of_injective _ Sum.inl_injective]
  simp

@[simp] theorem card_betaIndices (m : ℕ) (hm : 1 ≤ m) : (betaIndices m).card = m := by
  rw [betaIndices, Finset.card_image_of_injective _ Sum.inr_injective]
  simp
  omega

theorem alphaIndices_ne_betaIndices (m : ℕ) : alphaIndices m ≠ betaIndices m := by
  intro h
  have hx : (Sum.inr none : LinearIndex m) ∈ betaIndices m := by simp
  rw [← h] at hx
  simp at hx

theorem linearPoint_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (linearPoint (m := m)) := by
  intro a b he
  have hs : ∑ x ∈ ({a} : Finset (LinearIndex m)), linearPoint x =
      ∑ x ∈ ({b} : Finset (LinearIndex m)), linearPoint x := by simpa using he
  rcases linearBlock_subset_collision {a} {b} hs with h | ⟨h,_⟩ | ⟨h,_⟩
  · simpa using h
  · have hc := congrArg Finset.card h
    simp only [Finset.card_singleton, card_alphaIndices] at hc
    omega
  · have hc := congrArg Finset.card h
    rw [Finset.card_singleton, card_betaIndices m (by omega)] at hc
    omega

theorem card_linearBlock (m : ℕ) (hm : 2 ≤ m) : (linearBlock m).card = 2*m := by
  rw [linearBlock, Finset.card_image_of_injective _ (linearPoint_injective hm)]
  simp
  omega

theorem sum_alpha_eq_sum_beta (m : ℕ) :
    ∑ a ∈ alphaIndices m, linearPoint a = ∑ a ∈ betaIndices m, linearPoint a := by
  funext a
  rcases a with i | j
  · rw [sum_linearPoint_alpha, sum_linearPoint_alpha]
    simp
  · rw [sum_linearPoint_beta, sum_linearPoint_beta]
    simp

/-- Exact restricted-sum count of a single linear relation block. -/
theorem card_restrictedSums_linearBlock (m q : ℕ) (hm : 2 ≤ m) :
    (restrictedSums (linearBlock m) q).card = (2*m).choose q - if q=m then 1 else 0 := by
  classical
  let f : LinearIndex m ↪ LinearLattice m := ⟨linearPoint, linearPoint_injective hm⟩
  have hmap : linearBlock m = (Finset.univ : Finset (LinearIndex m)).map f := by
    simp [linearBlock, Finset.map_eq_image, f]
  rw [hmap, restrictedSums_map]
  change ((Finset.univ.powersetCard q).image (fun S : Finset (LinearIndex m) =>
    ∑ a ∈ S, linearPoint a)).card = _
  let U : Finset (Finset (LinearIndex m)) := Finset.univ.powersetCard q
  let g : Finset (LinearIndex m) → LinearLattice m := fun S => ∑ a ∈ S, linearPoint a
  change (U.image g).card = _
  have hcard : U.card = (2*m).choose q := by
    simp only [U, Finset.card_powersetCard, Finset.card_univ]
    congr 1
    simp
    omega
  by_cases hq : q=m
  · subst q
    rw [ite_eq_left rfl]
    have hα : alphaIndices m ∈ U := by simp [U]
    have hβ : betaIndices m ∈ U := by simp [U, card_betaIndices m (by omega)]
    have himage : (U.erase (betaIndices m)).image g = U.image g := by
      apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
      intro x hx
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
      by_cases he : S=betaIndices m
      · refine Finset.mem_image.mpr ⟨alphaIndices m, ?_, ?_⟩
        · exact Finset.mem_erase.mpr ⟨alphaIndices_ne_betaIndices m,hα⟩
        · simpa [g, he] using sum_alpha_eq_sum_beta m
      · exact Finset.mem_image.mpr ⟨S,Finset.mem_erase.mpr ⟨he,hS⟩,rfl⟩
    have hinj : Set.InjOn g (U.erase (betaIndices m)) := by
      intro S hS T hT he
      rcases linearBlock_subset_collision S T he with h | ⟨_,h⟩ | ⟨h,_⟩
      · exact h
      · exact False.elim ((Finset.mem_erase.mp hT).1 h)
      · exact False.elim ((Finset.mem_erase.mp hS).1 h)
    rw [← himage, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hβ, hcard]
  · rw [ite_eq_right hq, Nat.sub_zero]
    have hinj : Set.InjOn g U := by
      intro S hS T hT he
      have hcS : S.card=q := (Finset.mem_powersetCard.mp hS).2
      rcases linearBlock_subset_collision S T he with h | ⟨h,_⟩ | ⟨h,_⟩
      · exact h
      · rw [h, card_alphaIndices] at hcS
        exact False.elim (hq hcS.symm)
      · rw [h, card_betaIndices m (by omega)] at hcS
        exact False.elim (hq hcS.symm)
    rw [Finset.card_image_of_injOn hinj, hcard]

theorem linearBlock_subset_card_eq {m : ℕ} (hm : 1 ≤ m)
    (S T : Finset (LinearIndex m))
    (he : ∑ a ∈ S, linearPoint a = ∑ a ∈ T, linearPoint a) : S.card = T.card := by
  rcases linearBlock_subset_collision S T he with h | ⟨hS,hT⟩ | ⟨hS,hT⟩
  · rw [h]
  · rw [hS,hT,card_alphaIndices,card_betaIndices m hm]
  · rw [hS,hT,card_alphaIndices,card_betaIndices m hm]

end SumsetRanges
