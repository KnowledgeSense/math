import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

open Finset
open scoped Pointwise

namespace SumsetRanges

/-- Sums of exactly q elements, allowing repetitions. -/
def ordinarySums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : ℕ → Finset α
  | 0 => {0}
  | q+1 => A + ordinarySums A q

/-- Sums of q pairwise distinct elements of A. -/
def restrictedSums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (q : ℕ) : Finset α :=
  (A.powersetCard q).image (fun S => ∑ a ∈ S, a)

@[simp] theorem mem_restrictedSums {α : Type*} [AddCommMonoid α] [DecidableEq α]
    {A : Finset α} {q : ℕ} {x : α} :
    x ∈ restrictedSums A q ↔ ∃ S ⊆ A, S.card = q ∧ ∑ a ∈ S, a = x := by
  simp only [restrictedSums, mem_image, mem_powersetCard]
  constructor
  · rintro ⟨S, ⟨hS,hq⟩, hx⟩; exact ⟨S,hS,hq,hx⟩
  · rintro ⟨S,hS,hq,hx⟩; exact ⟨S,⟨hS,hq⟩,hx⟩

@[simp] theorem restrictedSums_zero {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : restrictedSums A 0 = {0} := by simp [restrictedSums]

theorem card_restrictedSums_le {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (q : ℕ) : (restrictedSums A q).card ≤ A.card.choose q := by
  calc
    _ ≤ (A.powersetCard q).card := Finset.card_image_le
    _ = _ := Finset.card_powersetCard q A

theorem restrictedSums_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    [AddCommMonoid β] (A : Finset α) (f : α ↪ β) (q : ℕ) :
    restrictedSums (A.map f) q = (A.powersetCard q).image (fun S => ∑ a ∈ S, f a) := by
  unfold restrictedSums
  rw [Finset.powersetCard_map, Finset.map_eq_image, Finset.image_image]
  congr 1
  funext S
  simp

/-- Actual attainable cardinalities for k-element integer sets. -/
def ordinaryRange (h k : ℕ) : Set ℕ :=
  {t | ∃ A : Finset ℤ, A.card = k ∧ (ordinarySums A h).card = t}

def restrictedRange (h k : ℕ) : Set ℕ :=
  {t | ∃ A : Finset ℤ, A.card = k ∧ (restrictedSums A h).card = t}

def ordinaryMinimum (h k : ℕ) : ℕ := h*k-h+1

def excludedValues (h k : ℕ) : Finset ℕ :=
  (range (min h k-2)).biUnion (fun l =>
    Finset.Icc (ordinaryMinimum h k+l*h+1) (ordinaryMinimum h k+l*h+(h-2-l)))

def momentOrder (h : ℕ) : ℕ := 4*h^2

def restrictedDimension (h : ℕ) : ℕ := momentOrder h+2*h+2

def restrictedScale (h : ℕ) : ℕ := 4*h*(2*h+2)^(momentOrder h)+2*h+1

def restrictedConstant (h : ℕ) : ℕ :=
  restrictedDimension h * restrictedScale h *
    (h*restrictedScale h+1)^(restrictedDimension h-1)

def restrictedExponent (h : ℕ) : ℕ :=
  momentOrder h*restrictedDimension h + Nat.clog 2 (restrictedConstant h)

def ordinaryExponent (h : ℕ) : ℕ := (h^2+2)*(h^2+2*h+2)

/-- The exact restricted main assertion, including the specified witness bound. -/
def RestrictedMainStatement : Prop := ∀ h k : ℕ, 2 ≤ h → (2*h)^80 ≤ k →
  restrictedRange h k = Set.Icc (h*(k-h)+1) (k.choose h) ∧
  ∀ t ∈ Set.Icc (h*(k-h)+1) (k.choose h), ∃ A : Finset ℤ,
    A.card = k ∧ (∀ a ∈ A, 0 ≤ a ∧ a ≤ (k^(restrictedExponent h) : ℕ)) ∧
    (restrictedSums A h).card = t

/-- The ordinary main assertion; the exclusion theorem is part of its proof. -/
def OrdinaryMainStatement : Prop := ∀ h k : ℕ, 2 ≤ h → (2*h)^80 ≤ k →
  ordinaryRange h k = Set.Icc (ordinaryMinimum h k) ((h+k-1).choose h) \ (excludedValues h k : Set ℕ) ∧
  ∀ t ∈ Set.Icc (ordinaryMinimum h k) ((h+k-1).choose h) \ (excludedValues h k : Set ℕ),
    ∃ A : Finset ℤ, A.card = k ∧
      (∀ a ∈ A, 0 ≤ a ∧ a ≤ (k^(ordinaryExponent h) : ℕ)) ∧
      (ordinarySums A h).card = t

end SumsetRanges
