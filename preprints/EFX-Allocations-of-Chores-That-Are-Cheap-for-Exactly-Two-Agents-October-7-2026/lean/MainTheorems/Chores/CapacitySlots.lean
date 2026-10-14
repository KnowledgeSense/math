import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

namespace ResearchMain.Chores

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Slot (u : A → ℕ) := (a : A) × Fin (u a)

def slotBlock (u : A → ℕ) (U : Finset A) : Finset (Slot u) :=
  U.sigma (fun _ => Finset.univ)

def mandatorySlots (l u : A → ℕ) (U : Finset A) : Finset (Slot u) :=
  U.sigma (fun a => Finset.univ.filter (fun i : Fin (u a) => i.val < l a))

def optionalSlots (l u : A → ℕ) : Finset (Slot u) :=
  Finset.univ.sigma (fun a => Finset.univ.filter (fun i : Fin (u a) => l a ≤ i.val))

omit [Fintype A] [DecidableEq A] in
theorem mem_slotBlock (u : A → ℕ) (U : Finset A) (s : Slot u) :
    s ∈ slotBlock u U ↔ s.1 ∈ U := by
  simp [slotBlock]

omit [Fintype A] [DecidableEq A] in
theorem mem_mandatorySlots (l u : A → ℕ) (U : Finset A) (s : Slot u) :
    s ∈ mandatorySlots l u U ↔ s.1 ∈ U ∧ s.2.val < l s.1 := by
  simp [mandatorySlots]

omit [DecidableEq A] in
theorem mem_optionalSlots (l u : A → ℕ) (s : Slot u) :
    s ∈ optionalSlots l u ↔ l s.1 ≤ s.2.val := by
  simp [optionalSlots]

omit [Fintype A] [DecidableEq A] in
theorem card_slotBlock (u : A → ℕ) (U : Finset A) :
    (slotBlock u U).card = ∑ a ∈ U, u a := by
  simp [slotBlock, Finset.card_sigma]

theorem card_fin_initial {l u : ℕ} (h : l ≤ u) :
    ((Finset.univ : Finset (Fin u)).filter (fun i => i.val < l)).card = l := by
  classical
  calc
    _ = (Finset.univ : Finset (Fin l)).card := by
      apply Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin l))
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        exact Fin.ext (congrArg (fun x : Fin l => x.val) hij)
      · intro j _
        refine ⟨Fin.castLE h j, ?_, ?_⟩
        · simp [j.isLt]
        · rfl
    _ = l := by simp

omit [Fintype A] [DecidableEq A] in
theorem card_mandatorySlots (l u : A → ℕ) (h : ∀ a, l a ≤ u a) (U : Finset A) :
    (mandatorySlots l u U).card = ∑ a ∈ U, l a := by
  rw [mandatorySlots, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun a _ => card_fin_initial (h a))

omit [DecidableEq A] in
theorem card_optionalSlots (l u : A → ℕ) (h : ∀ a, l a ≤ u a) :
    (optionalSlots l u).card + ∑ a, l a = ∑ a, u a := by
  have hf (a : A) :
      ((Finset.univ : Finset (Fin (u a))).filter (fun i => l a ≤ i.val)).card + l a = u a := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (u a)))) (fun i => i.val < l a)
    rw [card_fin_initial (h a)] at hc
    simpa [not_lt, add_comm] using hc
  simp only [optionalSlots, Finset.card_sigma]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => hf a)

omit [DecidableEq A] in
theorem mandatory_optional_disjoint (l u : A → ℕ) (U : Finset A) :
    Disjoint (mandatorySlots l u U) (optionalSlots l u) := by
  rw [Finset.disjoint_left]
  intro s hs ho
  have hm := (mem_mandatorySlots l u U s).mp hs
  have hop := (mem_optionalSlots l u s).mp ho
  omega

theorem mandatory_union_optional_card (l u : A → ℕ) (h : ∀ a, l a ≤ u a) (U : Finset A) :
    (mandatorySlots l u U ∪ optionalSlots l u).card =
      (optionalSlots l u).card + ∑ a ∈ U, l a := by
  rw [Finset.card_union_of_disjoint (mandatory_optional_disjoint l u U),
    card_mandatorySlots l u h U, add_comm]

end ResearchMain.Chores
