import SumsetRanges.SharedAtomBlock

open Finset
namespace SumsetRanges

abbrev RowIndex (m : ℕ) := Option (Fin (m-1))

def rowAlpha (m : ℕ) : Finset (RowIndex m) := {none}
def rowBeta (m : ℕ) : Finset (RowIndex m) := Finset.univ.erase none

def rowValue {m : ℕ} (S : Finset (RowIndex m)) (j : Fin (m-1)) : ℤ :=
  (if some j ∈ S then 1 else 0) + (if none ∈ S then 1 else 0)

@[simp] theorem mem_rowAlpha {m : ℕ} (a : RowIndex m) : a ∈ rowAlpha m ↔ a=none := by
  simp [rowAlpha]
@[simp] theorem mem_rowBeta {m : ℕ} (a : RowIndex m) : a ∈ rowBeta m ↔ a≠none := by
  simp [rowBeta]
@[simp] theorem card_rowAlpha (m : ℕ) : (rowAlpha m).card=1 := by simp [rowAlpha]
@[simp] theorem card_rowBeta (m : ℕ) : (rowBeta m).card=m-1 := by simp [rowBeta]

theorem rowAlpha_ne_rowBeta (m : ℕ) : rowAlpha m ≠ rowBeta m := by
  intro h
  have hn : none ∈ rowAlpha m := by simp
  rw [h] at hn
  simp at hn

theorem rowValue_collision {m : ℕ} (S T : Finset (RowIndex m))
    (he : rowValue S = rowValue T) :
    S=T ∨ (S=rowAlpha m ∧ T=rowBeta m) ∨ (S=rowBeta m ∧ T=rowAlpha m) := by
  have hj (j : Fin (m-1)) := congrFun he j
  simp only [rowValue] at hj
  by_cases hS : none ∈ S <;> by_cases hT : none ∈ T
  · left
    ext (_ | j)
    · simp [hS,hT]
    · have h := hj j
      simp only [ite_eq_left hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
  · right; left
    constructor <;> ext (_ | j)
    · simp [hS]
    · have h := hj j
      simp only [ite_eq_left hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
    · simp [hT]
    · have h := hj j
      simp only [ite_eq_left hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all
  · right; right
    constructor <;> ext (_ | j)
    · simp [hS]
    · have h := hj j
      simp only [ite_eq_right hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
    · simp [hT]
    · have h := hj j
      simp only [ite_eq_right hS, ite_eq_left hT] at h
      split_ifs at h <;> simp_all
  · left
    ext (_ | j)
    · simp [hS,hT]
    · have h := hj j
      simp only [ite_eq_right hS, ite_eq_right hT] at h
      split_ifs at h <;> simp_all

@[simp] theorem rowValue_alpha (m : ℕ) : rowValue (rowAlpha m) = fun _ => 1 := by
  funext j
  simp [rowValue]

@[simp] theorem rowValue_beta (m : ℕ) : rowValue (rowBeta m) = fun _ => 1 := by
  funext j
  simp [rowValue]

theorem rowValue_eq_one_iff {m : ℕ} (S : Finset (RowIndex m)) :
    rowValue S = (fun _ => 1) ↔ S=rowAlpha m ∨ S=rowBeta m := by
  constructor
  · intro he
    rw [← rowValue_alpha] at he
    rcases rowValue_collision S (rowAlpha m) he with h | ⟨h,_⟩ | ⟨h,_⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl) <;> simp

def unambiguousRows (m q : ℕ) : Finset (Finset (RowIndex m)) :=
  ((Finset.univ.powersetCard q).erase (rowAlpha m)).erase (rowBeta m)

theorem rowValue_injOn_unambiguous (m q : ℕ) :
    Set.InjOn (rowValue (m := m)) (unambiguousRows m q) := by
  intro S hS T hT he
  rcases rowValue_collision S T he with h | ⟨h,_⟩ | ⟨h,_⟩
  · exact h
  · exact False.elim ((Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).1 h)
  · exact False.elim ((Finset.mem_erase.mp hS).1 h)

theorem card_unambiguousRows (m q : ℕ) (hm : 2 ≤ m) :
    (unambiguousRows m q).card = m.choose q - (if q=1 then 1 else 0) -
      (if q=m-1 then 1 else 0) := by
  have hu : (Finset.univ : Finset (RowIndex m)).card=m := by simp; omega
  have hα : rowAlpha m ∈ (Finset.univ : Finset (RowIndex m)).powersetCard q ↔ q=1 := by
    simp [eq_comm]
  have hβ : rowBeta m ∈ ((Finset.univ : Finset (RowIndex m)).powersetCard q).erase (rowAlpha m) ↔ q=m-1 := by
    simp [Ne.symm (rowAlpha_ne_rowBeta m),eq_comm]
  unfold unambiguousRows
  by_cases hq : q=1 <;> by_cases hq' : q=m-1
  · rw [Finset.card_erase_of_mem (hβ.mpr hq'),
      Finset.card_erase_of_mem (hα.mpr hq), Finset.card_powersetCard, hu]
    simp only [ite_eq_left hq, ite_eq_left hq']
  · rw [Finset.erase_eq_of_notMem (mt hβ.mp hq'),
      Finset.card_erase_of_mem (hα.mpr hq), Finset.card_powersetCard, hu]
    simp only [ite_eq_left hq, ite_eq_right hq', Nat.sub_zero]
  · rw [Finset.card_erase_of_mem (hβ.mpr hq'),
      Finset.erase_eq_of_notMem (mt hα.mp hq), Finset.card_powersetCard, hu]
    simp only [ite_eq_right hq, ite_eq_left hq', Nat.sub_zero]
  · rw [Finset.erase_eq_of_notMem (mt hβ.mp hq'),
      Finset.erase_eq_of_notMem (mt hα.mp hq), Finset.card_powersetCard, hu]
    simp only [ite_eq_right hq, ite_eq_right hq', Nat.sub_zero]

end SumsetRanges
