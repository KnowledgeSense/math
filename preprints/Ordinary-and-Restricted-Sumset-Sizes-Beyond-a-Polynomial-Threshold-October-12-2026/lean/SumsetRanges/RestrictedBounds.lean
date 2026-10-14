import SumsetRanges.BalancedSubsets
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
namespace SumsetRanges

noncomputable def balancedSum (A : Finset ℤ) (q : ℕ) (hq : 0<q) (hqa : q≤A.card)
    (t : Fin (q*(A.card-q)+1)) : ℤ :=
  ∑ i : Fin q, A.orderEmbOfFin rfl ⟨balancedPoint q t.val i,
    balancedPoint_lt A.card q t.val hq hqa (Nat.le_of_lt_succ t.isLt) i⟩

theorem balancedSum_mem (A : Finset ℤ) (q : ℕ) (hq : 0<q) (hqa : q≤A.card)
    (t : Fin (q*(A.card-q)+1)) : balancedSum A q hq hqa t ∈ restrictedSums A q := by
  let f : Fin q → ℤ := fun i => A.orderEmbOfFin rfl ⟨balancedPoint q t.val i,
    balancedPoint_lt A.card q t.val hq hqa (Nat.le_of_lt_succ t.isLt) i⟩
  have hf : Function.Injective f := by
    intro i j he
    have hh := (A.orderEmbOfFin rfl).injective he
    have hv := congrArg Fin.val hh
    exact (balancedPoint_strictMono q t.val).injective hv
  refine mem_restrictedSums.mpr ⟨Finset.univ.image f,?_,?_,?_⟩
  · intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact A.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hf]
    simp
  · rw [Finset.sum_image hf.injOn]
    rfl

theorem balancedSum_strictMono (A : Finset ℤ) (q : ℕ) (hq : 0<q) (hqa : q≤A.card) :
    StrictMono (balancedSum A q hq hqa) := by
  intro t s hts
  have htv : t.val<s.val := hts
  have hmono (i : Fin q) : balancedPoint q t.val i≤balancedPoint q s.val i :=
    balancedPoint_mono_parameter q t.val s.val htv.le i
  have hstrict : ∃ i : Fin q, balancedPoint q t.val i<balancedPoint q s.val i := by
    by_contra! h
    have he := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun i _ => h i)
    rw [sum_balancedPoint q s.val hq,sum_balancedPoint q t.val hq] at he
    omega
  obtain ⟨i,hi⟩ := hstrict
  unfold balancedSum
  apply Finset.sum_lt_sum
  · intro j _
    exact (A.orderEmbOfFin rfl).monotone (hmono j)
  · refine ⟨i,Finset.mem_univ _,?_⟩
    exact (A.orderEmbOfFin rfl).strictMono hi

/-- The universal sharp lower bound for restricted sumsets in the integers. -/
theorem card_restrictedSums_lower (A : Finset ℤ) (q : ℕ) (hqa : q≤A.card) :
    q*(A.card-q)+1 ≤ (restrictedSums A q).card := by
  by_cases hq : q=0
  · subst q
    simp
  · have hq' := Nat.pos_of_ne_zero hq
    have hs : (Finset.univ.image (balancedSum A q hq' hqa)) ⊆ restrictedSums A q := by
      intro x hx
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hx
      exact balancedSum_mem A q hq' hqa t
    have hh := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ (balancedSum_strictMono A q hq' hqa).injective] at hh
    simpa using hh

theorem restrictedRange_bounds (h k : ℕ) (hhk : h≤k) :
    restrictedRange h k ⊆ Set.Icc (h*(k-h)+1) (k.choose h) := by
  rintro t ⟨A,hA,rfl⟩
  constructor
  · simpa [hA] using card_restrictedSums_lower A h (by omega)
  · simpa [hA] using card_restrictedSums_le A h

end SumsetRanges
