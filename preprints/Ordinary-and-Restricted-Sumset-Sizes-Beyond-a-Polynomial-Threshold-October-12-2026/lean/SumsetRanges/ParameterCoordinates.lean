import SumsetRanges.CoordinateWidths
import SumsetRanges.IntervalBox

open Finset
namespace SumsetRanges
open scoped Classical

def parameterDimension (h : ℕ) := 2*(h-1)+1

def repetitionIndex (h m : ℕ) (hm : m∈Icc 2 h) : Fin (parameterDimension h) :=
  ⟨2*(h-m),by simp only [parameterDimension]; have := mem_Icc.mp hm; omega⟩
def sharedIndex (h m : ℕ) (hm : m∈Icc 2 h) : Fin (parameterDimension h) :=
  ⟨2*(h-m)+1,by simp only [parameterDimension]; have := mem_Icc.mp hm; omega⟩
def denseIndex (h : ℕ) : Fin (parameterDimension h) := ⟨2*(h-1),by simp [parameterDimension]⟩

def repetitionParameters (h : ℕ) (v : Fin (parameterDimension h) → ℕ) (m : ℕ) : ℕ :=
  if hm : m∈Icc 2 h then v (repetitionIndex h m hm) else 0

def sharedParameters (h : ℕ) (v : Fin (parameterDimension h) → ℕ) (m : ℕ) : ℕ :=
  if hm : m∈Icc 2 h then v (sharedIndex h m hm)+1 else 1

def parameterCaps (h R S N : ℕ) (i : Fin (parameterDimension h)) : ℕ :=
  if i=denseIndex h then N else if i.val%2=0 then R else S-1

@[simp] theorem repetitionParameters_at (h m : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hm : m∈Icc 2 h) : repetitionParameters h v m=v (repetitionIndex h m hm) := by
  simp [repetitionParameters,hm]
@[simp] theorem sharedParameters_at (h m : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hm : m∈Icc 2 h) : sharedParameters h v m=v (sharedIndex h m hm)+1 := by
  simp [sharedParameters,hm]

@[simp] theorem parameterCaps_repetition (h m R S N : ℕ) (hm : m∈Icc 2 h) :
    parameterCaps h R S N (repetitionIndex h m hm)=R := by
  have hd : repetitionIndex h m hm≠denseIndex h := by
    intro he
    have hv := congrArg Fin.val he
    simp only [repetitionIndex,denseIndex] at hv
    have := mem_Icc.mp hm
    omega
  simp only [parameterCaps,ite_eq_right hd]
  simp [repetitionIndex]
@[simp] theorem parameterCaps_shared (h m R S N : ℕ) (hm : m∈Icc 2 h) :
    parameterCaps h R S N (sharedIndex h m hm)=S-1 := by
  have hd : sharedIndex h m hm≠denseIndex h := by
    intro he
    have hv := congrArg Fin.val he
    simp only [sharedIndex,denseIndex] at hv
    omega
  simp only [parameterCaps,ite_eq_right hd]
  simp [sharedIndex,Nat.add_mod]
@[simp] theorem parameterCaps_dense (h R S N : ℕ) :
    parameterCaps h R S N (denseIndex h)=N := by simp [parameterCaps]

theorem parameterCoordinates_bounds (h R S N : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hS : 1≤S) (hv : InNatBox (parameterCaps h R S N) v) :
    (∀m∈Icc 2 h,repetitionParameters h v m≤R) ∧
    (∀m∈Icc 2 h,1≤sharedParameters h v m ∧ sharedParameters h v m≤S) ∧
    v (denseIndex h)≤N := by
  refine ⟨?_,?_,?_⟩
  · intro m hm
    rw [repetitionParameters_at h m v hm]
    simpa using hv (repetitionIndex h m hm)
  · intro m hm
    have hs := hv (sharedIndex h m hm)
    simp only [parameterCaps_shared] at hs
    rw [sharedParameters_at h m v hm]
    omega
  · simpa using hv (denseIndex h)

@[simp] theorem repetitionIndex_eq (h m n : ℕ) (hm : m∈Icc 2 h) (hn : n∈Icc 2 h) :
    repetitionIndex h m hm=repetitionIndex h n hn ↔ m=n := by
  simp only [repetitionIndex,Fin.mk.injEq]
  have := mem_Icc.mp hm
  have := mem_Icc.mp hn
  omega
@[simp] theorem sharedIndex_eq (h m n : ℕ) (hm : m∈Icc 2 h) (hn : n∈Icc 2 h) :
    sharedIndex h m hm=sharedIndex h n hn ↔ m=n := by
  simp only [sharedIndex,Fin.mk.injEq]
  have := mem_Icc.mp hm
  have := mem_Icc.mp hn
  omega
@[simp] theorem repetitionIndex_ne_shared (h m n : ℕ) (hm : m∈Icc 2 h) (hn : n∈Icc 2 h) :
    repetitionIndex h m hm≠sharedIndex h n hn := by
  simp only [repetitionIndex,sharedIndex,ne_eq,Fin.mk.injEq]
  omega
@[simp] theorem sharedIndex_ne_repetition (h m n : ℕ) (hm : m∈Icc 2 h) (hn : n∈Icc 2 h) :
    sharedIndex h m hm≠repetitionIndex h n hn := (repetitionIndex_ne_shared h n m hn hm).symm
@[simp] theorem repetitionIndex_ne_dense (h m : ℕ) (hm : m∈Icc 2 h) :
    repetitionIndex h m hm≠denseIndex h := by
  intro he
  have hv := congrArg Fin.val he
  simp only [repetitionIndex,denseIndex] at hv
  have := mem_Icc.mp hm
  omega
@[simp] theorem sharedIndex_ne_dense (h m : ℕ) (hm : m∈Icc 2 h) :
    sharedIndex h m hm≠denseIndex h := by
  intro he
  have hv := congrArg Fin.val he
  simp only [sharedIndex,denseIndex] at hv
  omega

@[simp] theorem repetitionParameters_update_repetition (h μ a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) (hm : μ∈Icc 2 h) :
    repetitionParameters h (Function.update v (repetitionIndex h μ hm) a)=
      Function.update (repetitionParameters h v) μ a := by
  funext m
  by_cases he : m=μ
  · subst m
    simp [repetitionParameters_at h μ _ hm]
  · by_cases hn : m∈Icc 2 h
    · simp [repetitionParameters,hn,he]
    · simp [repetitionParameters,hn,Function.update_of_ne he]

@[simp] theorem sharedParameters_update_repetition (h μ a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) (hm : μ∈Icc 2 h) :
    sharedParameters h (Function.update v (repetitionIndex h μ hm) a)=sharedParameters h v := by
  funext m
  by_cases hn : m∈Icc 2 h <;> simp [sharedParameters,hn]

@[simp] theorem repetitionParameters_update_shared (h μ a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) (hm : μ∈Icc 2 h) :
    repetitionParameters h (Function.update v (sharedIndex h μ hm) a)=repetitionParameters h v := by
  funext m
  by_cases hn : m∈Icc 2 h <;> simp [repetitionParameters,hn]

@[simp] theorem sharedParameters_update_shared (h μ a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) (hm : μ∈Icc 2 h) :
    sharedParameters h (Function.update v (sharedIndex h μ hm) a)=
      Function.update (sharedParameters h v) μ (a+1) := by
  funext m
  by_cases he : m=μ
  · subst m
    simp [sharedParameters_at h μ _ hm]
  · by_cases hn : m∈Icc 2 h
    · simp [sharedParameters,hn,he]
    · simp [sharedParameters,hn,Function.update_of_ne he]

@[simp] theorem repetitionParameters_update_dense (h a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) :
    repetitionParameters h (Function.update v (denseIndex h) a)=repetitionParameters h v := by
  funext m
  by_cases hn : m∈Icc 2 h <;> simp [repetitionParameters,hn]
@[simp] theorem sharedParameters_update_dense (h a : ℕ)
    (v : Fin (parameterDimension h) → ℕ) :
    sharedParameters h (Function.update v (denseIndex h) a)=sharedParameters h v := by
  funext m
  by_cases hn : m∈Icc 2 h <;> simp [sharedParameters,hn]

theorem parameterIndex_cases (h : ℕ) (hh : 2≤h) (i : Fin (parameterDimension h)) :
    i=denseIndex h ∨ ∃m,∃hm : m∈Icc 2 h,
      i=repetitionIndex h m hm ∨ i=sharedIndex h m hm := by
  by_cases he : i=denseIndex h
  · exact Or.inl he
  right
  have hi := i.isLt
  have hne : i.val≠2*(h-1) := by
    intro hv
    apply he
    exact Fin.ext hv
  have hm : h-i.val/2∈Icc 2 h := by
    simp only [mem_Icc]
    simp only [parameterDimension] at hi
    omega
  refine ⟨h-i.val/2,hm,?_⟩
  rcases Nat.mod_two_eq_zero_or_one i.val with hp | hp
  · left
    apply Fin.ext
    simp only [repetitionIndex]
    have := (mem_Icc.mp hm).1
    omega
  · right
    apply Fin.ext
    simp only [sharedIndex]
    have := (mem_Icc.mp hm).1
    omega

end SumsetRanges
