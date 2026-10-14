import MainTheorems.PreorderReciprocity.Basic
import Mathlib.Tactic.Ring

namespace ResearchMain.PreorderReciprocity

variable {E : Type*} [Fintype E] [Preorder E]

def addUnit (x : E → ℤ) : E → ℤ := fun e => x e + 1

def subUnit (x : E → ℤ) : E → ℤ := fun e => x e - 1

omit [Fintype E] [Preorder E] in
theorem addUnit_sum (x : E → ℤ) (I : Finset E) :
    ∑ e ∈ I, addUnit x e = (∑ e ∈ I, x e) + I.card := by
  simp [addUnit, Finset.sum_add_distrib]

omit [Fintype E] [Preorder E] in
theorem subUnit_sum (x : E → ℤ) (I : Finset E) :
    ∑ e ∈ I, subUnit x e = (∑ e ∈ I, x e) - I.card := by
  simp [subUnit, Finset.sum_sub_distrib]

omit [Fintype E] in
theorem addUnit_mem_iff (r s : ℤ) (x : E → ℤ) :
    StrictIntegerPoints r s (addUnit x) ↔ ClosedIntegerPoints (r - 1) (s - 1) x := by
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨fun e => by have := hp e; simp only [addUnit] at this; omega, ?_⟩
    intro I hI hIdeal
    have h := hb I hI hIdeal
    rw [addUnit_sum] at h
    have heq : (r - 1) * (I.card : ℤ) + (s - 1) =
        r * I.card + s - I.card - 1 := by ring
    rw [heq]
    omega
  · rintro ⟨hp, hb⟩
    refine ⟨fun e => by have := hp e; simp only [addUnit]; omega, ?_⟩
    intro I hI hIdeal
    have h := hb I hI hIdeal
    rw [addUnit_sum]
    have heq : (r - 1) * (I.card : ℤ) + (s - 1) =
        r * I.card + s - I.card - 1 := by ring
    rw [heq] at h
    omega

omit [Fintype E] in
theorem subUnit_mem_iff (r s : ℤ) (x : E → ℤ) :
    ClosedIntegerPoints (r - 1) (s - 1) (subUnit x) ↔ StrictIntegerPoints r s x := by
  have h := addUnit_mem_iff r s (subUnit x)
  have heq : addUnit (subUnit x) = x := by funext e; simp [addUnit, subUnit]
  rw [heq] at h
  exact h.symm

def integerPointTranslation (r s : ℤ) :
    {x : E → ℤ // ClosedIntegerPoints (r - 1) (s - 1) x} ≃
      {x : E → ℤ // StrictIntegerPoints r s x} where
  toFun x := ⟨addUnit x.1, (addUnit_mem_iff r s x.1).2 x.2⟩
  invFun x := ⟨subUnit x.1, (subUnit_mem_iff r s x.1).2 x.2⟩
  left_inv x := by apply Subtype.ext; funext e; simp [addUnit, subUnit]
  right_inv x := by apply Subtype.ext; funext e; simp [addUnit, subUnit]

theorem unique_strict_point_one_one {x : E → ℤ} :
    StrictIntegerPoints 1 1 x ↔ x = fun _ => 1 := by
  rw [← subUnit_mem_iff, sub_self, zero_parameters]
  constructor
  · intro h
    funext e
    have he := congrFun h e
    simp only [subUnit, Pi.zero_apply] at he
    omega
  · rintro rfl
    funext e
    simp [subUnit]

end ResearchMain.PreorderReciprocity
