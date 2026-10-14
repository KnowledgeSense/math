import CokernelPolynomiality.IntervalMorphisms
import Mathlib.Algebra.Exact.Basic

noncomputable section
namespace CokernelPolynomiality

theorem intervalProjection_surjective (c b d i : ℕ) (hcb : c ≤ b+1) :
    Function.Surjective (intervalComponent c d (b+1) d i) := by
  intro y
  by_cases ht : intervalActive (b+1) d i
  · have hs : intervalActive c d i := by unfold intervalActive at *; omega
    refine ⟨⟨y.val,by simp [intervalSpace,hs]⟩,?_⟩
    apply Subtype.ext
    simp [intervalComponent_val,ht]
  · refine ⟨0,?_⟩
    rw [map_zero]
    apply Subtype.ext
    exact (intervalSpace_val_zero ht y).symm

theorem intervalCokernel_exact (a b c d i : ℕ) (hac : a ≤ c) :
    Function.Exact (intervalComponent a b c d i) (intervalComponent c d (b+1) d i) := by
  intro y
  constructor
  · intro hy
    by_cases ht : intervalActive c d i
    · by_cases hi : i ≤ b
      · have hs : intervalActive a b i := ⟨by have := ht.1; omega,hi⟩
        refine ⟨⟨y.val,by simp [intervalSpace,hs]⟩,?_⟩
        apply Subtype.ext
        simp [intervalComponent_val,ht]
      · have hk : intervalActive (b+1) d i := ⟨by omega,ht.2⟩
        have hz := congrArg Subtype.val hy
        simp only [intervalComponent_val,ite_eq_left hk,ZeroMemClass.coe_zero] at hz
        refine ⟨0,?_⟩
        rw [map_zero]
        exact (Subtype.ext hz).symm
    · refine ⟨0,?_⟩
      rw [map_zero]
      apply Subtype.ext
      exact (intervalSpace_val_zero ht y).symm
  · rintro ⟨x,rfl⟩
    apply Subtype.ext
    simp only [intervalComponent_val,ZeroMemClass.coe_zero]
    by_cases hk : intervalActive (b+1) d i
    · have hs : ¬intervalActive a b i := by unfold intervalActive at *; omega
      simp [hk,intervalSpace_val_zero hs x]
    · simp [hk]

end CokernelPolynomiality
