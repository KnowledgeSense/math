import SumsetRanges.OrdinarySparseSet
import SumsetRanges.OrdinaryStepBounds

open Finset
namespace SumsetRanges

theorem ordinaryNonfreeSize_bound (h c : ℕ) (r u : ℕ → ℕ) (hh : 2≤h)
    (hc : (32*h^3)^10≤c) (hr : ∀m∈Icc 2 (h-1),r m≤repetitionCap c)
    (hu : ∀m∈Icc 2 (h-1),u m≤sharedCap c) :
    4*h*ordinaryNonfreeSize h r u≤c := by
  have hpos := large_caps_positive (by omega : 1≤h) hc
  have hcpos := (large_c_elementary (by omega : 1≤h) hc).1
  have hs := sharedCap_le_repetitionCap (by omega : 1≤c)
  have hn : ordinaryNonfreeSize h r u≤h*(5*repetitionCap c) := by
    calc
      _ ≤ ∑_m∈Icc 2 (h-1),5*repetitionCap c := by
        apply Finset.sum_le_sum
        intro m hm
        have hrm := hr m hm
        have hum := hu m hm
        omega
      _ = (h-2)*(5*repetitionCap c) := by simp [Nat.card_Icc]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.sub_le h 2)
  have hb := repetition_nonfree_bound (by omega : 1≤h) hc
  have hm := Nat.mul_le_mul_left (4*h) hn
  have hp : 4*h*(h*(5*repetitionCap c))≤8*h*(3*h^2*repetitionCap c) := by
    have hbase : 20*h^2≤24*h^3 := by nlinarith [sq_nonneg (h:ℤ)]
    have he := Nat.mul_le_mul_right (repetitionCap c) hbase
    nlinarith
  exact hm.trans (hp.trans hb)

theorem ordinaryNonfreeSize_step_r (h m : ℕ) (r u : ℕ → ℕ) (hm : m∈Icc 2 (h-1)) :
    ordinaryNonfreeSize h (Function.update r m (r m+1)) u=ordinaryNonfreeSize h r u+2 := by
  calc
    _ = ordinaryNonfreeSize h r u+∑j∈Icc 2 (h-1),if j=m then 2 else 0 := by
      unfold ordinaryNonfreeSize
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=m
      · subst j; simp only [Function.update_self,ite_true]; ring
      · simp [hj]
    _ = _ := by simp [hm]

theorem ordinaryNonfreeSize_step_u (h m : ℕ) (r u : ℕ → ℕ) (hm : m∈Icc 2 (h-1)) :
    ordinaryNonfreeSize h r (Function.update u m (u m+1))=ordinaryNonfreeSize h r u+2 := by
  calc
    _ = ordinaryNonfreeSize h r u+∑j∈Icc 2 (h-1),if j=m then 2 else 0 := by
      unfold ordinaryNonfreeSize
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=m
      · subst j; simp only [Function.update_self,ite_true]; ring
      · simp [hj]
    _ = _ := by simp [hm]

theorem ordinary_cubic_bound (h c : ℕ) (hh : 1≤h) (hc : (32*h^3)^10≤c) : 2*h^3≤c := by
  have hp : 0<32*h^3 := by positivity
  have he : 32*h^3≤(32*h^3)^10 := by
    simpa using Nat.pow_le_pow_right hp (by omega : 1≤10)
  omega

theorem ordinary_linear_box_bound (h c m : ℕ) (r u : ℕ → ℕ) (hh : 2≤h)
    (hc : (32*h^3)^10≤c) (hm : m∈Finset.Icc 2 (h-1))
    (hr : ∀j∈Finset.Icc 2 (h-1),r j≤repetitionCap c)
    (hu : ∀j∈Finset.Icc 2 (h-1),u j≤sharedCap c) (hi : r m<repetitionCap c) :
    4*h*(ordinaryNonfreeSize h r u+2)≤c := by
  have he := ordinaryNonfreeSize_bound h c (Function.update r m (r m+1)) u hh hc
    (fun j hj => by by_cases hjm : j=m; subst j; simp; omega; simpa [hjm] using hr j hj) hu
  rw [ordinaryNonfreeSize_step_r h m r u hm] at he
  exact he

theorem ordinary_shared_box_bound (h c m : ℕ) (r u : ℕ → ℕ) (hh : 2≤h)
    (hc : (32*h^3)^10≤c) (hm : m∈Finset.Icc 2 (h-1))
    (hr : ∀j∈Finset.Icc 2 (h-1),r j≤repetitionCap c)
    (hu : ∀j∈Finset.Icc 2 (h-1),u j≤sharedCap c) (hi : u m<sharedCap c) :
    4*h*(ordinaryNonfreeSize h r u+2)≤c := by
  have he := ordinaryNonfreeSize_bound h c r (Function.update u m (u m+1)) hh hc hr
    (fun j hj => by by_cases hjm : j=m; subst j; simp; omega; simpa [hjm] using hu j hj)
  rw [ordinaryNonfreeSize_step_u h m r u hm] at he
  exact he

end SumsetRanges
