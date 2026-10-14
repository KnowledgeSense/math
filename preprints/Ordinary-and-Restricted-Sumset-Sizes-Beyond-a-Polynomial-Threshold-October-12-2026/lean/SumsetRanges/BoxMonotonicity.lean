import SumsetRanges.IntervalBox
import SumsetRanges.LargeWeights
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open Finset
namespace SumsetRanges
open scoped BigOperators Classical

theorem box_antitone_of_steps {d : ℕ} (n : Fin d → ℕ) (f : (Fin d → ℕ) → ℤ)
    (hs : ∀x,InNatBox n x → ∀i,x i<n i → f (Function.update x i (x i+1))≤f x) :
    ∀x y,InNatBox n x → InNatBox n y → (∀i,x i≤y i) → f y≤f x := by
  suffices H : ∀N,∀x y, (∑i,y i)-(∑i,x i)=N → InNatBox n x → InNatBox n y →
      (∀i,x i≤y i) → f y≤f x by
    intro x y hx hy hxy
    exact H _ x y rfl hx hy hxy
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro x y hN hx hy hxy
    by_cases he : x=y
    · subst y
      exact le_refl _
    have hi : ∃i,x i<y i := by
      by_contra hn
      push Not at hn
      apply he
      funext i
      exact Nat.le_antisymm (hxy i) (hn i)
    obtain ⟨i,hi⟩ := hi
    let z := Function.update x i (x i+1)
    have hxz : ∀j,x j≤z j := by
      intro j
      by_cases hj : j=i
      · subst j; simp [z]
      · simp [z,Function.update_of_ne hj]
    have hzy : ∀j,z j≤y j := by
      intro j
      by_cases hj : j=i
      · subst j; simp [z]; omega
      · simpa [z,Function.update_of_ne hj] using hxy j
    have hz : InNatBox n z := fun j => (hzy j).trans (hy j)
    have hsum : (∑j,z j)=(∑j,x j)+1 := by
      simp only [z,Finset.sum_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
      have he : (∑j∈univ.erase i,x j)+x i=∑j,x j := Finset.sum_erase_add _ _ (mem_univ i)
      omega
    have hsumxy : (∑j,x j)≤∑j,y j := Finset.sum_le_sum (fun j _ => hxy j)
    have hsumzy : (∑j,z j)≤∑j,y j := Finset.sum_le_sum (fun j _ => hzy j)
    have hlt : (∑j,y j)-(∑j,z j)<N := by omega
    exact (ih _ hlt z y rfl hz hy hzy).trans (hs x hx i (hi.trans_le (hy i)))

end SumsetRanges
