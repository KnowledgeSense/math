import MainTheorems.Chores.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype E] [DecidableEq A]

def cheapCount (M : TwoCheapModel A E) (f : E → A) (a b : A) : ℕ :=
  ((bundle f b).filter (M.Cheap a)).card

def expensiveCount (M : TwoCheapModel A E) (f : E → A) (a b : A) : ℕ :=
  ((bundle f b).filter (fun e => ¬M.Cheap a e)).card

theorem cheap_add_expensive (M : TwoCheapModel A E) (f : E → A) (a b : A) :
    cheapCount M f a b + expensiveCount M f a b = (bundle f b).card := by
  exact Finset.card_filter_add_card_filter_not (s := bundle f b) (M.Cheap a)

theorem bundleCost_eq_counts (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (a b : A) :
    bundleCost M r a (bundle f b) = cheapCount M f a b + r * expensiveCount M f a b := by
  simp [bundleCost, itemCost, Finset.sum_ite, cheapCount, expensiveCount, mul_comm]

theorem bundleCost_eq_size (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (a b : A) :
    bundleCost M r a (bundle f b) = (bundle f b).card + (r - 1) * expensiveCount M f a b := by
  rw [bundleCost_eq_counts]
  have h := congrArg (fun n : ℕ => (n : ℝ)) (cheap_add_expensive M f a b)
  push_cast at h
  nlinarith

theorem ownCheap_iff_count (M : TwoCheapModel A E) (f : E → A) (a : A) :
    OwnCheap M f a ↔ 0 < cheapCount M f a a := by
  simp [OwnCheap, cheapCount, Finset.card_pos, Finset.filter_nonempty_iff]

theorem threshold_eq_counts (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (a : A)
    (ha : (bundle f a).Nonempty) :
    threshold M r f a =
      if 0 < cheapCount M f a a then
        (bundle f a).card - 1 + (r - 1) * expensiveCount M f a a
      else r * ((bundle f a).card - 1) := by
  rw [threshold, ite_eq_left ha]
  by_cases hc : OwnCheap M f a
  · rw [ite_eq_left hc, ite_eq_left ((ownCheap_iff_count M f a).mp hc), bundleCost_eq_size]
    ring
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((ownCheap_iff_count M f a).mpr h))]
    have hz : cheapCount M f a a = 0 := by
      have := (ownCheap_iff_count M f a).not.mp hc
      omega
    have hsize := cheap_add_expensive M f a a
    rw [bundleCost_eq_counts, hz]
    simp only [Nat.cast_zero, zero_add]
    have he : (expensiveCount M f a a : ℝ) = (bundle f a).card := by
      exact_mod_cast (by omega : expensiveCount M f a a = (bundle f a).card)
    rw [he]
    ring

theorem small_instance_efx [Fintype A] [DecidableEq E] (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    (hcard : Fintype.card E ≤ Fintype.card A) : ∃ f : E → A, EFX M r f := by
  classical
  let f : E → A := fun e => (Fintype.equivFin A).symm
    (Fin.castLE hcard (Fintype.equivFin E e))
  refine ⟨f, injective_allocation_efx M hr ?_⟩
  intro e d hed
  have hfin := (Fintype.equivFin A).symm.injective hed
  apply (Fintype.equivFin E).injective
  apply Fin.ext
  simpa only [Fin.val_castLE] using congrArg (fun x : Fin (Fintype.card A) => x.val) hfin

end ResearchMain.Chores
