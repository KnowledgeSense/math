import MainTheorems.Tuza.Constructions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ResearchMain.Tuza

variable {K : Type*} [AddCommGroup K]

def reflectionGraph (t : K) : SimpleGraph K where
  Adj x y := x ≠ y ∧ x + y = t + t
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [add_comm] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance [DecidableEq K] (t : K) : DecidableRel (reflectionGraph t).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ + _ = t + t))

theorem reflection_adj_unique {t x y z : K}
    (hy : (reflectionGraph t).Adj x y) (hz : (reflectionGraph t).Adj x z) : y = z :=
  add_left_cancel (hy.2.trans hz.2.symm)

theorem reflection_factor_unique
    (hd : Function.Injective (fun x : K => x + x)) {t s x y : K}
    (ht : (reflectionGraph t).Adj x y) (hs : (reflectionGraph s).Adj x y) : t = s :=
  hd (ht.2.symm.trans hs.2)

variable [Fintype K] [DecidableEq K]

theorem reflection_degree (hd : Function.Injective (fun x : K => x + x)) (t x : K) :
    (reflectionGraph t).degree x = if x = t then 0 else 1 := by
  by_cases hx : x = t
  · subst x
    simp only [ite_true]
    apply SimpleGraph.IsIsolated.degree_eq_zero
    intro y hy
    have he : y = t := add_left_cancel hy.2
    exact hy.1 he.symm
  · rw [ite_eq_right hx]
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    have hne : x ≠ t + t - x := by
      intro hh
      apply hx
      apply hd
      calc
        x + x = (t + t - x) + x := congrArg (fun z => z + x) hh
        _ = t + t := sub_add_cancel _ _
    refine ⟨t + t - x, ⟨hne, by abel⟩, ?_⟩
    intro y hy
    calc
      y = (x + y) - x := by abel
      _ = t + t - x := congrArg (fun z => z - x) hy.2

theorem reflection_card (hd : Function.Injective (fun x : K => x + x)) (t : K) :
    2 * (reflectionGraph t).edgeFinset.card = Fintype.card K - 1 := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [reflection_degree hd]
  simp [Finset.sum_ite, Finset.filter_ne']

theorem zmod_double_injective {q : ℕ} (hq : Odd q) :
    Function.Injective (fun x : ZMod q => x + x) := by
  have hunit : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr hq.coprime_two_left
  intro x y h
  exact hunit.mul_left_injective (by simpa [mul_two] using h)

end ResearchMain.Tuza
