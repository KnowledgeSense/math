import MeanMaximumForests.CoefficientRecursion
import MeanMaximumForests.CoefficientTail

/-! The lower coefficient ratio bound is proved directly by deleting a leaf.
No average-degree or external analytic theorem is assumed. -/
namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The lower tail inequality for every finite induced subforest. -/
theorem coefficient_extension_lower (hG : G.IsAcyclic) (s : Finset V) (k : ℕ) :
    ((s.card : ℝ) - 3 * k) * independentSetCoefficient G s k ≤
      ((k : ℝ) + 1) * independentSetCoefficient G s (k + 1) := by
  classical
  revert k
  refine Finset.strongInductionOn s ?_
  intro s ih k
  cases k with
  | zero => simp [coefficient_zero, coefficient_one]
  | succ k =>
    by_cases hs : s.Nonempty
    · obtain ⟨r, hr, huniq⟩ := exists_leaf_within G hG s hs
      have hH := ih (s.erase r) (erase_ssubset hr) (k + 1)
      have hrec1 := independentSetCoefficient_recursion G s r hr k
      have hrec2 := independentSetCoefficient_recursion G s r hr (k + 1)
      have hcardH : ((s.erase r).card : ℝ) + 1 = s.card := by
        exact_mod_cast card_erase_add_one hr
      by_cases he : ∃ v ∈ s.erase r, G.Adj r v
      · obtain ⟨v, hv, hadj⟩ := he
        have hcomp : compatibleVertices G s r = (s.erase r).erase v := by
          ext w
          by_cases hw : w ∈ s
          · have heq : G.Adj r w ↔ w = v := by
              constructor
              · intro h
                exact huniq w hw v (mem_of_mem_erase hv) h hadj
              · rintro rfl
                exact hadj
            simp only [mem_compatibleVertices, mem_erase, hw, and_true, heq]
            tauto
          · simp [mem_compatibleVertices, mem_erase, hw]
        rw [hcomp] at hrec1 hrec2
        have hK := ih ((s.erase r).erase v)
          (Finset.ssubset_of_subset_of_ssubset (erase_subset _ _) (erase_ssubset hr)) k
        have hrecH := independentSetCoefficient_recursion G (s.erase r) v hv k
        have hLK : compatibleVertices G (s.erase r) v ⊆ (s.erase r).erase v := by
          intro w hw
          obtain ⟨hwv, hw, _⟩ := (mem_compatibleVertices G).mp hw
          exact mem_erase.mpr ⟨hwv, hw⟩
        have hmono : (independentSetCoefficient G (compatibleVertices G (s.erase r) v) k : ℝ) ≤
            independentSetCoefficient G ((s.erase r).erase v) k := by
          exact_mod_cast independentSetCoefficient_mono G hLK k
        have hcardK : (((s.erase r).erase v).card : ℝ) + 1 = (s.erase r).card := by
          exact_mod_cast card_erase_add_one hv
        have hr1 : (independentSetCoefficient G s (k + 1) : ℝ) =
            independentSetCoefficient G (s.erase r) (k + 1) +
              independentSetCoefficient G ((s.erase r).erase v) k := by exact_mod_cast hrec1
        have hr2 : (independentSetCoefficient G s (k + 1 + 1) : ℝ) =
            independentSetCoefficient G (s.erase r) (k + 1 + 1) +
              independentSetCoefficient G ((s.erase r).erase v) (k + 1) := by exact_mod_cast hrec2
        have hrH : (independentSetCoefficient G (s.erase r) (k + 1) : ℝ) =
            independentSetCoefficient G ((s.erase r).erase v) (k + 1) +
              independentSetCoefficient G (compatibleVertices G (s.erase r) v) k := by
          exact_mod_cast hrecH
        simp only [Nat.cast_add, Nat.cast_one] at hH ⊢
        nlinarith
      · have hcomp : compatibleVertices G s r = s.erase r := by
          ext w
          simp only [mem_compatibleVertices, mem_erase]
          constructor
          · tauto
          · rintro ⟨hwr, hws⟩
            exact ⟨hwr, hws, fun h => he ⟨w, mem_erase.mpr ⟨hwr, hws⟩, h⟩⟩
        rw [hcomp] at hrec1 hrec2
        have hK := ih (s.erase r) (erase_ssubset hr) k
        have hr1 : (independentSetCoefficient G s (k + 1) : ℝ) =
            independentSetCoefficient G (s.erase r) (k + 1) +
              independentSetCoefficient G (s.erase r) k := by exact_mod_cast hrec1
        have hr2 : (independentSetCoefficient G s (k + 1 + 1) : ℝ) =
            independentSetCoefficient G (s.erase r) (k + 1 + 1) +
              independentSetCoefficient G (s.erase r) (k + 1) := by exact_mod_cast hrec2
        simp only [Nat.cast_add, Nat.cast_one] at hH ⊢
        nlinarith [Nat.cast_nonneg (α := ℝ) (independentSetCoefficient G (s.erase r) k)]
    · have hse : s = ∅ := not_nonempty_iff_eq_empty.mp hs
      subst s
      have hz : independentSetCoefficient G ∅ (k + 1) = 0 :=
        coefficient_eq_zero_of_gt G ∅ (k + 1) (by simp)
      rw [hz, Nat.cast_zero, mul_zero]
      positivity
/-- The initial coefficient tail forces every weak peak beyond `(n-1)/4`. -/
theorem weakLocalPeak_lower [Fintype V] (hG : G.IsAcyclic) {k : ℕ}
    (hk : WeakLocalPeak G k) : Fintype.card V ≤ 4 * k + 1 := by
  have hp : (0 : ℝ) < independentSetCoefficient G univ k := by
    apply Nat.cast_pos.mpr
    apply (coefficient_pos_iff_le G univ k).mpr
    simpa only [independenceNumber_univ] using hk.1
  have hl := coefficient_extension_lower G hG univ k
  rw [card_univ] at hl
  have hr : (independentSetCoefficient G univ (k + 1) : ℝ) ≤
      independentSetCoefficient G univ k := by exact_mod_cast hk.2.2
  have hm := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ k + 1)
  have hn : (Fintype.card V : ℝ) ≤ 4 * k + 1 := by nlinarith
  exact_mod_cast hn

end MeanMaximumForests
