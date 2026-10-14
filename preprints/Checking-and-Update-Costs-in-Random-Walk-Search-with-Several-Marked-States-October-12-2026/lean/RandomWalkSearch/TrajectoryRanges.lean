import RandomWalkSearch.Consecutive
import RandomWalkSearch.LazyGeometry
import Mathlib.Data.Finset.Range

/-! # Domination of adaptively allocated trajectories by full independent tapes -/

namespace RandomWalkSearch.Cycle
open scoped BigOperators

variable {k : ℕ}

theorem walkPosition_eq_integerPosition (w : ℕ → Fin 4) (n : ℕ) :
    walkPosition w n = LazyWalk.integerPosition n (LazyWalk.prefixTape n w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [walkPosition_succ, LazyWalk.prefixTape, LazyWalk.integerPosition,
      LazyWalk.integerRun] using congrArg (fun x : ℤ => x + (increment (w n)).value) ih

/-- The full-horizon integer-range arc, whether or not this trajectory is ever
started, and whether or not the algorithm actually consumes the full tape. -/
def trajectoryArc (z : Vertex k) (w : ℕ → Fin 4) (T : ℕ) : Finset (Vertex k) :=
  arc (z + (LazyWalk.integerLower T (LazyWalk.prefixTape T w) : ℤ))
    (LazyWalk.integerRange T (LazyWalk.prefixTape T w) + 1)

theorem walkPosition_mem_trajectoryArc (z : Vertex k) (w : ℕ → Fin 4)
    (T t : ℕ) (ht : t ≤ T) :
    z + (walkPosition w t : ℤ) ∈ trajectoryArc z w T := by
  rw [walkPosition_eq_integerPosition]
  have hb := LazyWalk.prefix_position_bounds w T t ht
  let x := LazyWalk.integerPosition t (LazyWalk.prefixTape t w)
  let lo := LazyWalk.integerLower T (LazyWalk.prefixTape T w)
  let hi := LazyWalk.integerUpper T (LazyWalk.prefixTape T w)
  have hxl : 0 ≤ x - lo := sub_nonneg.mpr hb.1
  have hhl : 0 ≤ hi - lo := sub_nonneg.mpr (LazyWalk.integerLower_le_upper ..)
  apply Finset.mem_image.mpr
  refine ⟨(x-lo).toNat, Finset.mem_range.mpr ?_, ?_⟩
  · change (x-lo).toNat < (hi-lo).toNat + 1
    have hle : (x-lo).toNat ≤ (hi-lo).toNat := Int.toNat_le_toNat (by omega)
    omega
  · have hx : ((x-lo).toNat : ℤ) = x-lo := Int.toNat_of_nonneg hxl
    change z + (lo : Vertex k) + ((x-lo).toNat : Vertex k) = z + (x : Vertex k)
    rw [← Int.cast_natCast, hx, Int.cast_sub]
    ring

/-- Expanding an arc one vertex at a time charges exactly one new interval
translate for each new vertex after the first. -/
theorem exposure_arc_succ_le (d : ℕ) (x : Vertex k) (s : ℕ) :
    (exposure d (arc x (s + 1))).card ≤ d + s := by
  induction s with
  | zero => simpa [arc, exposure] using card_intervalStarts_le (k := k) d x
  | succ s ih =>
    have harc : arc x (s+1+1) = insert (x + ((s+1 : ℕ) : Vertex k)) (arc x (s+1)) := by
      simp [arc, Finset.range_add_one]
    rw [harc]
    have hx : x + (s : Vertex k) ∈ arc x (s+1) :=
      Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩
    have ha : adjacent (x + (s : Vertex k)) (x + ((s+1 : ℕ) : Vertex k)) := by
      right; right; push_cast; ring
    exact (exposure_update d _ _ _ hx ha).trans (by omega)

/-- Actual adaptive allocation does not escape the full-horizon tape arcs. -/
theorem run_visited_subset_trajectoryArcs (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (he : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Extends (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (hb : ∀ n, (run p (lazyTapes z w) o n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) o n).updates ≤ T) (n : ℕ) :
    (run p (lazyTapes z w) o n).visited ⊆
      (Finset.range b).biUnion (fun i => trajectoryArc (z i) (w i) T) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hactive
      have he' := he n (Bool.eq_false_iff.mpr hactive)
      have hb' := hb (n+1)
      have hT' := hT (n+1)
      simp only [run_succ, step, hactive, Bool.false_eq_true, ite_false] at hb' hT'
      cases ha : p (run p (lazyTapes z w) o n) with
      | setup =>
        simp only [respond, History.visited_cons_setup, Finset.insert_subset_iff]
        refine ⟨?_, ih⟩
        have hs : (run p (lazyTapes z w) o n).setups < b := by
          simp only [ha, respond, History.setups, List.countP_cons, Event.isSetup, ite_true] at hb'
          change (run p (lazyTapes z w) o n).setups + 1 ≤ b at hb'
          omega
        apply Finset.mem_biUnion.mpr
        refine ⟨(run p (lazyTapes z w) o n).setups, Finset.mem_range.mpr hs, ?_⟩
        simpa only [walkPosition_zero, Int.cast_zero, add_zero, lazyTapes] using
          walkPosition_mem_trajectoryArc (z (run p (lazyTapes z w) o n).setups)
            (w (run p (lazyTapes z w) o n).setups) T 0 (Nat.zero_le T)
      | update i x =>
        have he'' : i < (run p (lazyTapes z w) o n).setups ∧
            (run p (lazyTapes z w) o n).endpoint i = some x := by simpa [ha, Extends] using he'
        have hx : x = z i + (walkPosition (w i)
            ((run p (lazyTapes z w) o n).trajectoryUpdates i) : ℤ) :=
          Option.some.inj (he''.2.symm.trans (run_endpoint p z w o he n i he''.1))
        have ht : (run p (lazyTapes z w) o n).trajectoryUpdates i + 1 ≤ T := by
          have hle := History.trajectoryUpdates_le_updates i (run p (lazyTapes z w) o n)
          simp only [ha, respond, History.updates, List.countP_cons, Event.isUpdate, ite_true] at hT'
          change (run p (lazyTapes z w) o n).updates + 1 ≤ T at hT'
          omega
        simp only [respond, History.visited_cons_update, Finset.insert_subset_iff]
        refine ⟨?_, ih⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_range.mpr (he''.1.trans_le (hb n)), ?_⟩
        have hm := walkPosition_mem_trajectoryArc (z i) (w i) T
          ((run p (lazyTapes z w) o n).trajectoryUpdates i + 1) ht
        simpa only [lazyTapes, hx, walkPosition_succ, Int.cast_add, add_assoc] using hm
      | check x => simpa [respond] using ih
      | output x => simpa [respond] using ih
      | think => simpa [respond] using ih

variable [NeZero (N k)]

theorem visitedEver_subset_trajectoryArcs (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (he : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Extends (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (hb : ∀ n, (run p (lazyTapes z w) o n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) o n).updates ≤ T) :
    visitedEver p (lazyTapes z w) o ⊆
      (Finset.range b).biUnion (fun i => trajectoryArc (z i) (w i) T) := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_ever _ _).mp hx
  exact run_visited_subset_trajectoryArcs b T p z w o he hb hT n hn

/-- Total full-tape ranges, independent of how updates are allocated. -/
def rangeSum (b T : ℕ) (w : ℕ → ℕ → Fin 4) : ℕ :=
  ∑ i ∈ Finset.range b, LazyWalk.integerRange T (LazyWalk.prefixTape T (w i))

theorem visitedEver_card_le_ranges (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (he : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Extends (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (hb : ∀ n, (run p (lazyTapes z w) o n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) o n).updates ≤ T) :
    (visitedEver p (lazyTapes z w) o).card ≤ b + rangeSum b T w := by
  calc
    _ ≤ ((Finset.range b).biUnion (fun i => trajectoryArc (z i) (w i) T)).card :=
      Finset.card_le_card (visitedEver_subset_trajectoryArcs b T p z w o he hb hT)
    _ ≤ ∑ i ∈ Finset.range b, (trajectoryArc (z i) (w i) T).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.range b, (LazyWalk.integerRange T (LazyWalk.prefixTape T (w i)) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_image_le.trans_eq (Finset.card_range _)
    _ = b + rangeSum b T w := by simp [rangeSum, Finset.sum_add_distrib, Nat.add_comm]

theorem visitedEver_exposure_le_ranges (d b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (he : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Extends (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (hb : ∀ n, (run p (lazyTapes z w) o n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) o n).updates ≤ T) :
    (exposure d (visitedEver p (lazyTapes z w) o)).card ≤ d * b + rangeSum b T w := by
  have hsub : exposure d (visitedEver p (lazyTapes z w) o) ⊆
      (Finset.range b).biUnion (fun i => exposure d (trajectoryArc (z i) (w i) T)) := by
    intro a ha
    obtain ⟨x, hx, hax⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp
      (visitedEver_subset_trajectoryArcs b T p z w o he hb hT hx)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr ⟨x, hxi, hax⟩⟩
  calc
    _ ≤ ((Finset.range b).biUnion (fun i => exposure d (trajectoryArc (z i) (w i) T))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range b, (exposure d (trajectoryArc (z i) (w i) T)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.range b, (d + LazyWalk.integerRange T (LazyWalk.prefixTape T (w i))) :=
      Finset.sum_le_sum (fun i _ => exposure_arc_succ_le d _ _)
    _ = d * b + rangeSum b T w := by
      simp [rangeSum, Finset.sum_add_distrib, Nat.mul_comm]

/-- Hard consecutive counting is a consequence of actual trajectory geometry. -/
theorem hard_consecutive_count (b T Q : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hl : ∀ n, (run p (lazyTapes z w) negativeOracle n).halted = false →
      Local (run p (lazyTapes z w) negativeOracle n) (p (run p (lazyTapes z w) negativeOracle n)))
    (he : ∀ n, (run p (lazyTapes z w) negativeOracle n).halted = false →
      Extends (run p (lazyTapes z w) negativeOracle n) (p (run p (lazyTapes z w) negativeOracle n)))
    (hb : ∀ n, (run p (lazyTapes z w) negativeOracle n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) negativeOracle n).updates ≤ T)
    (hQ : ∀ n, (run p (lazyTapes z w) negativeOracle n).checks ≤ Q) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (Q + 1) * k ^ 6 + (b + 1) * D k + rangeSum b T w := by
  have hI := visitedEver_exposure_le_ranges (D k) b T p z w negativeOracle he hb hT
  have hG := Finset.card_biUnion_le_card_mul (checkedEver p (lazyTapes z w) negativeOracle)
    progressionStarts (k ^ 6) (fun x _ => card_progressionStarts_le x)
  have hO := Finset.card_biUnion_le_card_mul (outputsEver p (lazyTapes z w) negativeOracle)
    markedStarts (D k + k ^ 6) (fun x _ => card_markedStarts_le x)
  have hG' := Nat.mul_le_mul_right (k ^ 6)
    (checkedEver_card_le Q p (lazyTapes z w) negativeOracle hQ)
  have hO' := Nat.mul_le_mul_right (D k + k ^ 6)
    (outputsEver_card_le p (lazyTapes z w) negativeOracle)
  have hu := (Finset.card_le_card (successfulTranslates_local_subset p (lazyTapes z w) hl)).trans
    (Finset.card_union_le ..)
  have hu' := Finset.card_union_le
    (exposure (D k) (visitedEver p (lazyTapes z w) negativeOracle))
    ((checkedEver p (lazyTapes z w) negativeOracle).biUnion progressionStarts)
  nlinarith

end RandomWalkSearch.Cycle
