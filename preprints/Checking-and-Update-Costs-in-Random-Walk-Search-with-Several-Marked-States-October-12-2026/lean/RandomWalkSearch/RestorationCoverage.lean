import RandomWalkSearch.RestorationPolicy

noncomputable section
namespace RandomWalkSearch.Cycle
open EndpointPolicy LazyWalk

variable {k : ℕ}

/-- Every frontier position from zero through the number of actual right symbols was visited. -/
theorem frontierTrail_contains (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n j : ℕ)
    (hj : j ≤ rightCountStream (w 0) n) : z 0 + (j : Vertex k) ∈ (frontierTrail z w n).visited := by
  induction n with
  | zero =>
    have he : j = 0 := by simpa [rightCountStream, rightCount] using hj
    subst j
    simp [frontierTrail]
  | succ n ih =>
    rw [frontierTrail, History.visited_cons_update]
    by_cases hq : w 0 n = 1
    · have hj' : j ≤ rightCountStream (w 0) n + 1 := by
        simpa [rightCountStream, rightCount, prefixTape, hq] using hj
      by_cases hjold : j ≤ rightCountStream (w 0) n
      · exact Finset.mem_insert_of_mem (ih hjold)
      · have he : j = rightCountStream (w 0) n + 1 := by omega
        apply Finset.mem_insert.mpr
        left
        simp [he, frontierTarget, frontierPosition, hq, increment, Increment.value, add_assoc]
    · apply Finset.mem_insert_of_mem
      apply ih
      simpa [rightCountStream, rightCount, prefixTape, hq] using hj

theorem frontierTrail_arc (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n q : ℕ)
    (hq : 0 < q) (hc : q - 1 ≤ rightCountStream (w 0) n) :
    arc (z 0) q ⊆ (frontierTrail z w n).visited := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact frontierTrail_contains z w n j (by have := Finset.mem_range.mp hj; omega)

theorem arc_covers_phase (q : ℕ) [NeZero q] (hq : q ∣ N k) (z : Vertex k) :
    Covers (phase q hq) (arc z q) := by
  intro c
  let j := (c - phase q hq z).val
  refine ⟨z + (j : Vertex k), Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (ZMod.val_lt _), rfl⟩, ?_⟩
  rw [map_add, map_natCast]
  change phase q hq z + ((c - phase q hq z).val : ZMod q) = c
  rw [ZMod.natCast_zmod_val]
  abel

theorem covers_phase_frontier (q : ℕ) [NeZero q] (hq : q ∣ N k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ)
    (hc : q - 1 ≤ rightCountStream (w 0) n) :
    Covers (phase q hq) (frontierTrail z w n).visited := by
  intro c
  obtain ⟨x, hx, hp⟩ := arc_covers_phase q hq (z 0) c
  exact ⟨x, frontierTrail_arc z w n q (NeZero.pos q) hc hx, hp⟩

theorem frontier_visits_all [NeZero (N k)] (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ)
    (hc : N k - 1 ≤ rightCountStream (w 0) n) :
    (frontierTrail z w n).visited = Finset.univ := by
  have hp := covers_phase_frontier (N k) (dvd_refl _) z w n hc
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨y, hy, he⟩ := hp x
  have hyx : y = x := by simpa [phase, ZMod.cast_id] using he
  exact hyx ▸ hy

theorem restorationCollect_finishes (hN : 2 < N k) (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k)) (t Q : ℕ)
    (hc : cover (frontierTrail z w t).visited)
    (hmark : ∀ v, cover v → ∃ x ∈ tests v, o x = true)
    (hbound : ∀ v, cover v → (tests v).card ≤ Q) :
    Succeeds (restorationCollect cover tests) (lazyTapes z w) o ∧
      updateCost (restorationCollect cover tests) (lazyTapes z w) o ≤ t ∧
      checkCost (restorationCollect cover tests) (lazyTapes z w) o ≤ Q := by
  classical
  have he : ∃ j, cover (frontierTrail z w j).visited := ⟨t, hc⟩
  let j := Nat.find he
  have hj : j ≤ t := Nat.find_min' he hc
  have hcj : cover (frontierTrail z w j).visited := Nat.find_spec he
  have hr : Reachable (restorationCollect cover tests) (lazyTapes z w) o (frontierTrail z w j) :=
    ⟨j + 1, restoration_run_eq_trail hN cover tests z w o j (fun m hm => Nat.find_min he hm)⟩
  obtain ⟨h, ⟨m, hm⟩, hh, ⟨x, hx, ho⟩, _, hu, hq⟩ :=
    finish_of_cover_with_policy cover tests (restorationCollect cover tests)
      (restorationCollect_cover cover tests) (lazyTapes z w) o (frontierTrail z w j)
      hr (by simp) (by simp) hcj (hmark _ hcj)
  have hu' : h.updates ≤ t := by simpa only [frontierTrail_updates] using hu.le.trans (by simpa using hj)
  have hq' : h.checks ≤ Q := by
    simp only [frontierTrail_checks, frontierTrail_checked, Finset.sdiff_empty, zero_add] at hq
    exact hq.trans (hbound _ hcj)
  subst h
  exact ⟨⟨m, x, hx, ho⟩, costs_le_of_halted _ _ _ m t Q hh hu' hq'⟩

theorem restorationCollect_checks_le (hN : 2 < N k) (cover : Finset (Vertex k) → Prop)
    (tests : Finset (Vertex k) → Finset (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k)) (Q : ℕ)
    (hmark : ∀ v, cover v → ∃ x ∈ tests v, o x = true)
    (hbound : ∀ v, cover v → (tests v).card ≤ Q) :
    checkCost (restorationCollect cover tests) (lazyTapes z w) o ≤ Q := by
  classical
  by_cases he : ∃ t, cover (frontierTrail z w t).visited
  · obtain ⟨t, ht⟩ := he
    exact (restorationCollect_finishes hN cover tests z w o t Q ht hmark hbound).2.2
  · apply iSup_le
    intro n
    cases n with
    | zero => simp [History.checks]
    | succ n =>
      rw [restoration_run_eq_trail hN cover tests z w o n (fun j _ hj => he ⟨j, hj⟩), frontierTrail_checks]
      exact zero_le

def sparseRestorationPolicy [NeZero (L k)] : Policy (Vertex k) :=
  restorationCollect (Covers (phase (L k) (L_dvd_N k)))
    (representatives (phase (L k) (L_dvd_N k)))

def denseRestorationPolicy [NeZero (N k)] : Policy (Vertex k) :=
  restorationCollect (fun v => v = Finset.univ) (fun v => v ∩ denseNet)

theorem sparseRestorationPolicy_restoration [NeZero (L k)] (r : Tapes (Vertex k)) :
    Restoration oracle 1 sparseRestorationPolicy r :=
  restorationCollect_restoration _ _ (representatives_subset _) r

theorem denseRestorationPolicy_restoration [NeZero (N k)] (r : Tapes (Vertex k)) :
    Restoration oracle 1 denseRestorationPolicy r :=
  restorationCollect_restoration _ _ (fun _ => Finset.inter_subset_left) r

theorem sparseRestorationPolicy_at_count [NeZero (N k)] [NeZero (L k)]
    (hk : 0 < k) (hN : 2 < N k) (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (a : Vertex k) (t : ℕ) (hc : L k - 1 ≤ rightCountStream (w 0) t) :
    Succeeds sparseRestorationPolicy (lazyTapes z w) (oracle a) ∧
      updateCost sparseRestorationPolicy (lazyTapes z w) (oracle a) ≤ t ∧
      checkCost sparseRestorationPolicy (lazyTapes z w) (oracle a) ≤ L k := by
  apply restorationCollect_finishes hN _ _ _ _ _ t (L k)
  · exact covers_phase_frontier (L k) (L_dvd_N k) z w t hc
  · exact sparse_tests_marked hk a
  · intro v _
    exact (representatives_card_le _ v).trans_eq (ZMod.card (L k))

theorem denseRestorationPolicy_at_count [NeZero (N k)]
    (hk : 0 < k) (hN : 2 < N k) (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (a : Vertex k) (t : ℕ) (hc : N k - 1 ≤ rightCountStream (w 0) t) :
    Succeeds denseRestorationPolicy (lazyTapes z w) (oracle a) ∧
      updateCost denseRestorationPolicy (lazyTapes z w) (oracle a) ≤ t ∧
      checkCost denseRestorationPolicy (lazyTapes z w) (oracle a) ≤ k := by
  apply restorationCollect_finishes hN _ _ _ _ _ t k
  · exact frontier_visits_all z w t hc
  · exact dense_tests_marked hk a
  · intro v _
    exact (Finset.card_le_card Finset.inter_subset_right).trans (grid_card_le k (D k))

end RandomWalkSearch.Cycle
