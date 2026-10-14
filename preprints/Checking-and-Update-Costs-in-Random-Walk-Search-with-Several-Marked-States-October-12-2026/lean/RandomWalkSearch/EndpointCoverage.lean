import RandomWalkSearch.EndpointNets

noncomputable section
namespace RandomWalkSearch.EndpointPolicy

/-- Discrete intermediate value theorem with one-sided unit step bound. -/
theorem hits_level (f : ℕ → ℤ) (n : ℕ) (a : ℤ)
    (hzero : f 0 ≤ a) (hend : a ≤ f n)
    (hstep : ∀ j, f (j + 1) ≤ f j + 1) : ∃ t ≤ n, f t = a := by
  have he : ∃ t, a ≤ f t := ⟨n, hend⟩
  refine ⟨Nat.find he, Nat.find_min' he hend, ?_⟩
  have hh := Nat.find_spec he
  rcases ht : Nat.find he with _ | t
  · rw [ht] at hh
    omega
  · have hb : f t < a := lt_of_not_ge (Nat.find_min he (by omega))
    have hs := hstep t
    rw [ht] at hh
    omega

theorem hits_level_down (f : ℕ → ℤ) (n : ℕ) (a : ℤ)
    (hzero : a ≤ f 0) (hend : f n ≤ a)
    (hstep : ∀ j, f j - 1 ≤ f (j + 1)) : ∃ t ≤ n, f t = a := by
  obtain ⟨t, ht, he⟩ := hits_level (fun j => -f j) n (-a) (by omega) (by omega)
    (fun j => by have := hstep j; omega)
  exact ⟨t, ht, by omega⟩

variable {X : Type*} [DecidableEq X]

theorem trajectory_mem_trail (r : Tapes X) (n t : ℕ) (ht : t ≤ n) :
    trajectory r t ∈ (trail r n).visited := by
  induction n with
  | zero =>
    have he : t = 0 := by omega
    subst t
    simp [trail, trajectory]
  | succ n ih =>
    by_cases he : t = n + 1
    · subst t
      simp [trail]
    · rw [trail, History.visited_cons_update]
      exact Finset.mem_insert_of_mem (ih (by omega))

end RandomWalkSearch.EndpointPolicy

namespace RandomWalkSearch.Cycle
open EndpointPolicy LazyWalk

variable {k : ℕ}

theorem lazy_trajectory (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) :
    trajectory (lazyTapes z w) n = z 0 + (integerWalk (w 0) n : Vertex k) := by
  induction n with
  | zero => simp [trajectory, lazyTapes, integerWalk]
  | succ n ih =>
    change trajectory (lazyTapes z w) n + ((increment (w 0 n)).value : Vertex k) = _
    rw [ih]
    simp only [integerWalk, Int.cast_add]
    ring

theorem integerWalk_step_bounds (w : ℕ → Fin 4) (n : ℕ) :
    integerWalk w n - 1 ≤ integerWalk w (n + 1) ∧
      integerWalk w (n + 1) ≤ integerWalk w n + 1 := by
  have h := abs_le.mp (increment_abs_le (w n))
  simp only [integerWalk]
  omega

/-- At first distance `q`, an actual lazy trajectory has visited every phase modulo `q`. -/
theorem covers_phase_at_exit (q : ℕ) [NeZero q] (hq : q ∣ N k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (t : ℕ)
    (hexit : |integerWalk (w 0) t| = (q : ℤ)) :
    Covers (phase q hq) (trail (lazyTapes z w) t).visited := by
  intro c
  let f := phase (k := k) q hq
  rcases (abs_eq (show (0 : ℤ) ≤ q by omega)).mp hexit with hpos | hneg
  · let j := (c - f (z 0)).val
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by omega
    have hjq : (j : ℤ) ≤ (q : ℤ) := by
      have hlt : j < q := ZMod.val_lt _
      omega
    obtain ⟨s, hs, hp⟩ := hits_level (integerWalk (w 0)) t (j : ℤ)
      hj0 (by omega) (fun n => (integerWalk_step_bounds (w 0) n).2)
    refine ⟨trajectory (lazyTapes z w) s, trajectory_mem_trail _ t s hs, ?_⟩
    rw [lazy_trajectory, hp]
    change f (z 0 + ((j : ℤ) : Vertex k)) = c
    rw [map_add, map_intCast, Int.cast_natCast]
    change f (z 0) + ((c - f (z 0)).val : ZMod q) = c
    rw [ZMod.natCast_zmod_val]
    abel
  · let j := (f (z 0) - c).val
    have hj0 : -(j : ℤ) ≤ 0 := by omega
    have hjq : -(q : ℤ) ≤ -(j : ℤ) := by
      have hlt : j < q := ZMod.val_lt _
      omega
    obtain ⟨s, hs, hp⟩ := hits_level_down (integerWalk (w 0)) t (-(j : ℤ))
      hj0 (by omega) (fun n => (integerWalk_step_bounds (w 0) n).1)
    refine ⟨trajectory (lazyTapes z w) s, trajectory_mem_trail _ t s hs, ?_⟩
    rw [lazy_trajectory, hp]
    change f (z 0 + (((-(j : ℤ)) : ℤ) : Vertex k)) = c
    rw [map_add, map_intCast, Int.cast_neg, Int.cast_natCast]
    change f (z 0) + -((f (z 0) - c).val : ZMod q) = c
    rw [ZMod.natCast_zmod_val]
    abel

/-- Reaching distance `N` has genuinely visited the entire cycle. -/
theorem visits_all_at_exit [NeZero (N k)]
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (t : ℕ)
    (hexit : |integerWalk (w 0) t| = (N k : ℤ)) :
    (trail (lazyTapes z w) t).visited = Finset.univ := by
  have hc := covers_phase_at_exit (N k) (dvd_refl _) z w t hexit
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨y, hy, he⟩ := hc x
  have hyx : y = x := by simpa [phase, ZMod.cast_id] using he
  exact hyx ▸ hy

/-- The actual sparse endpoint algorithm succeeds by distance `L`, with at most `L` checks. -/
theorem sparsePolicy_costs_at_exit [NeZero (N k)] [NeZero (L k)] (hk : 0 < k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) (t : ℕ)
    (hexit : |integerWalk (w 0) t| = (L k : ℤ)) :
    Succeeds sparsePolicy (lazyTapes z w) (oracle a) ∧
      updateCost sparsePolicy (lazyTapes z w) (oracle a) ≤ t ∧
      checkCost sparsePolicy (lazyTapes z w) (oracle a) ≤ L k := by
  apply collectThenCheck_costs _ _ _ _ t (L k)
  · exact covers_phase_at_exit (L k) (L_dvd_N k) z w t hexit
  · exact sparse_tests_marked hk a
  · intro v _
    exact (representatives_card_le _ v).trans_eq (ZMod.card (L k))

/-- The actual dense endpoint algorithm succeeds by distance `N`, with at most `k` checks. -/
theorem densePolicy_costs_at_exit [NeZero (N k)] (hk : 0 < k)
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (a : Vertex k) (t : ℕ)
    (hexit : |integerWalk (w 0) t| = (N k : ℤ)) :
    Succeeds densePolicy (lazyTapes z w) (oracle a) ∧
      updateCost densePolicy (lazyTapes z w) (oracle a) ≤ t ∧
      checkCost densePolicy (lazyTapes z w) (oracle a) ≤ k := by
  apply collectThenCheck_costs _ _ _ _ t k
  · exact visits_all_at_exit z w t hexit
  · exact dense_tests_marked hk a
  · intro v _
    exact (Finset.card_le_card Finset.inter_subset_right).trans (grid_card_le k (D k))

end RandomWalkSearch.Cycle
