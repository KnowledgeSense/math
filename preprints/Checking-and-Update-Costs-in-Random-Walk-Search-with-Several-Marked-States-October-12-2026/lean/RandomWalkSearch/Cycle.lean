import RandomWalkSearch.Locality
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Lazy cycles and the actual dense-plus-sparse marked translates -/

namespace RandomWalkSearch

namespace Cycle

variable (k : ℕ)

def L : ℕ := k ^ 2
def N : ℕ := k ^ 8
def D : ℕ := k ^ 7
abbrev Vertex := ZMod (N k)

variable {k}

theorem L_pos (hk : 0 < k) : 0 < L k := pow_pos hk _
theorem N_pos (hk : 0 < k) : 0 < N k := pow_pos hk _
theorem D_pos (hk : 0 < k) : 0 < D k := pow_pos hk _

theorem L_dvd_D (k : ℕ) : L k ∣ D k := by
  exact pow_dvd_pow k (by decide : 2 ≤ 7)

theorem D_dvd_N (k : ℕ) : D k ∣ N k := by
  exact pow_dvd_pow k (by decide : 7 ≤ 8)

theorem L_dvd_N (k : ℕ) : L k ∣ N k := (L_dvd_D k).trans (D_dvd_N k)

/-- A genuine nearest-neighbour increment. Two of four equally likely symbols
will be used for `stay` in the random-tape measure. -/
inductive Increment where
  | left
  | stay
  | right
  deriving DecidableEq

def Increment.value : Increment → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

def increment (q : Fin 4) : Increment :=
  if q = 0 then .left else if q = 1 then .right else .stay

def lazyTapes (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) : Tapes (Vertex k) where
  setup := z
  update := fun i j x => x + (increment (w i j)).value

def adjacent (x y : Vertex k) : Prop := y = x - 1 ∨ y = x ∨ y = x + 1

theorem lazyTapes_adjacent (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (i j : ℕ) (x : Vertex k) : adjacent x ((lazyTapes z w).update i j x) := by
  unfold lazyTapes adjacent
  cases h : increment (w i j) <;> simp [h, Increment.value, sub_eq_add_neg]

/-- A cyclic arc of `d` successive labels, defined by its actual vertices. -/
def arc (x : Vertex k) (d : ℕ) : Finset (Vertex k) :=
  (Finset.range d).image (fun j : ℕ => x + (j : Vertex k))

def interval (a : Vertex k) : Finset (Vertex k) := arc a (D k)

/-- The sparse progression consists of the `k^6` multiples of `L`, translated
by `a`; since `N = k^6 * L`, this is the residue class of `a` modulo `L`. -/
def progression (a : Vertex k) : Finset (Vertex k) :=
  (Finset.range (k ^ 6)).image (fun j : ℕ => a + (j * L k : ℕ))

def marked (a : Vertex k) : Finset (Vertex k) := interval a ∪ progression a

def oracle (a : Vertex k) : Oracle (Vertex k) := fun x => decide (x ∈ marked a)

/-- Interval starting positions whose interval contains a given vertex. -/
def intervalStarts (d : ℕ) (x : Vertex k) : Finset (Vertex k) :=
  (Finset.range d).image (fun j : ℕ => x - (j : Vertex k))

@[simp] theorem mem_intervalStarts (d : ℕ) (x a : Vertex k) :
    a ∈ intervalStarts d x ↔ x ∈ arc a d := by
  simp only [intervalStarts, arc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, sub_add_cancel _ _⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, hj, by rw [← hx]; simp⟩

theorem card_intervalStarts_le (d : ℕ) (x : Vertex k) :
    (intervalStarts d x).card ≤ d := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range d)

/-- Adding the right neighbour of a visited vertex exposes at most one new
possible interval translate. The statement is valid even for wrapped arcs. -/
theorem intervalStarts_right_subset (d : ℕ) (x : Vertex k) :
    intervalStarts d (x + 1) ⊆ insert (x + 1) (intervalStarts d x) := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  by_cases hj0 : j = 0
  · simp [hj0]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨m, Finset.mem_range.mpr (Nat.lt_of_succ_lt (Finset.mem_range.mp hj)), ?_⟩
    push_cast
    ring

/-- The analogous one-new-translate property for the left neighbour. -/
theorem intervalStarts_left_subset (d : ℕ) (x : Vertex k) :
    intervalStarts d (x - 1) ⊆ insert (x - d) (intervalStarts d x) := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hjd : j < d := Finset.mem_range.mp hj
  by_cases hnext : j + 1 < d
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨j + 1, Finset.mem_range.mpr hnext, ?_⟩
    push_cast
    ring
  · have heq : d = j + 1 := by omega
    apply Finset.mem_insert.mpr
    left
    rw [heq]
    push_cast
    ring

/-- Exact exposure set of all interval translates meeting a finite visited set. -/
def exposure (d : ℕ) (v : Finset (Vertex k)) : Finset (Vertex k) :=
  v.biUnion (intervalStarts d)

@[simp] theorem exposure_empty (d : ℕ) : exposure (k := k) d ∅ = ∅ := by
  simp [exposure]

@[simp] theorem exposure_insert (d : ℕ) (v : Finset (Vertex k)) (x : Vertex k) :
    exposure d (insert x v) = intervalStarts d x ∪ exposure d v := by
  simp [exposure]

theorem intervalStarts_subset_exposure (d : ℕ) {v : Finset (Vertex k)}
    {x : Vertex k} (hx : x ∈ v) : intervalStarts d x ⊆ exposure d v := by
  exact Finset.subset_biUnion_of_mem (intervalStarts d) hx

theorem exposure_setup (d : ℕ) (v : Finset (Vertex k)) (x : Vertex k) :
    (exposure d (insert x v)).card ≤ (exposure d v).card + d := by
  rw [exposure_insert]
  calc
    _ ≤ (intervalStarts d x).card + (exposure d v).card := Finset.card_union_le _ _
    _ ≤ (exposure d v).card + d := by have := card_intervalStarts_le d x; omega

/-- The visited-geometry induction can charge one translate per local update,
regardless of restoration, adaptivity, overlap, or wrap-around. -/
theorem exposure_update (d : ℕ) (v : Finset (Vertex k)) (x y : Vertex k)
    (hx : x ∈ v) (hxy : adjacent x y) :
    (exposure d (insert y v)).card ≤ (exposure d v).card + 1 := by
  have hbase := intervalStarts_subset_exposure d hx
  rcases hxy with rfl | rfl | rfl
  · rw [exposure_insert]
    have hsub : intervalStarts d (x - 1) ∪ exposure d v ⊆
        insert (x - d) (exposure d v) :=
      Finset.union_subset ((intervalStarts_left_subset d x).trans
        (Finset.insert_subset_insert _ hbase)) (Finset.subset_insert ..)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le ..)
  · rw [Finset.insert_eq_of_mem hx]
    omega
  · rw [exposure_insert]
    have hsub : intervalStarts d (x + 1) ∪ exposure d v ⊆
        insert (x + 1) (exposure d v) :=
      Finset.union_subset ((intervalStarts_right_subset d x).trans
        (Finset.insert_subset_insert _ hbase)) (Finset.subset_insert ..)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le ..)

/-! ## Geometry of genuine executions -/

theorem run_exposure_le (d : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (o : Oracle (Vertex k))
    (hl : ∀ n, (run p (lazyTapes z w) o n).halted = false →
      Local (run p (lazyTapes z w) o n) (p (run p (lazyTapes z w) o n)))
    (n : ℕ) :
    (exposure d (run p (lazyTapes z w) o n).visited).card ≤
      d * (run p (lazyTapes z w) o n).setups +
        (run p (lazyTapes z w) o n).updates := by
  induction n with
  | zero => simp [History.setups, History.updates]
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hactive
      have hl' := hl n (Bool.eq_false_iff.mpr hactive)
      cases ha : p (run p (lazyTapes z w) o n) with
      | setup =>
        simp only [respond, History.visited_cons_setup,
          History.setups, History.updates, List.countP_cons, Event.isSetup,
          Event.isUpdate, Bool.false_eq_true, ite_false, ite_true,
          Nat.add_zero, Nat.mul_add, Nat.mul_one] at ih ⊢
        exact (exposure_setup d _ _).trans (by omega)
      | update i x =>
        have hx : x ∈ (run p (lazyTapes z w) o n).visited := by
          simpa only [ha, Local] using hl'
        have hg := exposure_update d (run p (lazyTapes z w) o n).visited x
          ((lazyTapes z w).update i ((run p (lazyTapes z w) o n).trajectoryUpdates i) x)
          hx (lazyTapes_adjacent z w i _ x)
        simp only [respond, History.visited_cons_update,
          History.setups, History.updates, List.countP_cons, Event.isSetup,
          Event.isUpdate, Bool.false_eq_true, ite_false, ite_true,
          Nat.add_zero] at ih ⊢
        exact hg.trans (by omega)
      | check x =>
        simpa [ha, respond, History.setups, History.updates,
          Event.isSetup, Event.isUpdate] using ih
      | output x =>
        simpa [ha, respond, History.setups, History.updates,
          Event.isSetup, Event.isUpdate] using ih
      | think =>
        simpa [ha, respond, History.setups, History.updates,
          Event.isSetup, Event.isUpdate] using ih

end Cycle
end RandomWalkSearch
