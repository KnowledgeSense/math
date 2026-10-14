import RandomWalkSearch.EndpointExecution
import RandomWalkSearch.LazyExit
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace RandomWalkSearch.EndpointPolicy

variable {X K : Type*} [DecidableEq X] [DecidableEq K] [Fintype K]

def representatives (key : X → K) (v : Finset X) : Finset X :=
  Finset.univ.biUnion (fun j => (pick (v.filter (fun x => key x = j))).toFinset)

def Covers (key : X → K) (v : Finset X) : Prop := ∀ j, ∃ x ∈ v, key x = j

theorem representatives_subset (key : X → K) (v : Finset X) :
    representatives key v ⊆ v := by
  intro x hx
  obtain ⟨j, _, hx⟩ := Finset.mem_biUnion.mp hx
  have hp : pick (v.filter (fun x => key x = j)) = some x := by
    exact Option.mem_toFinset.mp hx
  exact (Finset.mem_filter.mp (pick_some_mem hp)).1

theorem representatives_card_le (key : X → K) (v : Finset X) :
    (representatives key v).card ≤ Fintype.card K := by
  calc
    _ ≤ Finset.univ.card * 1 := Finset.card_biUnion_le_card_mul _ _ _ (fun j _ => by
      cases pick (v.filter (fun x => key x = j)) <;> simp)
    _ = _ := by simp

theorem representatives_cover (key : X → K) (v : Finset X) (hc : Covers key v) :
    Covers key (representatives key v) := by
  intro j
  have he : (v.filter (fun x => key x = j)).Nonempty := by
    obtain ⟨x, hx, hj⟩ := hc j
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hj⟩⟩
  cases hp : pick (v.filter (fun x => key x = j)) with
  | none => exact False.elim (he.ne_empty ((pick_eq_none_iff _).mp hp))
  | some x =>
    have hx := Finset.mem_filter.mp (pick_some_mem hp)
    exact ⟨x, Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simp [hp]⟩, hx.2⟩

end RandomWalkSearch.EndpointPolicy

namespace RandomWalkSearch.Cycle
open EndpointPolicy

variable {k : ℕ}

def phase (q : ℕ) (hq : q ∣ N k) : Vertex k →+* ZMod q := ZMod.castHom hq (ZMod q)

def grid (m q : ℕ) : Finset (Vertex k) :=
  (Finset.range m).image (fun j : ℕ => (j * q : ℕ))

theorem grid_card_le (m q : ℕ) : (grid (k := k) m q).card ≤ m :=
  Finset.card_image_le.trans_eq (Finset.card_range _)

/-- A genuine cyclic arithmetic progression is exactly a phase class. -/
theorem mem_grid_iff_phase [NeZero (N k)] (m q : ℕ) (_hq : 0 < q)
    (hN : N k = m * q) (x : Vertex k) :
    x ∈ grid m q ↔ phase q (hN ▸ dvd_mul_left q m) x = 0 := by
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [map_natCast]
    simp [Nat.cast_mul]
  · intro hx
    have hcast : (x.val : ZMod q) = 0 := by
      change ZMod.cast x = 0 at hx
      rw [← ZMod.natCast_val] at hx
      exact hx
    have hd : q ∣ x.val := (ZMod.natCast_eq_zero_iff x.val q).mp hcast
    obtain ⟨j, hj⟩ := hd
    have hlt : x.val < m * q := lt_of_lt_of_eq x.val_lt hN
    have hjlt : j < m := by
      rw [hj] at hlt
      nlinarith
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjlt, ?_⟩
    rw [Nat.mul_comm j q, ← hj]
    exact ZMod.natCast_zmod_val x

/-- Every arc of `q` vertices intersects the grid of spacing `q`. -/
theorem arc_meets_grid [NeZero (N k)] (m q : ℕ) (hq : 0 < q)
    (hN : N k = m * q) (a : Vertex k) :
    ∃ x, x ∈ arc a q ∧ x ∈ grid m q := by
  let : NeZero q := ⟨by omega⟩
  let f := phase (k := k) q (hN ▸ dvd_mul_left q m)
  let j := (-f a).val
  refine ⟨a + (j : Vertex k), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (ZMod.val_lt _), rfl⟩
  · apply (mem_grid_iff_phase m q hq hN _).mpr
    change f (a + (j : Vertex k)) = 0
    rw [map_add, map_natCast]
    change f a + ((-f a).val : ZMod q) = 0
    rw [ZMod.natCast_zmod_val, add_neg_cancel]

theorem N_eq_sparse (k : ℕ) : N k = k ^ 6 * L k := by
  dsimp [N, L]
  ring

theorem N_eq_dense (k : ℕ) : N k = k * D k := by
  dsimp [N, D]
  ring

/-- Phase equality is membership in the actual translated sparse progression. -/
theorem mem_progression_iff_phase [NeZero (N k)] (hk : 0 < k) (a x : Vertex k) :
    x ∈ progression a ↔ phase (L k) (L_dvd_N k) x = phase (L k) (L_dvd_N k) a := by
  have hg := mem_grid_iff_phase (k ^ 6) (L k) (L_pos hk) (N_eq_sparse k) (x - a)
  have he : x ∈ progression a ↔ x - a ∈ grid (k ^ 6) (L k) := by
    simp only [progression, grid, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rw [← hx]; simp⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rw [hx]; abel⟩
  rw [he, hg]
  change phase (L k) (L_dvd_N k) (x - a) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

def sparsePolicy [NeZero (L k)] : Policy (Vertex k) :=
  collectThenCheck (Covers (phase (L k) (L_dvd_N k)))
    (representatives (phase (L k) (L_dvd_N k)))

def denseNet : Finset (Vertex k) := grid k (D k)

def densePolicy [NeZero (N k)] : Policy (Vertex k) :=
  collectThenCheck (fun v => v = Finset.univ) (fun v => v ∩ denseNet)

theorem sparse_tests_marked [NeZero (N k)] [NeZero (L k)] (hk : 0 < k) (a : Vertex k)
    (v : Finset (Vertex k)) (hc : Covers (phase (L k) (L_dvd_N k)) v) :
    ∃ x ∈ representatives (phase (L k) (L_dvd_N k)) v, oracle a x = true := by
  obtain ⟨x, hx, hp⟩ := representatives_cover _ _ hc (phase (L k) (L_dvd_N k) a)
  refine ⟨x, hx, ?_⟩
  have hm : x ∈ marked a := Finset.mem_union_right _ ((mem_progression_iff_phase hk a x).mpr hp)
  simpa [oracle] using hm

theorem dense_tests_marked [NeZero (N k)] (hk : 0 < k) (a : Vertex k)
    (v : Finset (Vertex k)) (hc : v = Finset.univ) :
    ∃ x ∈ v ∩ denseNet, oracle a x = true := by
  obtain ⟨x, hi, hg⟩ := arc_meets_grid k (D k) (D_pos hk) (N_eq_dense k) a
  refine ⟨x, Finset.mem_inter.mpr ⟨hc ▸ Finset.mem_univ x, hg⟩, ?_⟩
  have hm : x ∈ marked a := Finset.mem_union_left _ hi
  simpa [oracle] using hm

theorem sparsePolicy_consecutive [NeZero (L k)] (r : Tapes (Vertex k)) :
    Consecutive oracle 1 sparsePolicy r :=
  collectThenCheck_consecutive oracle _ _ (representatives_subset _) r

theorem densePolicy_consecutive [NeZero (N k)] (r : Tapes (Vertex k)) :
    Consecutive oracle 1 densePolicy r :=
  collectThenCheck_consecutive oracle _ _ (fun _ => Finset.inter_subset_left) r

end RandomWalkSearch.Cycle
