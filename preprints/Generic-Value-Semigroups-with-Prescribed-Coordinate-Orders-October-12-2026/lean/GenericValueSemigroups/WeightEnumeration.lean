import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

namespace GenericValueSemigroups
open scoped BigOperators Classical

def weight {d : ℕ} (r α : Fin d → ℕ) : ℕ := ∑ i, α i * r i

noncomputable def weightSet {d : ℕ} (r : Fin d → ℕ) (n : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (n+1))).filter (fun α => weight r α < n)

noncomputable def weightCount {d : ℕ} (r : Fin d → ℕ) (n : ℕ) : ℕ :=
  (weightSet r n).card

theorem coordinate_le_weight {d : ℕ} (r α : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (i : Fin d) : α i ≤ weight r α := by
  calc
    α i ≤ α i * r i := Nat.le_mul_of_pos_right _ (hr i)
    _ ≤ _ := Finset.single_le_sum (fun j _ => Nat.zero_le (α j * r j)) (Finset.mem_univ i)

@[simp] theorem mem_weightSet {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (n : ℕ) (α : Fin d → ℕ) : α ∈ weightSet r n ↔ weight r α < n := by
  simp only [weightSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨fun i => by have hi := coordinate_le_weight r α hr i; omega, h⟩⟩

@[simp] theorem weightCount_zero {d : ℕ} (r : Fin d → ℕ) : weightCount r 0 = 0 := by
  simp [weightCount, weightSet]

theorem weightCount_mono {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) :
    Monotone (weightCount r) := by
  intro n m hnm
  apply Finset.card_le_card
  intro α ha
  exact (mem_weightSet r hr m α).mpr (lt_of_lt_of_le ((mem_weightSet r hr n α).mp ha) hnm)

@[simp] theorem weight_single {d : ℕ} (r : Fin d → ℕ) (i : Fin d) (k : ℕ) :
    weight r (Function.update (fun _ => 0) i k) = k * r i := by
  simp [weight, Function.update_apply]

theorem weightCount_large {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (i : Fin d) (j : ℕ) : j < weightCount r ((j+1)*r i) := by
  let f : ℕ → (Fin d → ℕ) := fun k => Function.update (fun _ => 0) i k
  have hf : Function.Injective f := by
    intro a b hab
    have hh := congrFun hab i
    simpa [f] using hh
  have hsub : (Finset.range (j+1)).image f ⊆ weightSet r ((j+1)*r i) := by
    intro α ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    rw [mem_weightSet r hr, weight_single]
    exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hk) (hr i)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_range] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self j) hc

theorem weightCount_unbounded {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (j : ℕ) : ∃ n, j < weightCount r (n+1) := by
  let i : Fin d := ⟨0,hd⟩
  refine ⟨(j+1)*r i, ?_⟩
  exact lt_of_lt_of_le (weightCount_large r hr i j) (weightCount_mono r hr (Nat.le_succ _))

/-- The nondecreasing list of monomial weights, with every multiplicity retained. -/
noncomputable def weightAt {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (j : ℕ) : ℕ := Nat.find (weightCount_unbounded r hr hd j)

theorem weightAt_count_upper {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (j : ℕ) : j < weightCount r (weightAt r hr hd j + 1) :=
  Nat.find_spec (weightCount_unbounded r hr hd j)

/-- The counting function and sorted weight enumeration are inverse in this strict sense. -/
theorem weightAt_lt_iff {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (j n : ℕ) : weightAt r hr hd j < n ↔ j < weightCount r n := by
  constructor
  · intro hn
    exact lt_of_lt_of_le (weightAt_count_upper r hr hd j)
      (weightCount_mono r hr (by omega))
  · intro hn
    cases n with
    | zero => simp at hn
    | succ n =>
      have hh : weightAt r hr hd j ≤ n := Nat.find_min' (weightCount_unbounded r hr hd j) hn
      omega

theorem weightAt_mono {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) : Monotone (weightAt r hr hd) := by
  intro i j hij
  have hh := weightAt_count_upper r hr hd j
  exact Nat.lt_succ_iff.mp ((weightAt_lt_iff r hr hd i _).mpr (lt_of_le_of_lt hij hh))

theorem weightCount_at_weightAt {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (j : ℕ) : weightCount r (weightAt r hr hd j) ≤ j := by
  by_contra hn
  have hh := (weightAt_lt_iff r hr hd j (weightAt r hr hd j)).mpr (by omega)
  exact (lt_irrefl _) hh

@[simp] theorem weightAt_zero {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) : weightAt r hr hd 0 = 0 := by
  have hz : (fun _ : Fin d => 0) ∈ weightSet r 1 := by
    rw [mem_weightSet r hr]
    simp [weight]
  have hc : 0 < weightCount r 1 := Finset.card_pos.mpr ⟨_, hz⟩
  have hw := (weightAt_lt_iff r hr hd 0 1).mpr hc
  omega

theorem weightAt_unbounded {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (n : ℕ) : ∀ j, weightCount r n ≤ j → n ≤ weightAt r hr hd j := by
  intro j hj
  by_contra hh
  have hc := (weightAt_lt_iff r hr hd j n).mp (by omega)
  omega

end GenericValueSemigroups
