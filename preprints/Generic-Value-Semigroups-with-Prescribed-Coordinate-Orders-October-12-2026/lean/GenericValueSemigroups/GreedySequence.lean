import Mathlib.Data.Finset.Max
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

namespace GenericValueSemigroups
open scoped Classical

def greedy (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => w 0
  | n+1 => max (w (n+1)) (greedy w n + 1)

@[simp] theorem greedy_zero (w : ℕ → ℕ) : greedy w 0 = w 0 := rfl
@[simp] theorem greedy_succ (w : ℕ → ℕ) (n : ℕ) :
    greedy w (n+1) = max (w (n+1)) (greedy w n + 1) := rfl

theorem weight_le_greedy (w : ℕ → ℕ) (n : ℕ) : w n ≤ greedy w n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

theorem greedy_strictMono (w : ℕ → ℕ) : StrictMono (greedy w) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

theorem index_le_greedy (w : ℕ → ℕ) (n : ℕ) : n ≤ greedy w n :=
  (greedy_strictMono w).id_le n

/-- The greedy positions are the index plus the largest preceding weight deficit. -/
theorem greedy_eq_running_deficit (w : ℕ → ℕ) (n : ℕ) :
    greedy w n = n + (Finset.range (n+1)).sup (fun i => w i-i) := by
  induction n with
  | zero => simp [greedy]
  | succ n ih =>
    rw [greedy_succ, Finset.range_add_one, Finset.sup_insert, ih]
    change max (w (n+1)) (n + (Finset.range (n+1)).sup (fun i => w i-i) + 1) =
      n+1 + max (w (n+1)-(n+1)) ((Finset.range (n+1)).sup (fun i => w i-i))
    have hn := index_le_greedy w n
    omega

/-- A global bound on weight deficits bounds every greedy position. -/
theorem greedy_le_of_weight_bound (w : ℕ → ℕ) (D : ℕ)
    (h : ∀ n, w n ≤ n+D) (n : ℕ) : greedy w n ≤ n+D := by
  induction n with
  | zero => exact h 0
  | succ n ih => rw [greedy_succ]; exact max_le (h _) (by omega)

/-- Once the largest weight deficit is attained, the greedy sequence is consecutive. -/
theorem greedy_eventually_consecutive (w : ℕ → ℕ) (D J : ℕ)
    (h : ∀ n, w n ≤ n+D) (hJ : w J = J+D) :
    ∀ n, J ≤ n → greedy w n = n+D := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    apply le_antisymm (greedy_le_of_weight_bound w D h J)
    simpa only [hJ] using weight_le_greedy w J
  | succ n hn ih =>
    rw [greedy_succ, ih]
    simpa only [Nat.add_right_comm n D 1] using (max_eq_right (h (n+1)))

/-- The values before the j-th greedy position are exactly its first j terms. -/
theorem greedy_values_below (w : ℕ → ℕ) (j : ℕ) :
    (Finset.range (greedy w j)).filter (fun n => n ∈ Set.range (greedy w)) =
      (Finset.range j).image (greedy w) := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hn, i, rfl⟩
    exact ⟨i, (greedy_strictMono w).lt_iff_lt.mp hn, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(greedy_strictMono w) hi, i, rfl⟩

theorem greedy_gap_count (w : ℕ → ℕ) (j : ℕ) :
    ((Finset.range (greedy w j)).filter (fun n => n ∉ Set.range (greedy w))).card =
      greedy w j - j := by
  classical
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.range (greedy w j)) (fun n => n ∈ Set.range (greedy w))
  rw [greedy_values_below, Finset.card_image_of_injective _ (greedy_strictMono w).injective,
    Finset.card_range, Finset.card_range] at hc
  omega

theorem mem_greedy_range_of_threshold (w : ℕ → ℕ) (D J : ℕ)
    (h : ∀ n, w n ≤ n+D) (hJ : w J = J+D) {n : ℕ} (hn : J+D ≤ n) :
    n ∈ Set.range (greedy w) := by
  refine ⟨n-D, ?_⟩
  rw [greedy_eventually_consecutive w D J h hJ (n-D) (by omega)]
  omega

/-- The complete gap set is finite, and its cardinality is the attained largest deficit. -/
theorem greedy_gaps_finite_card (w : ℕ → ℕ) (D J : ℕ)
    (h : ∀ n, w n ≤ n+D) (hJ : w J = J+D) :
    ∃ gaps : Finset ℕ, (∀ n, n ∈ gaps ↔ n ∉ Set.range (greedy w)) ∧ gaps.card = D := by
  classical
  let gaps := (Finset.range (greedy w J)).filter (fun n => n ∉ Set.range (greedy w))
  have hgJ := greedy_eventually_consecutive w D J h hJ J (le_refl J)
  refine ⟨gaps, ?_, ?_⟩
  · intro n
    simp only [gaps, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro hn
      refine ⟨?_, hn⟩
      rw [hgJ]
      by_contra hh
      exact hn (mem_greedy_range_of_threshold w D J h hJ (by omega))
  · change ((Finset.range (greedy w J)).filter _).card = D
    rw [greedy_gap_count, hgJ, Nat.add_sub_cancel_left]

theorem greedy_lt_before_first_maximum (w : ℕ → ℕ) (D J : ℕ)
    (hmin : ∀ n, n<J → w n<n+D) : ∀ n, n<J → greedy w n<n+D := by
  intro n
  induction n with
  | zero => exact hmin 0
  | succ n ih =>
    intro hn
    rw [greedy_succ]
    have hw := hmin (n+1) hn
    have hg := ih (by omega)
    omega

theorem greedy_last_gap (w : ℕ → ℕ) (D J : ℕ)
    (h : ∀ n, w n ≤ n+D) (hJ : w J=J+D) (hpos : 0<J)
    (hmin : ∀ n, n<J → w n<n+D) : J+D-1 ∉ Set.range (greedy w) := by
  rintro ⟨n,hn⟩
  by_cases hnj : n<J
  · have hh := greedy_lt_before_first_maximum w D J hmin n hnj
    omega
  · have hh := greedy_eventually_consecutive w D J h hJ n (by omega)
    omega

/-- The first attaining index gives the exact cofinality threshold. -/
theorem greedy_conductor (w : ℕ → ℕ) (hw0 : w 0=0) (D J : ℕ)
    (h : ∀ n, w n ≤ n+D) (hJ : w J=J+D)
    (hmin : ∀ n, n<J → w n<n+D) (N : ℕ) :
    (∀ n, N≤n → n ∈ Set.range (greedy w)) ↔ J+D≤N := by
  constructor
  · intro hN
    by_cases hpos : 0<J
    · by_contra hbad
      have hmem := hN (J+D-1) (by omega)
      exact greedy_last_gap w D J h hJ hpos hmin hmem
    · have hzero : J=0 := by omega
      simp only [hzero, hw0, zero_add] at hJ
      omega
  · intro hN n hn
    exact mem_greedy_range_of_threshold w D J h hJ (le_trans hN hn)

end GenericValueSemigroups
