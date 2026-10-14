import MainTheorems.PathCycleTuza.RunCosts
import Mathlib.Algebra.BigOperators.Fin

namespace ResearchMain.PathCycleTuza

structure CircularRuns (n k : ℕ) where
  count : ℕ
  count_four : 4 ≤ count
  count_even : count % 2 = 0
  length : Fin count → ℕ
  positive : ∀ i, 0 < length i
  lower : ∀ i, Tuza.halfUp k ≤ length i
  upper : ∀ i, length i ≤ k
  total : ∑ i, length i = n

def canonicalRuns (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n) : CircularRuns n k where
  count := runCount n k
  count_four := runCount_four n k hk hn
  count_even := runCount_even n k
  length := runLength n k
  positive := runLength_positive n k (by omega)
  lower i := (runLength_bounds n k i).1
  upper i := (runLength_bounds n k i).2
  total := runLength_sum n k hk hn

namespace CircularRuns

variable {n k : ℕ} (D : CircularRuns n k)

def index (j : ℕ) : Fin D.count := ⟨j % D.count, Nat.mod_lt _ (by have := D.count_four; omega)⟩

def extendedLength (j : ℕ) : ℕ := D.length (D.index j)

def runStart (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, D.extendedLength i

theorem index_val (j : ℕ) : (D.index j).val = j % D.count := rfl

theorem index_lt (j : ℕ) (hj : j < D.count) : D.index j = ⟨j, hj⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hj

theorem index_add_count (j : ℕ) : D.index (j + D.count) = D.index j := by
  apply Fin.ext
  simp [index]

theorem extendedLength_add_count (j : ℕ) :
    D.extendedLength (j + D.count) = D.extendedLength j := by
  rw [extendedLength, extendedLength, index_add_count]

theorem extendedLength_lower (j : ℕ) : Tuza.halfUp k ≤ D.extendedLength j := D.lower _

theorem extendedLength_positive (j : ℕ) : 0 < D.extendedLength j := D.positive _

theorem runStart_zero : D.runStart 0 = 0 := by simp [runStart]

theorem runStart_succ (j : ℕ) : D.runStart (j + 1) = D.runStart j + D.extendedLength j := by
  exact Finset.sum_range_succ _ _

theorem runStart_mono : Monotone D.runStart := by
  apply monotone_nat_of_le_succ
  intro j
  rw [runStart_succ]
  omega

theorem runStart_strict : StrictMono D.runStart := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [runStart_succ]
  have := D.extendedLength_positive j
  omega

theorem runStart_lower (j t : ℕ) : D.runStart j + Tuza.halfUp k * t ≤ D.runStart (j + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    change D.runStart j + Tuza.halfUp k * (t + 1) ≤ D.runStart ((j + t) + 1)
    rw [runStart_succ, Nat.mul_succ]
    have := D.extendedLength_lower (j + t)
    omega

theorem runStart_total : D.runStart D.count = n := by
  rw [runStart, ← Fin.sum_univ_eq_sum_range]
  convert D.total using 1
  apply Finset.sum_congr rfl
  intro i him
  rw [extendedLength, index_lt _ _ i.isLt]

theorem runStart_period (j : ℕ) : D.runStart (j + D.count) = D.runStart j + n := by
  rw [Nat.add_comm j D.count, runStart, Finset.sum_range_add]
  have h : ∑ i ∈ Finset.range j, D.extendedLength (D.count + i) = D.runStart j := by
    apply Finset.sum_congr rfl
    intro i him
    rw [Nat.add_comm D.count i, extendedLength_add_count]
  rw [h]
  change D.runStart D.count + D.runStart j = _
  rw [runStart_total]
  omega

abbrev Position := Σ i : Fin D.count, Fin (D.length i)

def vertexEquiv : D.Position ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr D.total)

theorem vertex_val (p : D.Position) : (D.vertexEquiv p).val = D.runStart p.1.val + p.2.val := by
  dsimp [vertexEquiv]
  rw [finSigmaFinEquiv_apply, runStart, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i him
  have hi : i.val < D.count := i.isLt.trans p.1.isLt
  rw [extendedLength, index_lt _ _ hi]
  rfl

theorem position_bounds (p : D.Position) :
    D.runStart p.1.val ≤ (D.vertexEquiv p).val ∧
      (D.vertexEquiv p).val < D.runStart (p.1.val + 1) := by
  rw [vertex_val, runStart_succ, extendedLength, index_lt _ _ p.1.isLt]
  change D.runStart p.1.val ≤ D.runStart p.1.val + p.2.val ∧
    D.runStart p.1.val + p.2.val < D.runStart p.1.val + D.length p.1
  have := p.2.isLt
  omega

def color (x : Fin n) : Bool := decide ((D.vertexEquiv.symm x).1.val % 2 = 0)

theorem sameColor_positions (p q : D.Position)
    (hc : D.color (D.vertexEquiv p) = D.color (D.vertexEquiv q)) : p.1.val % 2 = q.1.val % 2 := by
  simp only [color, Equiv.symm_apply_apply, decide_eq_decide] at hc
  omega

end CircularRuns

end ResearchMain.PathCycleTuza
