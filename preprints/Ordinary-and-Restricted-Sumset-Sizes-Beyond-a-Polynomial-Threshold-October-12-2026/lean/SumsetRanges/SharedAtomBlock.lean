import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import SumsetRanges.LinearBlock

open Finset
namespace SumsetRanges

abbrev SharedIndex (m u : ℕ) := Fin u × Option (Fin (m-1))
abbrev SharedAtom (m u : ℕ) := Option (Fin u × Fin (m-1))
abbrev SharedLattice (m u : ℕ) := SharedAtom m u → ℤ

def sharedPoint {m u : ℕ} : SharedIndex m u → SharedLattice m u
  | (i, none) => fun a => match a with
    | none => -1
    | some (i', _) => if i'=i then 1 else 0
  | (i, some j) => fun a => if a=some (i,j) then 1 else 0

def sharedAtomBlock (m u : ℕ) : Finset (SharedLattice m u) :=
  Finset.univ.image sharedPoint

def sharedAlphaCount {m u : ℕ} (S : Finset (SharedIndex m u)) : ℕ :=
  (S.filter (fun a => a.2=none)).card

def sharedRowValue {m u : ℕ} (S : Finset (SharedIndex m u))
    (i : Fin u) (j : Fin (m-1)) : ℤ :=
  (if (i,some j) ∈ S then 1 else 0) + (if (i,none) ∈ S then 1 else 0)

theorem sum_sharedPoint_row {m u : ℕ} (S : Finset (SharedIndex m u))
    (i : Fin u) (j : Fin (m-1)) :
    (∑ a ∈ S, sharedPoint a) (some (i,j)) = sharedRowValue S i j := by
  have h : ∀ a : SharedIndex m u, sharedPoint a (some (i,j)) =
      (if a=(i,some j) then (1 : ℤ) else 0) + (if a=(i,none) then 1 else 0) := by
    rintro ⟨k, _ | l⟩ <;> simp [sharedPoint, eq_comm]
  simp only [Finset.sum_apply, h, Finset.sum_add_distrib]
  simp [sharedRowValue]

theorem sum_sharedPoint_omega {m u : ℕ} (S : Finset (SharedIndex m u)) :
    (∑ a ∈ S, sharedPoint a) none = -(sharedAlphaCount S : ℤ) := by
  have h : ∀ a : SharedIndex m u, sharedPoint a none =
      -(if a.2=none then (1 : ℤ) else 0) := by
    rintro ⟨k, _ | l⟩ <;> simp [sharedPoint]
  simp only [Finset.sum_apply, h, Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_filter]
  simp [sharedAlphaCount]

/-- Exhaustive fibers of the shared-atom relation block: row coordinate values
 and the total number of selected alpha points are precisely the invariants. -/
theorem sharedAtomBlock_subset_collision {m u : ℕ}
    (S T : Finset (SharedIndex m u)) :
    (∑ a ∈ S, sharedPoint a = ∑ a ∈ T, sharedPoint a) ↔
      sharedAlphaCount S = sharedAlphaCount T ∧
      ∀ i j, sharedRowValue S i j = sharedRowValue T i j := by
  constructor
  · intro he
    constructor
    · have h := congrFun he none
      rw [sum_sharedPoint_omega, sum_sharedPoint_omega] at h
      omega
    · intro i j
      have h := congrFun he (some (i,j))
      simpa only [sum_sharedPoint_row] using h
  · rintro ⟨hc,hr⟩
    funext a
    rcases a with _ | ⟨i,j⟩
    · rw [sum_sharedPoint_omega, sum_sharedPoint_omega, hc]
    · rw [sum_sharedPoint_row, sum_sharedPoint_row, hr]

theorem sharedPoint_injective {m u : ℕ} (hm : 2 ≤ m) :
    Function.Injective (sharedPoint (m := m) (u := u)) := by
  rintro ⟨i, _ | j⟩ ⟨k, _ | l⟩ he
  · have h := congrFun he (some (i, ⟨0, by omega⟩))
    simp only [sharedPoint, ite_true] at h
    split_ifs at h with hik
    · subst k; rfl
    · norm_num at h
  · have h := congrFun he none
    norm_num [sharedPoint] at h
  · have h := congrFun he none
    norm_num [sharedPoint] at h
  · have h := congrFun he (some (i,j))
    simp only [sharedPoint, ite_true] at h
    split_ifs at h with heq
    · have hh : (i,j)=(k,l) := Option.some.inj heq
      cases hh
      rfl
    · norm_num at h

theorem card_sharedAtomBlock (m u : ℕ) (hm : 2 ≤ m) :
    (sharedAtomBlock m u).card = m*u := by
  rw [sharedAtomBlock, Finset.card_image_of_injective _ (sharedPoint_injective hm)]
  simp
  rw [show m-1+1=m by omega]
  exact Nat.mul_comm u m

/-- A linear functional recovers the size of each subset from its sum. -/
def sharedDegree {m u : ℕ} (v : SharedLattice m u) : ℤ :=
  (∑ i : Fin u, ∑ j : Fin (m-1), v (some (i,j))) + (m-2 : ℤ)*v none

theorem sharedDegree_point {m u : ℕ} (hm : 2 ≤ m) (a : SharedIndex m u) :
    sharedDegree (sharedPoint a) = 1 := by
  rcases a with ⟨i, _ | j⟩
  · simp [sharedDegree, sharedPoint]
    omega
  · simp [sharedDegree, sharedPoint, ite_and]

theorem sharedDegree_sum {m u : ℕ} (S : Finset (SharedIndex m u)) :
    sharedDegree (∑ a ∈ S, sharedPoint a) = ∑ a ∈ S, sharedDegree (sharedPoint a) := by
  unfold sharedDegree
  simp only [Finset.sum_apply, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i : Fin u, ∑ a ∈ S, ∑ j : Fin (m-1), sharedPoint a (some (i,j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem sharedAtomBlock_subset_card_eq {m u : ℕ} (hm : 2 ≤ m)
    (S T : Finset (SharedIndex m u))
    (he : ∑ a ∈ S, sharedPoint a = ∑ a ∈ T, sharedPoint a) : S.card = T.card := by
  have h := congrArg sharedDegree he
  rw [sharedDegree_sum, sharedDegree_sum] at h
  simp only [sharedDegree_point hm, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

end SumsetRanges
