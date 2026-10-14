import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

def networkUnit {α : Type*} [DecidableEq α] : Option α → α → ℤ
  | none => 0
  | some a => Pi.single a 1

def IsNetworkColumn {α : Type*} [DecidableEq α] (v : α → ℤ) : Prop :=
  ∃ a b : Option α, ∀ i, v i = networkUnit a i - networkUnit b i

theorem networkUnit_pullback {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (a : Option β) :
    ∃ b : Option α, ∀ i, networkUnit a (f i) = networkUnit b i := by
  classical
  cases a with
  | none => exact ⟨none, fun _ => rfl⟩
  | some a =>
    by_cases h : ∃ i, f i = a
    · obtain ⟨i, rfl⟩ := h
      refine ⟨some i, ?_⟩
      intro j
      simp [networkUnit, Pi.single_apply, hf.eq_iff]
    · refine ⟨none, ?_⟩
      intro i
      have hi : f i ≠ a := fun he => h ⟨i, he⟩
      simp [networkUnit, hi]

theorem IsNetworkColumn.pullback {α β : Type*} [DecidableEq α] [DecidableEq β]
    {v : β → ℤ} (hv : IsNetworkColumn v) (f : α → β)
    (hf : Function.Injective f) : IsNetworkColumn (fun i => v (f i)) := by
  obtain ⟨a, b, h⟩ := hv
  obtain ⟨a', ha⟩ := networkUnit_pullback f hf a
  obtain ⟨b', hb⟩ := networkUnit_pullback f hf b
  refine ⟨a', b', ?_⟩
  intro i
  change v (f i) = networkUnit a' i - networkUnit b' i
  rw [h, ha, hb]

theorem networkColumn_sum_or_unit {α : Type*} [Fintype α] [DecidableEq α]
    {v : α → ℤ} (hv : IsNetworkColumn v) :
    (∑ i, v i) = 0 ∨
      ∃ i : α, ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
        ∀ j, v j = if j = i then c else 0 := by
  classical
  obtain ⟨a, b, h⟩ := hv
  have hv' : v = fun i => networkUnit a i - networkUnit b i := funext h
  rw [hv']
  cases a with
  | none =>
    cases b with
    | none => exact Or.inl (by simp [networkUnit])
    | some b =>
      refine Or.inr ⟨b, -1, Or.inr rfl, ?_⟩
      intro j
      by_cases hj : j = b <;> simp [networkUnit, hj]
  | some a =>
    cases b with
    | none =>
      refine Or.inr ⟨a, 1, Or.inl rfl, ?_⟩
      intro j
      by_cases hj : j = a <;> simp [networkUnit, hj]
    | some b =>
      exact Or.inl (by simp [Finset.sum_sub_distrib, networkUnit])

theorem networkMatrix_det_abs (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ j, IsNetworkColumn (fun i => A i j)) : A.det.natAbs ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hzero : ∀ j, (∑ i, A i j) = 0
    · have hdet : A.det = 0 := by
        apply Matrix.det_eq_zero_of_not_linearIndependent_rows
        intro hlin
        have hsum : (∑ i : Fin (n + 1), (1 : ℤ) • A i) = 0 := by
          simp only [one_smul]
          funext j
          change (∑ i : Fin (n + 1), fun k : Fin (n + 1) => A i k) j = 0
          rw [Finset.sum_apply]
          exact hzero j
        have h := (linearIndependent_iff'.mp hlin) Finset.univ (fun _ => (1 : ℤ))
          hsum (0 : Fin (n + 1)) (Finset.mem_univ _)
        norm_num at h
      simp [hdet]
    · obtain ⟨j, hj⟩ := not_forall.mp hzero
      obtain hsum | ⟨i, c, hc, hcol⟩ := networkColumn_sum_or_unit (hA j)
      · exact (hj hsum).elim
      · let B := A.submatrix i.succAbove j.succAbove
        have hB : ∀ l, IsNetworkColumn (fun k => B k l) := by
          intro l
          exact (hA (j.succAbove l)).pullback i.succAbove Fin.succAbove_right_injective
        have hminor := ih B hB
        have hdet : A.det = (-1 : ℤ) ^ (i.val + j.val) * c * B.det := by
          rw [Matrix.det_succ_column A j]
          calc
            _ = (-1 : ℤ) ^ (i.val + j.val) * A i j *
                (A.submatrix i.succAbove j.succAbove).det := by
              apply Finset.sum_eq_single i
              · intro k hk hki
                rw [hcol k, ite_eq_right hki, mul_zero, zero_mul]
              · intro hi
                exact (hi (Finset.mem_univ i)).elim
            _ = _ := by rw [hcol i, ite_eq_left rfl]
        rw [hdet, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
        rcases hc with rfl | rfl <;> simpa using hminor

theorem networkMatrix_totallyUnimodular {α β : Type*} [DecidableEq α]
    (A : Matrix α β ℤ) (hA : ∀ j, IsNetworkColumn (fun i => A i j)) :
    A.IsTotallyUnimodular := by
  classical
  intro n f g hf hg
  have hsub : ∀ j, IsNetworkColumn (fun i => (A.submatrix f g) i j) :=
    fun j => (hA (g j)).pullback f hf
  have h := networkMatrix_det_abs n (A.submatrix f g) hsub
  have h' : (A.submatrix f g).det = 0 ∨
      (A.submatrix f g).det = 1 ∨ (A.submatrix f g).det = -1 := by
    cases hd : (A.submatrix f g).det <;> simp [hd] at h ⊢ <;> omega
  rcases h' with h' | h' | h'
  · exact ⟨0, by simpa using h'.symm⟩
  · exact ⟨1, by simpa using h'.symm⟩
  · exact ⟨-1, by simpa using h'.symm⟩

end ResearchMain.PreorderGamma.SimplicialRealization
