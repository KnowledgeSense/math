import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def gramFirst (X : Matrix (Fin 2) J ℝ) : ℝ := ∑ j, X 0 j ^ 2
def gramSecond (X : Matrix (Fin 2) J ℝ) : ℝ := ∑ j, X 1 j ^ 2
def gramCross (X : Matrix (Fin 2) J ℝ) : ℝ := ∑ j, X 0 j * X 1 j

def gramFiber (a b c : ℝ) : Set (Matrix (Fin 2) J ℝ) :=
  {X | (∀ i j, 0 ≤ X i j) ∧ gramFirst X = a ∧ gramSecond X = b ∧ gramCross X = c}

theorem gramFiber_closed (a b c : ℝ) : IsClosed (gramFiber (J := J) a b c) := by
  have hpos : IsClosed {X : Matrix (Fin 2) J ℝ | ∀ i j, 0 ≤ X i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const (by fun_prop)
  have hA : IsClosed {X : Matrix (Fin 2) J ℝ | gramFirst X = a} :=
    isClosed_eq (by unfold gramFirst; fun_prop) continuous_const
  have hB : IsClosed {X : Matrix (Fin 2) J ℝ | gramSecond X = b} :=
    isClosed_eq (by unfold gramSecond; fun_prop) continuous_const
  have hC : IsClosed {X : Matrix (Fin 2) J ℝ | gramCross X = c} :=
    isClosed_eq (by unfold gramCross; fun_prop) continuous_const
  simpa only [gramFiber, Set.ofPred_and] using hpos.inter (hA.inter (hB.inter hC))

theorem gramFiber_coordinate_bound {a b c : ℝ} {X : Matrix (Fin 2) J ℝ}
    (hX : X ∈ gramFiber a b c) (i : Fin 2) (j : J) :
    X i j ∈ Set.Icc 0 (Real.sqrt (a + b)) := by
  have hA : gramFirst X = a := hX.2.1
  have hB : gramSecond X = b := hX.2.2.1
  have ha : 0 ≤ a := by rw [← hA]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ b := by rw [← hB]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : X i j ^ 2 ≤ a + b := by
    fin_cases i
    · change X 0 j ^ 2 ≤ a + b
      have h := Finset.single_le_sum (fun k _ => sq_nonneg (X 0 k)) (Finset.mem_univ j)
      change X 0 j ^ 2 ≤ gramFirst X at h
      rw [hA] at h
      linarith
    · change X 1 j ^ 2 ≤ a + b
      have h := Finset.single_le_sum (fun k _ => sq_nonneg (X 1 k)) (Finset.mem_univ j)
      change X 1 j ^ 2 ≤ gramSecond X at h
      rw [hB] at h
      linarith
  have hroot := Real.sq_sqrt (add_nonneg ha hb)
  have hrootNonneg := Real.sqrt_nonneg (a + b)
  exact ⟨hX.1 i j, by nlinarith⟩

theorem gramFiber_compact (a b c : ℝ) : IsCompact (gramFiber (J := J) a b c) := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 2 =>
      Set.pi Set.univ fun _ : J => Set.Icc 0 (Real.sqrt (a + b))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (gramFiber_closed a b c)
  intro X hX
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  exact gramFiber_coordinate_bound hX

end ResearchMain.DiagonalSchatten
