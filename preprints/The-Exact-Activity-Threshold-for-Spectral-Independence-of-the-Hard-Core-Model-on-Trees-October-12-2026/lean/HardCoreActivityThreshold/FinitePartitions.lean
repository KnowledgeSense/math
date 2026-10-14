import HardCoreActivityThreshold.EqualPartitions
import HardCoreActivityThreshold.PartitionTransfers
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace HardCoreActivityThreshold

open Set Finset

noncomputable def partitionTotal {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑i,a i
noncomputable def partitionCost {n : ℕ} (a : Fin n → ℝ) : ℝ := ∑i,scalarPartitionFunction (a i)
def partitionDomain (n : ℕ) (Y : ℝ) : Set (Fin n → ℝ) :=
  {a | (∀i,a i∈Icc 0 criticalEndpoint) ∧ partitionTotal a=Y}

theorem partitionDomain_compact (n : ℕ) (Y : ℝ) : IsCompact (partitionDomain n Y) := by
  have hc : IsCompact {a : Fin n → ℝ | ∀i,a i∈Icc 0 criticalEndpoint} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hf : Continuous (partitionTotal (n := n)) := by unfold partitionTotal; fun_prop
  exact hc.inter_right (isClosed_eq hf continuous_const)

theorem partitionCost_continuousOn (n : ℕ) (Y : ℝ) :
    ContinuousOn (partitionCost (n := n)) (partitionDomain n Y) := by
  apply continuousOn_finsetSum
  intro i hi
  apply partitionFunction_continuousOn.comp (continuous_apply i).continuousOn
  intro a ha
  exact ha.1 i

theorem partitionCost_maximizer {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀i,a i∈Icc 0 criticalEndpoint) :
    ∃b∈partitionDomain n (partitionTotal a),IsMaxOn partitionCost (partitionDomain n (partitionTotal a)) b :=
  (partitionDomain_compact n _).exists_isMaxOn ⟨a,ha,rfl⟩ (partitionCost_continuousOn n _)

theorem sum_map_update {n : ℕ} (a : Fin n → ℝ) (φ : ℝ → ℝ) (i : Fin n) (v : ℝ) :
    (∑k,φ (Function.update a i v k))=(∑k,φ (a k))-φ (a i)+φ v := by
  have he : (fun k => φ (Function.update a i v k))=Function.update (fun k => φ (a k)) i (φ v) := by
    funext k
    by_cases hk : k=i
    · subst k; simp
    · simp [Function.update_of_ne hk]
  rw [he,Finset.sum_update_of_mem (mem_univ i)]
  have h := Finset.sum_update_of_mem (mem_univ i) (fun k => φ (a k)) (φ (a i))
  simp only [Function.update_eq_self] at h
  linarith

noncomputable def partitionTransfer {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update (Function.update a i (a i+t)) j (a j-t)

theorem partitionTransfer_total {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) (hij : i≠j) (t : ℝ) :
    partitionTotal (partitionTransfer a i j t)=partitionTotal a := by
  unfold partitionTotal partitionTransfer
  rw [show (∑k,Function.update (Function.update a i (a i+t)) j (a j-t) k)=
      (∑k,id (Function.update (Function.update a i (a i+t)) j (a j-t) k)) by rfl]
  rw [sum_map_update,sum_map_update]
  simp [Function.update_of_ne hij.symm]
  ring

theorem partitionTransfer_cost {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) (hij : i≠j) (t : ℝ) :
    partitionCost (partitionTransfer a i j t)=partitionCost a-scalarPartitionFunction (a i)-
      scalarPartitionFunction (a j)+transferFunction (a i) (a j) t := by
  unfold partitionCost partitionTransfer
  rw [sum_map_update,sum_map_update]
  simp only [Function.update_of_ne hij.symm]
  unfold transferFunction
  ring

end HardCoreActivityThreshold
