import MainTheorems.WishartBlocks.ContinuousFKG
import MainTheorems.WishartBlocks.ContinuousDensity

namespace ResearchMain.WishartBlocks

open MeasureTheory Bornology
open scoped BigOperators Topology

def intervalLattice (n : ℕ) (a b : ℝ) : Sublattice (Fin n → ℝ) where
  carrier := Set.Icc (fun _ => a) (fun _ => b)
  supClosed' := by
    intro x hx y hy
    exact ⟨le_sup_of_le_left hx.1, sup_le hx.2 hy.2⟩
  infClosed' := by
    intro x hx y hy
    exact ⟨le_inf hx.1 hy.1, inf_le_left.trans hx.2⟩

theorem intervalLattice_bounded (n : ℕ) (a b : ℝ) :
    IsBounded (intervalLattice n a b : Set (Fin n → ℝ)) :=
  Metric.isBounded_Icc _ _

theorem intervalLattice_measurable (n : ℕ) (a b : ℝ) :
    MeasurableSet (intervalLattice n a b : Set (Fin n → ℝ)) :=
  measurableSet_Icc

theorem intervalLattice_frontier_zero (n : ℕ) (a b : ℝ) :
    volume (frontier (intervalLattice n a b : Set (Fin n → ℝ))) = 0 := by
  have hne : ∀ᵐ x : Fin n → ℝ, ∀ i, x i ≠ a ∧ x i ≠ b := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i a).and
      (Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) i b)
  have hnot : ∀ᵐ x : Fin n → ℝ, x ∉ frontier
      (intervalLattice n a b : Set (Fin n → ℝ)) := by
    filter_upwards [hne] with x hx
    intro hfr
    have hclosed : IsClosed (intervalLattice n a b : Set (Fin n → ℝ)) := isClosed_Icc
    have hxI : x ∈ (intervalLattice n a b : Set (Fin n → ℝ)) := by
      exact hclosed.closure_eq ▸ hfr.1
    let U : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Ioo a b
    have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
    have hxU : x ∈ U := by
      intro i _
      exact ⟨lt_of_le_of_ne (hxI.1 i) (Ne.symm (hx i).1),
        lt_of_le_of_ne (hxI.2 i) (hx i).2⟩
    have hUI : U ⊆ (intervalLattice n a b : Set (Fin n → ℝ)) := by
      intro y hy
      exact ⟨fun i => (hy i (by simp)).1.le, fun i => (hy i (by simp)).2.le⟩
    have hi : x ∈ interior (intervalLattice n a b : Set (Fin n → ℝ)) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hxU) hUI)
    exact hfr.2 hi
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnot

theorem eigenvalue_box_association {n : ℕ} (α : ℝ) {a b : ℝ} (ha : 0 < a)
    {F G : (Fin n → ℝ) → ℝ}
    (hcF : Continuous F) (hcG : Continuous G)
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hmF : Monotone F) (hmG : Monotone G) :
    (∫ x in (intervalLattice n a b : Set (Fin n → ℝ)), eigenvalueWeight α x * F x) *
      (∫ x in (intervalLattice n a b : Set (Fin n → ℝ)), eigenvalueWeight α x * G x) ≤
    (∫ x in (intervalLattice n a b : Set (Fin n → ℝ)), eigenvalueWeight α x) *
      (∫ x in (intervalLattice n a b : Set (Fin n → ℝ)),
        eigenvalueWeight α x * (F x * G x)) := by
  have he : regularizedEigenvalueWeight (n := n) α a =ᵐ[volume.restrict
      (intervalLattice n a b : Set (Fin n → ℝ))] eigenvalueWeight α := by
    filter_upwards [self_mem_ae_restrict (intervalLattice_measurable n a b)] with x hx
    exact regularizedEigenvalueWeight_eq α ha hx.1
  have h := continuous_fkg_integral (intervalLattice n a b)
    (intervalLattice_bounded n a b) (intervalLattice_measurable n a b)
    (intervalLattice_frontier_zero n a b)
    (regularizedEigenvalueWeight_continuous α ha n) hcF hcG
    (regularizedEigenvalueWeight_nonneg α ha) hF hG hmF hmG
    (regularizedEigenvalueWeight_lattice α ha)
  have heF : (fun x => regularizedEigenvalueWeight α a x * F x) =ᵐ[volume.restrict
      (intervalLattice n a b : Set (Fin n → ℝ))] fun x => eigenvalueWeight α x * F x := by
    filter_upwards [he] with x hx
    rw [hx]
  have heG : (fun x => regularizedEigenvalueWeight α a x * G x) =ᵐ[volume.restrict
      (intervalLattice n a b : Set (Fin n → ℝ))] fun x => eigenvalueWeight α x * G x := by
    filter_upwards [he] with x hx
    rw [hx]
  have heFG : (fun x => regularizedEigenvalueWeight α a x * (F x * G x)) =ᵐ[volume.restrict
      (intervalLattice n a b : Set (Fin n → ℝ))] fun x => eigenvalueWeight α x * (F x * G x) := by
    filter_upwards [he] with x hx
    rw [hx]
  simpa only [integral_congr_ae he, integral_congr_ae heF, integral_congr_ae heG,
    integral_congr_ae heFG] using h

end ResearchMain.WishartBlocks
