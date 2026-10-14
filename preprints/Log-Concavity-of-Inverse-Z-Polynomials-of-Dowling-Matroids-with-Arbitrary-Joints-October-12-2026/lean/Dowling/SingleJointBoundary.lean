import Dowling.MatroidDeletionColoopY
import Dowling.RetainedDegree

noncomputable section
namespace Dowling
open Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]

theorem fullY_eq_of_card {H : Type*} [Group H] [Fintype H]
    (hc : Fintype.card G=Fintype.card H) (n : ℕ) : fullY G n=fullY H n := by
  apply Polynomial.ext
  intro k
  apply Int.cast_injective (α := ℝ)
  rw [fullY_coeff_real,fullY_coeff_real,hc]

theorem singleJoint_ground_remove_flat [Subsingleton G] {n : ℕ} (i : Fin n) :
    (matroid G n {i}).IsFlat ((matroid G n {i}).E\{Sum.inl i}) := by
  let : NeZero n := ⟨by have := i.isLt; omega⟩
  let p : GainPartition G n := zeroPartition
  have hr : p.code 0=none := rfl
  have hmin : ∀ j,p.code j=none → (0 : Fin n)≤j := fun j _ => Fin.zero_le j
  have hmark : ∀ j∈({i} : Set (Fin n)),p.code j=none → j=i := fun j hj _ => Set.mem_singleton_iff.mp hj
  have he := flatEdges_releaseZeroBlock p 0 hr hmin {i} i hmark
  have had : Admissible ({i} : Set (Fin n)) (p.releaseZeroBlock 0 hr hmin) := by
    intro j hj
    exact False.elim (p.releaseZeroBlock_no_zero 0 hr hmin j hj)
  rw [matroid_ground,← flatEdges_zeroPartition {i},← he]
  exact flatEdges_isFlat _ _ had

/-- With one retained joint and identity gains, that literal joint is a
coloop. Its deletion is the actual jointless braid matroid. -/
theorem configurationY_single_joint [Subsingleton G] {n : ℕ} (i : Fin n) :
    configurationY (G := G) ({i} : Set (Fin n))=(1+Polynomial.X)*fullY G (n-1) := by
  have he : Sum.inl i∈(matroid G n {i}).E := by rw [matroid_ground]; exact Set.mem_singleton i
  have h := matroid_inverseZ_coloop (matroid G n {i}) (Sum.inl i)
    (matroid_empty_isFlat _) he (singleJoint_ground_remove_flat i)
  rw [matroid_delete_joint,actual_inverseZ_eq_configurationY,actual_inverseZ_eq_configurationY] at h
  simp only [Set.sdiff_self] at h
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [trivial_jointless_inverseZ] at h
    have hg : Fintype.card G=Fintype.card Unit := by
      simpa using Fintype.card_eq_one_iff.mpr ⟨(1 : G),fun x => Subsingleton.elim x 1⟩
    rw [← fullY_eq_of_card hg n] at h
    simpa only [Nat.succ_sub_one,mul_comm] using h

end Dowling
