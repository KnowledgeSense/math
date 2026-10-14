import SumsetRanges.OrdinaryImages
import SumsetRanges.Kneser.MulStab

open Finset
open scoped Pointwise
namespace SumsetRanges

theorem zero_mem_ordinarySums_of_zero_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (hzero : 0 ∈ S) (h : ℕ) : 0 ∈ ordinarySums S h := by
  induction h with
  | zero => simp [ordinarySums]
  | succ h ih => exact Finset.mem_add.mpr ⟨0, hzero, 0, ih, zero_add 0⟩

/-- A proper sumset cannot already be the stabilization of its preceding sumset
    when the original set generates the ambient group. -/
theorem ordinarySums_addStab_ssubset {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] (S : Finset G) (h : ℕ) (hzero : 0 ∈ S)
    (hgen : AddSubgroup.closure (S : Set G) = ⊤)
    (hproper : ordinarySums S (h+1) ≠ Finset.univ) :
    ordinarySums S h + (ordinarySums S (h+1)).addStab ⊂ ordinarySums S (h+1) := by
  let P := ordinarySums S h
  let T := ordinarySums S (h+1)
  have hTzero : 0 ∈ T := zero_mem_ordinarySums_of_zero_mem S hzero _
  have hTne : T.Nonempty := ⟨0, hTzero⟩
  have hPT : P ⊆ T := by
    intro x hx
    exact Finset.mem_add.mpr ⟨0, hzero, x, hx, zero_add x⟩
  have hsub : P+T.addStab ⊆ T := by
    simpa only [Finset.add_addStab] using Finset.add_subset_add_right hPT (t := T.addStab)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have hST : S+T = T := by
    calc
      S+T = S+(P+T.addStab) := by rw [heq]
      _ = (S+P)+T.addStab := (add_assoc _ _ _).symm
      _ = T+T.addStab := rfl
      _ = T := Finset.add_addStab T
  have hSstab : S ⊆ T.addStab := (Finset.add_subset_right_iff hTne).mp hST.subset
  have hSsub : (S : Set G) ⊆ AddAction.stabilizer G T := by
    rw [← Finset.coe_addStab hTne]
    exact Finset.coe_subset.mpr hSstab
  have htop : AddAction.stabilizer G T = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (AddSubgroup.closure_le _).mpr hSsub
  apply hproper
  apply Finset.eq_univ_of_forall
  intro x
  have hx : x ∈ T.addStab := by
    have hx' : x ∈ AddAction.stabilizer G T := by rw [htop]; trivial
    change x ∈ (T.addStab : Set G)
    rw [Finset.coe_addStab hTne]
    exact hx'
  have hx0 := (Finset.mem_addStab' hTne).mp hx hTzero
  simpa only [vadd_eq_add, add_zero] using hx0

/-- There is a new coset in the next sumset modulo its own stabilizer. -/
theorem ordinarySums_stabilizer_image_ssubset {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] (S : Finset G) (h : ℕ)
    [DecidableEq (G ⧸ AddAction.stabilizer G (ordinarySums S (h+1)))]
    (hzero : 0 ∈ S)
    (hgen : AddSubgroup.closure (S : Set G) = ⊤)
    (hproper : ordinarySums S (h+1) ≠ Finset.univ) :
    let π := QuotientAddGroup.mk' (AddAction.stabilizer G (ordinarySums S (h+1)))
    (ordinarySums S h).image π ⊂ (ordinarySums S (h+1)).image π := by
  classical
  let T := ordinarySums S (h+1)
  let π := QuotientAddGroup.mk' (AddAction.stabilizer G T)
  have hTne : T.Nonempty := ⟨0, zero_mem_ordinarySums_of_zero_mem S hzero _⟩
  have hPT : ordinarySums S h ⊆ T := by
    intro x hx
    exact Finset.mem_add.mpr ⟨0, hzero, x, hx, zero_add x⟩
  apply (Finset.ssubset_iff_of_subset (Finset.image_subset_image hPT)).mpr
  have hss := ordinarySums_addStab_ssubset S h hzero hgen hproper
  obtain ⟨x, hxT, hxnot⟩ := (Finset.ssubset_iff_of_subset hss.subset).mp hss
  refine ⟨π x, Finset.mem_image.mpr ⟨x, hxT, rfl⟩, ?_⟩
  intro hx
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
  have hdiff : x-y ∈ AddAction.stabilizer G T :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy.symm
  have hd : x-y ∈ T.addStab := by
    change x-y ∈ (T.addStab : Set G)
    rw [Finset.coe_addStab hTne]
    exact hdiff
  apply hxnot
  exact Finset.mem_add.mpr ⟨y, hy, x-y, hd, by simp⟩

end SumsetRanges
