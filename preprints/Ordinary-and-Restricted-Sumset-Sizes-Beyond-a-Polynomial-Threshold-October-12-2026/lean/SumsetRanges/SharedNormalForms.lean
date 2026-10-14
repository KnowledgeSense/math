import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import SumsetRanges.CanonicalRows
import Mathlib.Data.Fintype.Powerset

open Finset
namespace SumsetRanges

noncomputable def normalizeRows {m u : ℕ} (R : Fin u → Finset (RowIndex m))
    (i : Fin u) : Finset (RowIndex m) := if i ∈ ambiguousRows R then ∅ else R i

theorem normalizeRows_valid {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    ValidRows (ambiguousRows R) (normalizeRows R) := by
  constructor
  · intro i hi
    simp [normalizeRows,hi]
  · intro i hi
    simp only [normalizeRows, ite_eq_right hi]
    simp only [ambiguousRows, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
    exact hi

theorem canonicalRows_normalize {m u : ℕ} (R : Fin u → Finset (RowIndex m)) (p : ℕ) :
    canonicalRows (ambiguousRows R) (normalizeRows R) p =
      canonicalRows (ambiguousRows R) R p := by
  funext i
  by_cases hi : i ∈ ambiguousRows R <;> simp [canonicalRows,normalizeRows,hi]

abbrev SharedNormalData (m u : ℕ) :=
  Σ J : Finset (Fin u), {R : Fin u → Finset (RowIndex m) // ValidRows J R} × Fin (J.card+1)

noncomputable instance sharedNormalDataFintype (m u : ℕ) : Fintype (SharedNormalData m u) := by
  classical
  unfold SharedNormalData
  infer_instance

noncomputable def normalRows {m u : ℕ} (d : SharedNormalData m u) : Fin u → Finset (RowIndex m) :=
  canonicalRows d.1 d.2.1.val d.2.2.val

noncomputable def normalSubset {m u : ℕ} (d : SharedNormalData m u) : Finset (SharedIndex m u) :=
  assembleRows (normalRows d)

noncomputable def normalSum {m u : ℕ} (d : SharedNormalData m u) : SharedLattice m u :=
  ∑ a ∈ normalSubset d, sharedPoint a

noncomputable def normalDegree {m u : ℕ} (d : SharedNormalData m u) : ℕ := (normalSubset d).card

theorem normalSum_injective (m u : ℕ) : Function.Injective (normalSum (m := m) (u := u)) := by
  rintro ⟨J,⟨R,hR⟩,p⟩ ⟨K,⟨T,hT⟩,q⟩ he
  have hh := canonicalRows_data_injective J K R T p.val q.val hR hT
    (by omega) (by omega) he
  obtain ⟨hJ,hR',hp⟩ := hh
  subst K
  subst T
  have hpq : p=q := Fin.ext hp
  subst q
  rfl

noncomputable def normalDataOfRows {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    SharedNormalData m u :=
  ⟨ambiguousRows R, ⟨normalizeRows R, normalizeRows_valid R⟩,
    ⟨(ambiguousAlphaRows R).card, Nat.lt_succ_of_le
      (Finset.card_le_card (ambiguousAlphaRows_subset R))⟩⟩

theorem normalDataOfRows_sum {m u : ℕ} (R : Fin u → Finset (RowIndex m)) :
    normalSum (normalDataOfRows R) = ∑ a ∈ assembleRows R, sharedPoint a := by
  unfold normalSum normalSubset normalRows normalDataOfRows
  dsimp
  rw [canonicalRows_normalize]
  exact canonicalRows_same_sum R

theorem normalDataOfRows_degree {m u : ℕ} (hm : 2 ≤ m)
    (R : Fin u → Finset (RowIndex m)) :
    normalDegree (normalDataOfRows R) = (assembleRows R).card :=
  sharedAtomBlock_subset_card_eq hm _ _ (normalDataOfRows_sum R)

/-- Exact finite enumeration of distinct sums in the shared-atom block, with
 one normal form per sum and no sum omitted. -/
theorem sharedAtomBlock_normal_forms (m u q : ℕ) (hm : 2 ≤ m) :
    restrictedSums (sharedAtomBlock m u) q =
      (Finset.univ.filter (fun d : SharedNormalData m u => normalDegree d=q)).image normalSum := by
  classical
  let f : SharedIndex m u ↪ SharedLattice m u := ⟨sharedPoint,sharedPoint_injective hm⟩
  have hf : sharedAtomBlock m u = (Finset.univ : Finset (SharedIndex m u)).map f := by
    simp [sharedAtomBlock,Finset.map_eq_image,f]
  rw [hf,restrictedSums_map]
  ext x
  constructor
  · intro hx
    obtain ⟨S,hS,hx⟩ := Finset.mem_image.mp hx
    have hcard := (Finset.mem_powersetCard.mp hS).2
    refine Finset.mem_image.mpr ⟨normalDataOfRows (rowPart S), ?_, ?_⟩
    · simp [normalDataOfRows_degree hm, hcard]
    · rw [normalDataOfRows_sum, assembleRows_rowPart]
      exact hx
  · intro hx
    obtain ⟨d,hd,hx⟩ := Finset.mem_image.mp hx
    have hcard := (Finset.mem_filter.mp hd).2
    refine Finset.mem_image.mpr ⟨normalSubset d, ?_, hx⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩

theorem card_sharedAtomBlock_normal_forms (m u q : ℕ) (hm : 2 ≤ m) :
    (restrictedSums (sharedAtomBlock m u) q).card =
      (Finset.univ.filter (fun d : SharedNormalData m u => normalDegree d=q)).card := by
  classical
  rw [sharedAtomBlock_normal_forms m u q hm,
    Finset.card_image_of_injective _ (normalSum_injective m u)]

end SumsetRanges
