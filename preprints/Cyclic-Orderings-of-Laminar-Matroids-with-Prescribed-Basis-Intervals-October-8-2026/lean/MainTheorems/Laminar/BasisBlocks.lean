import MainTheorems.Laminar.SubtreeRows
import Mathlib.Combinatorics.Matroid.Rank.ENat

namespace ResearchMain.Laminar

open Classical

def nextRow {k : ℕ} (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩

theorem nextRow_ne {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : nextRow i ≠ i := by
  intro h
  have he := congrArg Fin.val h
  change (i.val + 1) % k = i.val at he
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi] at he
    omega
  · have hi' : i.val + 1 = k := by omega
    rw [hi', Nat.mod_self] at he
    omega

theorem window_same_row {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (next : R → R) (i : R) (t : ℕ) (hnext : next i = i) : window order next i t = rows i := by
  unfold window
  rw [hnext]
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (suffix_subset order i t) (prefix_subset order i t)
  · intro e he
    let j := (order i).symm ⟨e, he⟩
    have heq : (order i j).val = e := congrArg Subtype.val ((order i).apply_symm_apply ⟨e, he⟩)
    rcases lt_or_ge j.val t with hj | hj
    · exact Finset.mem_union_right _ (heq ▸ (mem_prefix order i t j).mpr hj)
    · exact Finset.mem_union_left _ (heq ▸ (mem_suffix order i t j).mpr hj)

theorem window_card_eq {R E : Type*} {rows : R → Finset E} (order : Ordering rows)
    (next : R → R) (i : R) {r t : ℕ} (hi : (rows i).card = r)
    (hn : (rows (next i)).card = r) (hd : Disjoint (rows i) (rows (next i))) (ht : t ≤ r) :
    (window order next i t).card = r := by
  have hd' : Disjoint (rowSuffix order i t) (rowPrefix order (next i) t) :=
    hd.mono (suffix_subset order i t) (prefix_subset order (next i) t)
  rw [window, Finset.card_union_of_disjoint hd', suffix_card, prefix_card, hi, hn,
    min_eq_right ht, Nat.sub_add_cancel ht]

noncomputable def IsLaminar {E : Type*} (M : Matroid E) : Prop :=
  ∃ family : Finset (Finset E), ∃ capacity : Finset E → ℕ,
    LaminarFamily family ∧ (∀ F ∈ family, (F : Set E) ⊆ M.E) ∧
    ∀ I : Finset E, M.Indep (I : Set E) ↔ (I : Set E) ⊆ M.E ∧ Feasible family capacity I

theorem prescribed_basis_blocks {E : Type*} (M : Matroid E) (hlam : IsLaminar M)
    {k r : ℕ} (hk : 1 ≤ k) (hrank : M.eRank = (r : ℕ∞)) (rows : Fin k → Finset E)
    (hbases : ∀ i, M.IsBase (rows i : Set E))
    (hdisj : ∀ i j, i ≠ j → Disjoint (rows i) (rows j))
    (hcover : ((Finset.univ.biUnion rows : Finset E) : Set E) = M.E) :
    ∃ order : Ordering rows, ∀ i t, t ≤ r → M.IsBase (window order nextRow i t : Set E) := by
  obtain ⟨family, capacity, hfamily, _, hindep⟩ := hlam
  let ground := Finset.univ.biUnion rows
  have hrows : ∀ i, rows i ⊆ ground := fun i e he =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩
  have hcard : ∀ i, (rows i).card = r := by
    intro i
    have he := (hbases i).encard_eq_eRank
    rw [Set.encard_coe_eq_coe_finsetCard, hrank] at he
    exact_mod_cast he
  have hfeasible : ∀ i, Feasible family capacity (rows i) := fun i =>
    (hindep (rows i)).mp (hbases i).indep |>.2
  obtain ⟨order, hwin⟩ := capacity_ordering nextRow family capacity ground r rows hfamily
    hrows (fun i => (hcard i).le) hfeasible
  refine ⟨order, ?_⟩
  intro i t ht
  by_cases hk1 : k = 1
  · have hn : nextRow i = i := by subst k; exact Subsingleton.elim _ _
    rw [window_same_row order nextRow i t hn]
    exact hbases i
  · have hk2 : 2 ≤ k := by omega
    have hground : (window order nextRow i t : Set E) ⊆ M.E := by
      rw [← hcover]
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hrows i (suffix_subset order i t he)
      · exact hrows (nextRow i) (prefix_subset order (nextRow i) t he)
    have hI := (hindep (window order nextRow i t)).mpr ⟨hground, hwin i t ht⟩
    apply hI.isBase_of_eRk_ge (Finset.finite_toSet _)
    rw [hI.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard,
      window_card_eq order nextRow i (hcard i) (hcard (nextRow i))
        (hdisj i (nextRow i) (nextRow_ne hk2 i).symm) ht, hrank]

end ResearchMain.Laminar
