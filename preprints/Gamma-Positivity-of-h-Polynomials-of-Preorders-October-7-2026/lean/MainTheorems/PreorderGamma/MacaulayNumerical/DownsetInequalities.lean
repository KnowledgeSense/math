import MainTheorems.PreorderGamma.MacaulayNumerical.ShadowRaiseBound
import Mathlib.Data.Fintype.EquivFin

namespace ResearchMain.PreorderGamma.MacaulayNumerical

open Finset.Colex
open scoped FinsetFamily

theorem finite_order_prefix_exists {α : Type*} [LinearOrder α]
    (s : Finset α) (m : ℕ) (hm : m ≤ s.card) :
    ∃ t : Finset α, t.card = m ∧ t ⊆ s ∧
      ∀ a ∈ t, ∀ b ∈ s, b ≤ a → b ∈ t := by
  classical
  let f := s.orderEmbOfCardLe hm
  let t := (Finset.univ : Finset (Fin m)).map f.toEmbedding
  have hts : t ⊆ s := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
    exact s.orderEmbOfCardLe_mem hm i
  refine ⟨t, by simp [t], hts, ?_⟩
  intro a ha b hb hba
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ha
  let o := s.orderIsoOfFin rfl
  let j : Fin s.card := o.symm ⟨b, hb⟩
  have hle : (⟨b, hb⟩ : s) ≤ o (Fin.castLE hm i) := by
    change b ≤ f i
    exact hba
  have hjle : j ≤ Fin.castLE hm i := by
    simpa [j] using o.symm.monotone hle
  have hjnat : j.val ≤ i.val := hjle
  have hjm : j.val < m := lt_of_le_of_lt hjnat i.isLt
  let k : Fin m := ⟨j.val, hjm⟩
  apply Finset.mem_map.mpr
  refine ⟨k, Finset.mem_univ k, ?_⟩
  have hcast : Fin.castLE hm k = j := by apply Fin.ext; rfl
  change (o (Fin.castLE hm k)).val = b
  rw [hcast]
  simp [j]

theorem colex_initial_same_card {n r : ℕ} (A : Finset (Finset (Fin n)))
    (hA : (A : Set (Finset (Fin n))).Sized r) :
    ∃ C : Finset (Finset (Fin n)), IsInitSeg C r ∧ C.card = A.card := by
  classical
  let : Fintype (Colex (Finset (Fin n))) := Fintype.ofEquiv _ toColex
  let all : Finset (Colex (Finset (Fin n))) :=
    Finset.univ.filter fun t => (ofColex t).card = r
  have hsub : A.map toColex.toEmbedding ⊆ all := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    simp [all, hA hs]
  have hbound : A.card ≤ all.card := by
    simpa using Finset.card_le_card hsub
  obtain ⟨D, hDcard, hDsub, hDdown⟩ := finite_order_prefix_exists all A.card hbound
  let C := D.map ofColex.toEmbedding
  have hCsized : (C : Set (Finset (Fin n))).Sized r := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hs
    exact (Finset.mem_filter.mp (hDsub hu)).2
  refine ⟨C, ⟨hCsized, ?_⟩, by simpa [C] using hDcard⟩
  intro s t hs ht
  obtain ⟨u, hu, heu⟩ := Finset.mem_map.mp hs
  change ofColex u = s at heu
  have htall : toColex t ∈ all := by simp [all, ht.2]
  have htu : toColex t ≤ u := by
    rw [← toColex_ofColex u, heu]
    exact ht.1.le
  have htD := hDdown u hu (toColex t) htall htu
  exact Finset.mem_map.mpr ⟨toColex t, htD, ofColex_toColex t⟩

def degreeFamily {V : Type*} [DecidableEq V] (F : Finset (Finset V)) (d : ℕ) :
    Finset (Finset V) := F.filter fun s => s.card = d

theorem degreeFamily_sized {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (d : ℕ) :
    (degreeFamily F d : Set (Finset V)).Sized d := by
  intro s hs
  exact (Finset.mem_filter.mp hs).2

theorem shadow_degree_subset {V : Type*} [DecidableEq V]
    (F : Finset (Finset V))
    (hdown : ∀ s ∈ F, ∀ t ⊆ s, t ∈ F) (d : ℕ) :
    ∂ (degreeFamily F (d + 1)) ⊆ degreeFamily F d := by
  intro t ht
  obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_shadow_iff.mp ht
  obtain ⟨hsF, hcard⟩ := Finset.mem_filter.mp hs
  apply Finset.mem_filter.mpr
  refine ⟨hdown s hsF (s.erase a) (Finset.erase_subset a s), ?_⟩
  rw [Finset.card_erase_of_mem ha, hcard]
  omega

theorem squarefree_downset_macaulay_fin {n : ℕ} (F : Finset (Finset (Fin n)))
    (hdown : ∀ s ∈ F, ∀ t ⊆ s, t ∈ F) {d : ℕ} (hd : 0 < d) :
    (degreeFamily F (d + 1)).card ≤ macaulayRaise d (degreeFamily F d).card := by
  classical
  let A := degreeFamily F (d + 1)
  by_cases hzero : A.card = 0
  · change A.card ≤ _
    rw [hzero]
    exact Nat.zero_le _
  obtain ⟨C, hC, hcard⟩ := colex_initial_same_card A (degreeFamily_sized F (d + 1))
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hs, hCs⟩ := hC.exists_initSeg hCne
  have hKK : (∂ C).card ≤ (∂ A).card :=
    Finset.kruskal_katona (degreeFamily_sized F (d + 1)) hcard.le hC
  have hshadow : (∂ A).card ≤ (degreeFamily F d).card :=
    Finset.card_le_card (shadow_degree_subset F hdown d)
  have hraise : C.card ≤ macaulayRaise d ((∂ C).card - 1) := by
    rw [hCs]
    exact initSeg_card_le_macaulayRaise_shadow hs hd
  calc
    (degreeFamily F (d + 1)).card = C.card := hcard.symm
    _ ≤ macaulayRaise d ((∂ C).card - 1) := hraise
    _ ≤ macaulayRaise d (degreeFamily F d).card :=
      macaulayRaise_mono d ((Nat.sub_le _ _).trans (hKK.trans hshadow))

theorem squarefree_downset_macaulay {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V))
    (hdown : ∀ s ∈ F, ∀ t ⊆ s, t ∈ F) {d : ℕ} (hd : 0 < d) :
    (degreeFamily F (d + 1)).card ≤ macaulayRaise d (degreeFamily F d).card := by
  classical
  let e := Fintype.equivFin V
  let ee := e.finsetCongr
  let H := F.map ee.toEmbedding
  have hHdown : ∀ s ∈ H, ∀ t ⊆ s, t ∈ H := by
    intro s hs t hts
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hs
    have hpre : ee.symm t ⊆ u := by
      apply (Finset.map_subset_map (f := e.toEmbedding)).mp
      change ee (ee.symm t) ⊆ ee u
      rw [ee.apply_symm_apply]
      exact hts
    exact Finset.mem_map.mpr ⟨ee.symm t, hdown u hu _ hpre, ee.apply_symm_apply t⟩
  have hcount (j : ℕ) : (degreeFamily H j).card = (degreeFamily F j).card := by
    simp [degreeFamily, H, Finset.filter_map, ee, Equiv.finsetCongr_apply]
  have h := squarefree_downset_macaulay_fin H hHdown hd
  simpa only [hcount] using h

end ResearchMain.PreorderGamma.MacaulayNumerical
