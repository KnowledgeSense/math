import ASR312.AfterEmptyRow

namespace ASR312

noncomputable def gappedColumn {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) (i : Fin n) :
    Fin (r+n) := by
  classical
  have hmn : m ≤ n := by have hh := Finset.card_le_univ s; simpa [hs] using hh
  exact if h : i ∈ s then
    Fin.castLE (by omega : r+m ≤ r+n) (completionColumn A hc ((s.orderIsoOfFin hs).symm ⟨i,h⟩))
  else ⟨r+m+(subsetRank sᶜ ⟨i,by simpa using h⟩).val,by
    have hb := (subsetRank sᶜ ⟨i,by simpa using h⟩).isLt
    have hcard := Finset.card_compl s
    simp only [Fintype.card_fin,hs] at hcard
    omega⟩

theorem gappedColumn_mem {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (i : Fin n) (hi : i ∈ s) :
    (gappedColumn A hc s hs i).val = (completionColumn A hc ((s.orderIsoOfFin hs).symm ⟨i,hi⟩)).val := by
  classical
  simp [gappedColumn,hi]

theorem gappedColumn_notMem {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (i : Fin n) (hi : i ∉ s) :
    (gappedColumn A hc s hs i).val = r+m+(subsetRank sᶜ ⟨i,by simpa using hi⟩).val := by
  classical
  simp [gappedColumn,hi]

theorem gappedColumn_lt_iff {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) (i : Fin n) :
    (gappedColumn A hc s hs i).val < r+m ↔ i ∈ s := by
  classical
  by_cases hi : i ∈ s
  · rw [gappedColumn_mem A hc s hs i hi]
    simp only [hi,iff_true]
    exact (completionColumn A hc _).isLt
  · rw [gappedColumn_notMem A hc s hs i hi]
    simp [hi]

theorem gappedColumn_small_anti {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (i j : Fin n) (hij : i < j) (hi : i ∈ s) (hj : j ∈ s) :
    gappedColumn A hc s hs j < gappedColumn A hc s hs i := by
  change (gappedColumn A hc s hs j).val < (gappedColumn A hc s hs i).val
  rw [gappedColumn_mem A hc s hs i hi,gappedColumn_mem A hc s hs j hj]
  exact completionColumn_strictAnti A hc ((s.orderIsoOfFin hs).symm.strictMono
    (show (⟨i,hi⟩ : s) < ⟨j,hj⟩ from hij))

theorem gappedColumn_large_mono {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (i j : Fin n) (hij : i < j) (hi : i ∉ s) (hj : j ∉ s) :
    gappedColumn A hc s hs i < gappedColumn A hc s hs j := by
  classical
  change (gappedColumn A hc s hs i).val < (gappedColumn A hc s hs j).val
  rw [gappedColumn_notMem A hc s hs i hi,gappedColumn_notMem A hc s hs j hj]
  exact Nat.add_lt_add_left (subsetRank_strictMono sᶜ
    (show (⟨i,by simpa using hi⟩ : (sᶜ : Finset (Fin n))) < ⟨j,by simpa using hj⟩ from hij)) _

theorem gappedColumn_injective {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) :
    Function.Injective (gappedColumn A hc s hs) := by
  classical
  intro i j hij
  have hm : i ∈ s ↔ j ∈ s := by
    rw [← gappedColumn_lt_iff A hc s hs i,← gappedColumn_lt_iff A hc s hs j,hij]
  by_cases hi : i ∈ s
  · have hj := hm.mp hi
    have hv := congrArg Fin.val hij
    rw [gappedColumn_mem A hc s hs i hi,gappedColumn_mem A hc s hs j hj] at hv
    have hr := completionColumn_injective A hc (Fin.ext hv)
    exact congrArg Subtype.val ((s.orderIsoOfFin hs).symm.injective hr)
  · have hj : j ∉ s := fun h => hi (hm.mpr h)
    have hv := congrArg Fin.val hij
    rw [gappedColumn_notMem A hc s hs i hi,gappedColumn_notMem A hc s hs j hj] at hv
    have hr : subsetRank sᶜ ⟨i,by simpa using hi⟩ = subsetRank sᶜ ⟨j,by simpa using hj⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (subsetRank_injective sᶜ hr)

theorem gappedColumn_small_surjective {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (j : Fin (r+m)) (hj : j ∈ zeroSumColumns A) : ∃ i, (gappedColumn A hc s hs i).val = j.val := by
  obtain ⟨q,hq⟩ := completionColumn_surjective A hc j hj
  let i := (s.orderIsoOfFin hs) q
  refine ⟨i.val,?_⟩
  rw [gappedColumn_mem A hc s hs i.val i.property]
  change (completionColumn A hc ((s.orderIsoOfFin hs).symm ((s.orderIsoOfFin hs) q))).val = j.val
  rw [OrderIso.symm_apply_apply,hq]

theorem gappedColumn_large_surjective {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (j : Fin (r+n)) (hj : r+m ≤ j.val) : ∃ i, gappedColumn A hc s hs i = j := by
  classical
  have hm : m ≤ n := by have hh := Finset.card_le_univ s; simpa [hs] using hh
  have hcard : sᶜ.card = n-m := by simp [Finset.card_compl,hs]
  let q : Fin sᶜ.card := ⟨j.val-(r+m),by rw [hcard]; omega⟩
  let i := (sᶜ.orderIsoOfFin rfl) q
  have hi : i.val ∉ s := Finset.mem_compl.mp i.property
  refine ⟨i.val,Fin.ext ?_⟩
  rw [gappedColumn_notMem A hc s hs i.val hi]
  have he : subsetRank sᶜ ⟨i.val,i.property⟩ = q :=
    (sᶜ.orderIsoOfFin rfl).symm_apply_apply q
  rw [he]
  dsimp [q]
  omega

theorem gappedColumn_small_range_iff {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (j : Fin (r+m)) : (∃ i, (gappedColumn A hc s hs i).val = j.val) ↔ j ∈ zeroSumColumns A := by
  constructor
  · rintro ⟨i,hi⟩
    have him : i ∈ s := (gappedColumn_lt_iff A hc s hs i).mp (by rw [hi]; exact j.isLt)
    rw [gappedColumn_mem A hc s hs i him] at hi
    have hj := Fin.ext hi
    exact hj ▸ completionColumn_mem A hc _
  · exact gappedColumn_small_surjective A hc s hs j

end ASR312
