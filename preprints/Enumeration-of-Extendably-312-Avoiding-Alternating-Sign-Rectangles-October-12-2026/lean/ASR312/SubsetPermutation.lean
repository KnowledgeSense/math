import ASR312.PermutationMatrices

namespace ASR312

noncomputable def subsetRank {n : ℕ} (s : Finset (Fin n)) (i : s) : Fin s.card :=
  (s.orderIsoOfFin rfl).symm i

theorem subsetRank_strictMono {n : ℕ} (s : Finset (Fin n)) :
    StrictMono (subsetRank s) := (s.orderIsoOfFin rfl).symm.strictMono

theorem subsetRank_injective {n : ℕ} (s : Finset (Fin n)) :
    Function.Injective (subsetRank s) := (s.orderIsoOfFin rfl).symm.injective

noncomputable def subsetShuffleFun {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : Fin n := by
  classical
  exact if h : i ∈ s then
    ⟨s.card - 1 - (subsetRank s ⟨i,h⟩).val, by
      have hr := (subsetRank s ⟨i,h⟩).isLt
      have hc := Finset.card_le_univ s
      simp only [Fintype.card_fin] at hc
      omega⟩
  else ⟨s.card + (subsetRank sᶜ ⟨i,by simpa using h⟩).val, by
    have hr := (subsetRank sᶜ ⟨i,by simpa using h⟩).isLt
    have hc := Finset.card_compl s
    simp only [Fintype.card_fin] at hc
    have hs := Finset.card_le_univ s
    simp only [Fintype.card_fin] at hs
    omega⟩

theorem subsetShuffleFun_mem {n : ℕ} (s : Finset (Fin n)) (i : Fin n) (h : i ∈ s) :
    (subsetShuffleFun s i).val = s.card - 1 - (subsetRank s ⟨i,h⟩).val := by
  classical
  simp [subsetShuffleFun,h]

theorem subsetShuffleFun_notMem {n : ℕ} (s : Finset (Fin n)) (i : Fin n) (h : i ∉ s) :
    (subsetShuffleFun s i).val = s.card + (subsetRank sᶜ ⟨i,by simpa using h⟩).val := by
  classical
  simp [subsetShuffleFun,h]

theorem subsetShuffleFun_lt_iff {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    (subsetShuffleFun s i).val < s.card ↔ i ∈ s := by
  classical
  by_cases h : i ∈ s
  · rw [subsetShuffleFun_mem s i h]
    have hr := (subsetRank s ⟨i,h⟩).isLt
    simp only [h,iff_true]
    omega
  · rw [subsetShuffleFun_notMem s i h]
    simp [h]

theorem subsetShuffleFun_injective {n : ℕ} (s : Finset (Fin n)) :
    Function.Injective (subsetShuffleFun s) := by
  classical
  intro i j hij
  have hv := congrArg Fin.val hij
  have hm : i ∈ s ↔ j ∈ s := by
    rw [← subsetShuffleFun_lt_iff s i, ← subsetShuffleFun_lt_iff s j,hij]
  by_cases hi : i ∈ s
  · have hj := hm.mp hi
    rw [subsetShuffleFun_mem s i hi,subsetShuffleFun_mem s j hj] at hv
    have hri := (subsetRank s ⟨i,hi⟩).isLt
    have hrj := (subsetRank s ⟨j,hj⟩).isLt
    have hr : subsetRank s ⟨i,hi⟩ = subsetRank s ⟨j,hj⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (subsetRank_injective s hr)
  · have hj : j ∉ s := fun h => hi (hm.mpr h)
    rw [subsetShuffleFun_notMem s i hi,subsetShuffleFun_notMem s j hj] at hv
    have hr : subsetRank sᶜ ⟨i,by simpa using hi⟩ =
        subsetRank sᶜ ⟨j,by simpa using hj⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (subsetRank_injective sᶜ hr)

noncomputable def subsetShuffle {n : ℕ} (s : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (subsetShuffleFun s) (Finite.injective_iff_bijective.mp (subsetShuffleFun_injective s))

theorem subsetShuffle_avoids {n : ℕ} (s : Finset (Fin n)) :
    Avoids312 (permutationMatrix (subsetShuffle s)) := by
  classical
  apply permutationMatrix_avoids_of_split (k := s.card)
  · intro i j hij hi hj
    change (subsetShuffleFun s i).val < s.card at hi
    change (subsetShuffleFun s j).val < s.card at hj
    have hmi := (subsetShuffleFun_lt_iff s i).mp hi
    have hmj := (subsetShuffleFun_lt_iff s j).mp hj
    have hr := subsetRank_strictMono s (show (⟨i,hmi⟩ : s) < ⟨j,hmj⟩ from hij)
    change (subsetShuffleFun s j).val < (subsetShuffleFun s i).val
    rw [subsetShuffleFun_mem s i hmi,subsetShuffleFun_mem s j hmj]
    have hri := (subsetRank s ⟨i,hmi⟩).isLt
    have hrj := (subsetRank s ⟨j,hmj⟩).isLt
    change (subsetRank s ⟨i,hmi⟩).val < (subsetRank s ⟨j,hmj⟩).val at hr
    omega
  · intro i j hij hi hj
    change s.card ≤ (subsetShuffleFun s i).val at hi
    change s.card ≤ (subsetShuffleFun s j).val at hj
    have hmi : i ∉ s := fun h => (Nat.not_lt.mpr hi) ((subsetShuffleFun_lt_iff s i).mpr h)
    have hmj : j ∉ s := fun h => (Nat.not_lt.mpr hj) ((subsetShuffleFun_lt_iff s j).mpr h)
    have hr := subsetRank_strictMono sᶜ
      (show (⟨i,by simpa using hmi⟩ : (sᶜ : Finset (Fin n))) < ⟨j,by simpa using hmj⟩ from hij)
    change (subsetShuffleFun s i).val < (subsetShuffleFun s j).val
    rw [subsetShuffleFun_notMem s i hmi,subsetShuffleFun_notMem s j hmj]
    exact Nat.add_lt_add_left hr _

end ASR312
