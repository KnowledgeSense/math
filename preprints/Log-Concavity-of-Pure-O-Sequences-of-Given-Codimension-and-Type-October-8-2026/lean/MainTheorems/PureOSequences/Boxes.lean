import MainTheorems.PureOSequences.Sequences

namespace ResearchMain.PureOSequences

open Classical

noncomputable def boxCount (g : Monomial r) (d : ℕ) : ℕ :=
  ((divisorsFinset g).filter fun m => totalDeg m = d).card

noncomputable def boxCountZ (g : Monomial r) (d : ℤ) : ℤ :=
  ∑ m ∈ divisorsFinset g, if (totalDeg m : ℤ) = d then 1 else 0

@[simp] theorem boxCount_degree_zero {r : ℕ} (g : Monomial r) : boxCount g 0 = 1 := by
  have hset : ((divisorsFinset g).filter fun m => totalDeg m = 0) = {0} := by
    ext m
    simp only [Finset.mem_filter, mem_divisorsFinset_iff, Finset.mem_singleton,
      totalDeg_eq_zero_iff]
    exact and_iff_right_of_imp (fun hm => hm ▸ bot_le)
  simp only [boxCount, hset, Finset.card_singleton]

theorem boxCount_symmetry {r : ℕ} (g : Monomial r) (d : ℕ) (hd : d ≤ totalDeg g) :
    boxCount g d = boxCount g (totalDeg g - d) := by
  unfold boxCount
  apply Finset.card_bij (fun m _ => g - m)
  · intro m hm
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hm
    have hmg := mem_divisorsFinset_iff.mp hmem
    refine Finset.mem_filter.mpr ⟨mem_divisorsFinset_iff.mpr tsub_le_self, ?_⟩
    rw [totalDeg_complement hmg, hdeg]
  · intro m hm n hn heq
    have hmg := mem_divisorsFinset_iff.mp (Finset.mem_filter.mp hm).1
    have hng := mem_divisorsFinset_iff.mp (Finset.mem_filter.mp hn).1
    simpa only [tsub_tsub_cancel_of_le hmg, tsub_tsub_cancel_of_le hng] using
      congrArg (fun m => g - m) heq
  · intro n hn
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hn
    have hng := mem_divisorsFinset_iff.mp hmem
    refine ⟨g - n, Finset.mem_filter.mpr ⟨mem_divisorsFinset_iff.mpr tsub_le_self, ?_⟩,
      tsub_tsub_cancel_of_le hng⟩
    rw [totalDeg_complement hng, hdeg, Nat.sub_sub_self hd]

theorem boxCountZ_nat (g : Monomial r) (d : ℕ) :
    boxCountZ g d = boxCount g d := by
  simp only [boxCountZ, boxCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Nat.cast_inj]

theorem boxCountZ_nonneg (g : Monomial r) (d : ℤ) : 0 ≤ boxCountZ g d := by
  apply Finset.sum_nonneg
  intro m _
  split <;> norm_num

theorem boxCountZ_zero (g : Monomial r) (d : ℤ)
    (hd : d < 0 ∨ (totalDeg g : ℤ) < d) : boxCountZ g d = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hmg := totalDeg_le_of_le (mem_divisorsFinset_iff.mp hm)
  have hne : (totalDeg m : ℤ) ≠ d := by omega
  exact ite_eq_right hne

theorem totalDeg_add_single {r : ℕ} (m : Monomial r) (i : Fin r) (c : ℕ) :
    totalDeg (m + Finsupp.single i c) = totalDeg m + c := by
  simp [totalDeg, Finsupp.sum_add_index']

theorem exists_divisor_of_degree {r : ℕ} (g : Monomial r) (d : ℕ)
    (hd : d ≤ totalDeg g) : ∃ m, m ≤ g ∧ totalDeg m = d := by
  induction d with
  | zero => exact ⟨0, bot_le, rfl⟩
  | succ d ih =>
    obtain ⟨m, hmg, hmdeg⟩ := ih (by omega)
    have hex : ∃ i, m i < g i := by
      by_contra h
      push Not at h
      have heq : m = g := Finsupp.ext (fun i => le_antisymm (hmg i) (h i))
      rw [heq] at hmdeg
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨m + Finsupp.single i 1, ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · simpa [hj] using hi
      · simpa [Finsupp.single_eq_of_ne hj] using hmg j
    · rw [totalDeg_add_single, hmdeg]

theorem boxCountZ_pos {r : ℕ} (g : Monomial r) (d : ℤ)
    (hlo : 0 ≤ d) (hhi : d ≤ totalDeg g) : 0 < boxCountZ g d := by
  have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hlo
  obtain ⟨m, hmg, hmdeg⟩ := exists_divisor_of_degree g d.toNat (by omega)
  have hm : m ∈ divisorsFinset g := mem_divisorsFinset_iff.mpr hmg
  have hterm : (if (totalDeg m : ℤ) = d then (1 : ℤ) else 0) = 1 := by
    simp [hmdeg, hdn]
  have hsum := Finset.single_le_sum (f := fun m =>
    if (totalDeg m : ℤ) = d then (1 : ℤ) else 0)
    (fun _ _ => by split <;> norm_num) hm
  rw [hterm] at hsum
  exact lt_of_lt_of_le (by norm_num) hsum

theorem erase_add_single {r : ℕ} (m : Monomial r) (i : Fin r) :
    m.erase i + Finsupp.single i (m i) = m := by
  ext j
  by_cases hj : j = i <;> simp [hj, Finsupp.erase_ne, Finsupp.single_eq_of_ne]

theorem boxCountZ_convolution {r : ℕ} (g : Monomial r) (i : Fin r) (c : ℕ)
    (hi : i ∉ g.support) (d : ℤ) :
    boxCountZ (g + Finsupp.single i c) d = windowSum (boxCountZ g) c d := by
  have hgi : g i = 0 := Finsupp.notMem_support_iff.mp hi
  have hzero : ∀ m ∈ divisorsFinset g, m i = 0 := by
    intro m hm
    have := mem_divisorsFinset_iff.mp hm i
    omega
  unfold boxCountZ windowSum
  dsimp only
  rw [← Finset.sum_product (Finset.range (c + 1)) (divisorsFinset g)
    (fun p : ℕ × Monomial r => if (totalDeg p.2 : ℤ) = d - p.1 then (1 : ℤ) else 0)]
  symm
  refine Finset.sum_bij (fun p _ => p.2 + Finsupp.single i p.1) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hj, hm⟩ := Finset.mem_product.mp hp
    apply mem_divisorsFinset_iff.mpr
    intro a
    by_cases ha : a = i
    · have := Finset.mem_range.mp hj
      simp [ha, hzero p.2 hm, hgi]
      omega
    · simpa [Finsupp.single_eq_of_ne ha] using mem_divisorsFinset_iff.mp hm a
  · intro p hp q hq heq
    obtain ⟨_, hm⟩ := Finset.mem_product.mp hp
    obtain ⟨_, hn⟩ := Finset.mem_product.mp hq
    have hj : p.1 = q.1 := by
      simpa [hzero p.2 hm, hzero q.2 hn] using congrArg (fun m => m i) heq
    have hm_eq : p.2 = q.2 := by
      rw [hj] at heq
      exact add_right_cancel heq
    exact Prod.ext hj hm_eq
  · intro m hm
    have hmg := mem_divisorsFinset_iff.mp hm
    have he : m.erase i ∈ divisorsFinset g := by
      apply mem_divisorsFinset_iff.mpr
      intro a
      by_cases ha : a = i
      · simp [ha]
      · simpa [Finsupp.erase_ne ha, Finsupp.single_eq_of_ne ha] using hmg a
    refine ⟨(m i, m.erase i), Finset.mem_product.mpr ⟨?_, he⟩, erase_add_single m i⟩
    have hmic := hmg i
    simpa [hgi, Finset.mem_range, Nat.lt_succ_iff] using hmic
  · intro p _
    simp only [totalDeg_add_single, Nat.cast_add, eq_sub_iff_add_eq]

theorem zero_box_ratioDecreasing {r : ℕ} : RatioDecreasing (boxCountZ (0 : Monomial r)) := by
  have hzero : divisorsFinset (0 : Monomial r) = {0} := by
    ext m
    simp only [mem_divisorsFinset_iff, Finset.mem_singleton]
    exact ⟨fun hm => le_antisymm hm bot_le, fun hm => hm ▸ le_rfl⟩
  intro a b hab
  simp only [boxCountZ, hzero, Finset.sum_singleton, totalDeg,
    Finsupp.sum_zero_index, Nat.cast_zero]
  split_ifs <;> omega

theorem box_ratioDecreasing {r : ℕ} (g : Monomial r) : RatioDecreasing (boxCountZ g) := by
  induction g using Finsupp.induction with
  | zero => exact zero_box_ratioDecreasing
  | @single_add i c g hi _hc ih =>
    rw [add_comm]
    apply ratioDecreasing_of_logConcave _ (totalDeg (g + Finsupp.single i c))
    · intro d
      rw [boxCountZ_convolution g i c hi d, boxCountZ_convolution g i c hi (d - 1),
        boxCountZ_convolution g i c hi (d + 1)]
      exact window_logConcave ih c d
    · exact boxCountZ_pos _
    · exact boxCountZ_zero _

theorem box_logConcave {r : ℕ} (g : Monomial r) :
    IsLogConcaveUpTo (totalDeg g) (boxCount g) := by
  intro i hi
  have hipos := (Finset.mem_Ioo.mp hi).1
  have h := box_ratioDecreasing g (i : ℤ) (i : ℤ) le_rfl
  have hsub : (i : ℤ) - 1 = (i - 1 : ℕ) := by omega
  rw [hsub, ← Nat.cast_add_one, boxCountZ_nat, boxCountZ_nat, boxCountZ_nat] at h
  have hnat : boxCount g (i + 1) * boxCount g (i - 1) ≤ boxCount g i * boxCount g i := by
    exact_mod_cast h
  simpa only [mul_comm, sq] using hnat

theorem type_one_logConcave {r : ℕ} (P : PureOrderIdeal r) (ht : typePO P = 1) :
    IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp ht
  have hcarrier : P.ideal.carrier = divisorsFinset g := by
    ext m
    constructor
    · intro hm
      obtain ⟨n, hn, hmn⟩ := exists_le_maximal P.ideal m hm
      rw [hg, Finset.mem_singleton] at hn
      exact mem_divisorsFinset_iff.mpr (hn ▸ hmn)
    · intro hm
      have hgm : g ∈ P.ideal.carrier := by
        have hmax : g ∈ maximalMonomials P.ideal := by simp [hg]
        exact (mem_maximalMonomials_iff P.ideal g).mp hmax |>.1
      exact P.ideal.downward_closed hgm (mem_divisorsFinset_iff.mp hm)
  have hsocle : socleDegree P = totalDeg g := by
    unfold socleDegree
    have hm := Classical.choose_spec P.maximal_nonempty
    have heq : Classical.choose P.maximal_nonempty = g := by
      simpa only [hg, Finset.mem_singleton] using hm
    rw [heq]
  have hseq : pureOSequence P.ideal = boxCount g := by
    funext d
    rw [pureOSequence, boxCount, hcarrier]
  rw [hsocle, hseq]
  exact box_logConcave g

end ResearchMain.PureOSequences
