/-
Copyright 2026 Google LLC
Construction adapted from AlphaProof Nexus Results, under the Apache 2.0 license.
See THIRD_PARTY_LICENSES/Apache-2.0.txt.
-/
import MainTheorems.PureOSequences.CoordinateCounts

namespace ResearchMain.PureOSequences

open Classical

noncomputable def stringGenerators (t : ℕ) : Finset (Monomial 3) :=
  (Finset.range (t - 1)).image (fun q => triple (3 * t - q) q 0)

noncomputable def fatStringGenerators (t : ℕ) : Finset (Monomial 3) :=
  insert (triple t t t) (stringGenerators t)

theorem fatString_degree (t : ℕ) :
    ∀ m ∈ fatStringGenerators t, totalDeg m = 3 * t := by
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · simp
    omega
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    have := Finset.mem_range.mp hq
    simp only [degree_triple]
    omega

theorem fatString_nonempty (t : ℕ) : (fatStringGenerators t).Nonempty :=
  ⟨triple t t t, Finset.mem_insert_self _ _⟩

noncomputable def fatStringIdeal (t : ℕ) : PureOrderIdeal 3 :=
  pureGenerated (fatStringGenerators t) (fatString_degree t) (fatString_nonempty t)

theorem string_rank_count (t j : ℕ) (ht : 5 ≤ t) (hj : j ≤ 2) :
    pureOSequence (generatedOrderIdeal (stringGenerators t)) (3 * t - j) = t - 1 := by
  symm
  rw [← Finset.card_range (t - 1)]
  apply Finset.card_bij (fun q _ => triple (3 * t - j - q) q 0)
  · intro q hq
    have hqt := Finset.mem_range.mp hq
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply mem_generatedOrderIdeal_iff.mpr
      refine ⟨triple (3 * t - q) q 0, Finset.mem_image.mpr ⟨q, hq, rfl⟩, ?_⟩
      rw [triple_le]
      simp only [triple_zero, triple_one, triple_two]
      omega
    · simp only [degree_triple]
      omega
  · intro q _ p _ heq
    simpa only [triple_one] using congrArg (fun m => m 1) heq
  · intro m hm
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hm
    obtain ⟨g, hg, hmg⟩ := mem_generatedOrderIdeal_iff.mp hmem
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
    have hqt := Finset.mem_range.mp hq
    rw [triple_le] at hmg
    have hz : m 2 = 0 := by omega
    have hs : m 0 + m 1 + m 2 = 3 * t - j := by
      simpa only [totalDeg_eq_sum_univ, Fin.sum_univ_three] using hdeg
    refine ⟨m 1, Finset.mem_range.mpr (by omega), ?_⟩
    have hx : 3 * t - j - m 1 = m 0 := by omega
    rw [hx, ← hz]
    exact triple_ext m

theorem fat_string_disjoint (t j : ℕ) (ht : 5 ≤ t) (hj : j ≤ 2) :
    Disjoint
      ((divisorsFinset (triple t t t)).filter fun m => totalDeg m = 3 * t - j)
      ((generatedOrderIdeal (stringGenerators t)).carrier.filter
        fun m => totalDeg m = 3 * t - j) := by
  apply Finset.disjoint_left.mpr
  intro m hf hs
  obtain ⟨hfat, hdeg⟩ := Finset.mem_filter.mp hf
  have hbox := mem_divisorsFinset_iff.mp hfat
  rw [triple_le] at hbox
  obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hs
  obtain ⟨g, hg, hmg⟩ := mem_generatedOrderIdeal_iff.mp hmem
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
  rw [triple_le] at hmg
  have hsum : m 0 + m 1 + m 2 = 3 * t - j := by
    simpa only [totalDeg_eq_sum_univ, Fin.sum_univ_three] using hdeg
  omega

theorem fatString_rank (t j : ℕ) (ht : 5 ≤ t) (hj : j ≤ 2) :
    pureOSequence (fatStringIdeal t).ideal (3 * t - j) =
      boxCount (triple t t t) j + (t - 1) := by
  have hcarrier : (fatStringIdeal t).ideal.carrier =
      divisorsFinset (triple t t t) ∪ (generatedOrderIdeal (stringGenerators t)).carrier := by
    simp only [fatStringIdeal, pureGenerated, generatedOrderIdeal, fatStringGenerators,
      Finset.biUnion_insert]
  rw [pureOSequence, hcarrier, Finset.filter_union,
    Finset.card_union_of_disjoint (fat_string_disjoint t j ht hj)]
  change boxCount (triple t t t) (3 * t - j) +
    pureOSequence (generatedOrderIdeal (stringGenerators t)) (3 * t - j) = _
  rw [string_rank_count t j ht hj,
    boxCount_symmetry (triple t t t) (3 * t - j) (by simp; omega)]
  congr 2
  simp
  omega

theorem fatString_type (t : ℕ) (ht : 5 ≤ t) : typePO (fatStringIdeal t) = t := by
  rw [fatStringIdeal, type_pureGenerated]
  have hnot : triple t t t ∉ stringGenerators t := by
    intro hm
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hm
    have hz := congrArg (fun m => m 2) heq
    simp only [triple_two] at hz
    omega
  have hinj : Function.Injective (fun q => triple (3 * t - q) q 0) := by
    intro q p heq
    simpa only [triple_one] using congrArg (fun m => m 1) heq
  rw [fatStringGenerators, Finset.card_insert_of_notMem hnot, stringGenerators,
    Finset.card_image_of_injective _ hinj, Finset.card_range]
  omega

theorem fatString_usesEveryVariable (t : ℕ) (ht : 5 ≤ t) :
    UsesEveryVariable (fatStringIdeal t) := by
  intro i
  refine ⟨triple t t t, mem_generatedOrderIdeal_iff.mpr
    ⟨triple t t t, Finset.mem_insert_self _ _, le_rfl⟩, ?_⟩
  fin_cases i <;> simp <;> omega

theorem fatString_not_logConcave (t : ℕ) (ht : 5 ≤ t) :
    ¬ IsLogConcaveUpTo (socleDegree (fatStringIdeal t))
      (pureOSequence (fatStringIdeal t).ideal) := by
  have hs : socleDegree (fatStringIdeal t) = 3 * t := socle_pureGenerated _ _ _
  have hfat (j : ℕ) (hj : j ≤ 2) :
      boxCount (triple t t t) j * 2 = (j + 1) * (j + 2) :=
    boxCount_three_saturated _ _ (by simp; omega) (by simp; omega) (by simp; omega)
  have h0 := fatString_rank t 0 ht (by omega)
  have h1 := fatString_rank t 1 ht (by omega)
  have h2 := fatString_rank t 2 ht (by omega)
  have hf0 := hfat 0 (by omega)
  have hf1 := hfat 1 (by omega)
  have hf2 := hfat 2 (by omega)
  have hr0 : pureOSequence (fatStringIdeal t).ideal (3 * t) = t := by
    simp only [Nat.sub_zero] at h0
    omega
  have hr1 : pureOSequence (fatStringIdeal t).ideal (3 * t - 1) = t + 2 := by omega
  have hr2 : pureOSequence (fatStringIdeal t).ideal (3 * t - 2) = t + 5 := by omega
  intro h
  have hbad := h (3 * t - 1) (by rw [hs, Finset.mem_Ioo]; omega)
  rw [show 3 * t - 1 - 1 = 3 * t - 2 by omega,
    show 3 * t - 1 + 1 = 3 * t by omega, hr1, hr2, hr0] at hbad
  nlinarith

theorem exists_large_type_counterexample (t : ℕ) (ht : 5 ≤ t) :
    ∃ P : PureOrderIdeal 3, typePO P = t ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) :=
  ⟨fatStringIdeal t, fatString_type t ht, fatString_usesEveryVariable t ht,
    fatString_not_logConcave t ht⟩

end ResearchMain.PureOSequences
