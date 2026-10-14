import MainTheorems.PureOSequences.PaddedTriples
import MainTheorems.PureOSequences.CoordinateCounts
import MainTheorems.PureOSequences.TubeCounts

namespace ResearchMain.PureOSequences

theorem flat_rank_count (k t j : ℕ) (hhi : j ≤ k + 14) :
    boxCount (higherFlat k t) (higherDegree k t - j) * 2 = (j + 1) * (j + 2) := by
  have hj : j ≤ higherDegree k t := by unfold higherDegree; omega
  rw [boxCount_symmetry (higherFlat k t) (higherDegree k t - j)
    (by rw [higherFlat_degree]; exact Nat.sub_le _ _), higherFlat_degree,
    Nat.sub_sub_self hj]
  have hflat : higherFlat k t =
      paddedTriple k (triple (k + 14) (k + 14) (higherDegree k t - 2 * k - 28)) := by
    simp only [higherFlat, paddedTriple, triple_zero, triple_one, triple_two]
  rw [hflat, boxCount_paddedTriple]
  exact boxCount_three_saturated _ _ (by simpa using hhi) (by simpa using hhi)
    (by simp only [triple_two]; unfold higherDegree; omega)

theorem higher_rank_disjoint (k t j : ℕ) (hhi : j ≤ k + 14) :
    Disjoint
      ((divisorsFinset (higherFlat k t)).filter
        fun m => totalDeg m = higherDegree k t - j)
      ((generatedOrderIdeal (higherTubeGenerators k t)).carrier.filter
        fun m => totalDeg m = higherDegree k t - j) := by
  apply Finset.disjoint_left.mpr
  intro m hf htube
  obtain ⟨hfat, hdeg⟩ := Finset.mem_filter.mp hf
  have hbox := mem_divisorsFinset_iff.mp hfat
  rw [higherFlat, blockMonomial_le] at hbox
  obtain ⟨hmem, _⟩ := Finset.mem_filter.mp htube
  obtain ⟨g, hg, hmg⟩ := mem_generatedOrderIdeal_iff.mp hmem
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hg
  rw [higherTube, blockMonomial_le] at hmg
  have hsum : (∑ i, m (Fin.natAdd 4 i)) = 0 := Finset.sum_eq_zero (fun i _ =>
    le_antisymm (hbox.2.2.2.2 i) (Nat.zero_le _))
  have hcoords := degree_block_coordinates m
  rw [hdeg, hsum] at hcoords
  unfold higherDegree at hcoords
  omega

theorem higher_rank_double (k t j : ℕ) (ht : 2 ≤ t)
    (hlo : k + 12 ≤ j) (hhi : j ≤ k + 14) :
    pureOSequence (higherIdeal k t).ideal (higherDegree k t - j) * 2 =
      (j + 1) * (j + 2) + 50 * (t + 3) * 2 ^ k := by
  have hcarrier : (higherIdeal k t).ideal.carrier =
      divisorsFinset (higherFlat k t) ∪
        (generatedOrderIdeal (higherTubeGenerators k t)).carrier := by
    simp only [higherIdeal, pureGenerated, generatedOrderIdeal, higherGenerators,
      Finset.biUnion_insert]
  rw [pureOSequence, hcarrier, Finset.filter_union,
    Finset.card_union_of_disjoint (higher_rank_disjoint k t j hhi)]
  change (boxCount (higherFlat k t) (higherDegree k t - j) +
    pureOSequence (generatedOrderIdeal (higherTubeGenerators k t))
      (higherDegree k t - j)) * 2 = _
  rw [add_mul, flat_rank_count k t j hhi, tube_rank_count k t j ht hlo hhi]
  ring

theorem higherIdeal_not_logConcave (k t : ℕ) (ht : 2 ≤ t) :
    ¬ IsLogConcaveUpTo (socleDegree (higherIdeal k t))
      (pureOSequence (higherIdeal k t).ideal) := by
  have hs : socleDegree (higherIdeal k t) = higherDegree k t := socle_pureGenerated _ _ _
  have hlow := higher_rank_double k t (k + 14) ht (by omega) (by omega)
  have hmid := higher_rank_double k t (k + 13) ht (by omega) (by omega)
  have hhigh := higher_rank_double k t (k + 12) ht (by omega) (by omega)
  intro h
  have hbad := h (higherDegree k t - (k + 13)) (by
    rw [hs, Finset.mem_Ioo]
    unfold higherDegree
    omega)
  rw [show higherDegree k t - (k + 13) - 1 = higherDegree k t - (k + 14) by omega,
    show higherDegree k t - (k + 13) + 1 = higherDegree k t - (k + 12) by
      unfold higherDegree; omega] at hbad
  have hdouble :
      (pureOSequence (higherIdeal k t).ideal (higherDegree k t - (k + 14)) * 2) *
      (pureOSequence (higherIdeal k t).ideal (higherDegree k t - (k + 12)) * 2) ≤
      (pureOSequence (higherIdeal k t).ideal (higherDegree k t - (k + 13)) * 2) ^ 2 := by
    nlinarith
  rw [hlow, hmid, hhigh] at hdouble
  have hnegative := higher_defect_negative k t ht
  nlinarith

theorem exists_higher_counterexample (k t : ℕ) (ht : 2 ≤ t) :
    ∃ P : PureOrderIdeal (4 + k), typePO P = t ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) :=
  ⟨higherIdeal k t, higherIdeal_type k t ht, higherIdeal_usesEveryVariable k t ht,
    higherIdeal_not_logConcave k t ht⟩

theorem exists_counterexample_above_dimension_three (r t : ℕ) (hr : 4 ≤ r) (ht : 2 ≤ t) :
    ∃ P : PureOrderIdeal r, typePO P = t ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
  rw [hk]
  exact exists_higher_counterexample k t ht

end ResearchMain.PureOSequences
