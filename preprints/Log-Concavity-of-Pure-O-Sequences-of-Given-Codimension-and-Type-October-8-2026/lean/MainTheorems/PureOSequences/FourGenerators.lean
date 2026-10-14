import MainTheorems.PureOSequences.Triples

namespace ResearchMain.PureOSequences

noncomputable def fourGenerators : Finset (Monomial 3) :=
  {triple 4 4 16, triple 1 22 1, triple 1 1 22, triple 22 1 1}

theorem fourGenerators_degree : ∀ m ∈ fourGenerators, totalDeg m = 24 := by
  intro m hm
  simp only [fourGenerators, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

theorem fourGenerators_nonempty : fourGenerators.Nonempty :=
  ⟨triple 4 4 16, Finset.mem_insert_self _ _⟩

noncomputable def fourGeneratorIdeal : PureOrderIdeal 3 :=
  pureGenerated fourGenerators fourGenerators_degree fourGenerators_nonempty

def fourGeneratorTest (x y z : ℕ) : Bool :=
  decide ((x ≤ 4 ∧ y ≤ 4 ∧ z ≤ 16) ∨
    (x ≤ 1 ∧ y ≤ 22 ∧ z ≤ 1) ∨
    (x ≤ 1 ∧ y ≤ 1 ∧ z ≤ 22) ∨
    (x ≤ 22 ∧ y ≤ 1 ∧ z ≤ 1))

theorem fourGenerator_membership (m : Monomial 3) :
    m ∈ fourGeneratorIdeal.ideal.carrier ↔ fourGeneratorTest (m 0) (m 1) (m 2) = true := by
  simp [fourGeneratorIdeal, pureGenerated, fourGenerators, triple_le, fourGeneratorTest]

theorem fourGenerator_rank_count (d : ℕ) :
    pureOSequence fourGeneratorIdeal.ideal d = (rankPairs 23 d fourGeneratorTest).card := by
  apply rank_count_from_pairs
  · intro x y z
    simpa only [triple_zero, triple_one, triple_two] using
      fourGenerator_membership (triple x y z)
  · intro m hm
    have h := (fourGenerator_membership m).mp hm
    simp only [fourGeneratorTest, decide_eq_true_eq] at h
    omega

theorem fourGenerator_counts :
    ((rankPairs 23 20 fourGeneratorTest).card, (rankPairs 23 21 fourGeneratorTest).card,
      (rankPairs 23 22 fourGeneratorTest).card) = (27, 22, 18) := by
  decide +kernel

theorem fourGenerator_type : typePO fourGeneratorIdeal = 4 := by
  rw [fourGeneratorIdeal, type_pureGenerated]
  norm_num [fourGenerators, triple_eq_iff]

theorem fourGenerator_usesEveryVariable : UsesEveryVariable fourGeneratorIdeal := by
  intro i
  refine ⟨triple 4 4 16, ?_, ?_⟩
  · rw [fourGenerator_membership]
    norm_num [fourGeneratorTest]
  · fin_cases i <;> norm_num

theorem fourGenerator_not_logConcave :
    ¬ IsLogConcaveUpTo (socleDegree fourGeneratorIdeal)
      (pureOSequence fourGeneratorIdeal.ideal) := by
  have hs : socleDegree fourGeneratorIdeal = 24 := socle_pureGenerated _ _ _
  have hcounts := fourGenerator_counts
  have h20 : pureOSequence fourGeneratorIdeal.ideal 20 = 27 := by
    rw [fourGenerator_rank_count]
    exact congrArg Prod.fst hcounts
  have h21 : pureOSequence fourGeneratorIdeal.ideal 21 = 22 := by
    rw [fourGenerator_rank_count]
    exact congrArg (fun p => p.2.1) hcounts
  have h22 : pureOSequence fourGeneratorIdeal.ideal 22 = 18 := by
    rw [fourGenerator_rank_count]
    exact congrArg (fun p => p.2.2) hcounts
  intro h
  have hbad := h 21 (by rw [hs]; decide)
  norm_num [h20, h21, h22] at hbad

theorem exists_type_four_counterexample :
    ∃ P : PureOrderIdeal 3, typePO P = 4 ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) :=
  ⟨fourGeneratorIdeal, fourGenerator_type, fourGenerator_usesEveryVariable,
    fourGenerator_not_logConcave⟩

end ResearchMain.PureOSequences
