import MainTheorems.PureOSequences.Triples

namespace ResearchMain.PureOSequences

noncomputable def threeGenerators : Finset (Monomial 3) :=
  {triple 10 10 56, triple 15 15 46, triple 27 27 22}

theorem threeGenerators_degree : ∀ m ∈ threeGenerators, totalDeg m = 76 := by
  intro m hm
  simp only [threeGenerators, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl <;> norm_num

theorem threeGenerators_nonempty : threeGenerators.Nonempty := by
  exact ⟨triple 10 10 56, Finset.mem_insert_self _ _⟩

noncomputable def threeGeneratorIdeal : PureOrderIdeal 3 :=
  pureGenerated threeGenerators threeGenerators_degree threeGenerators_nonempty

def threeGeneratorTest (x y z : ℕ) : Bool :=
  decide ((x ≤ 10 ∧ y ≤ 10 ∧ z ≤ 56) ∨
    (x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 46) ∨
    (x ≤ 27 ∧ y ≤ 27 ∧ z ≤ 22))

def threeGeneratorPairs (d : ℕ) : Finset (ℕ × ℕ) :=
  rankPairs 28 d threeGeneratorTest

theorem mem_threeGeneratorIdeal (m : Monomial 3) :
    m ∈ threeGeneratorIdeal.ideal.carrier ↔
      (m 0 ≤ 10 ∧ m 1 ≤ 10 ∧ m 2 ≤ 56) ∨
      (m 0 ≤ 15 ∧ m 1 ≤ 15 ∧ m 2 ≤ 46) ∨
      (m 0 ≤ 27 ∧ m 1 ≤ 27 ∧ m 2 ≤ 22) := by
  simp [threeGeneratorIdeal, pureGenerated, threeGenerators, triple_le]

theorem threeGenerator_rank_count (d : ℕ) :
    pureOSequence threeGeneratorIdeal.ideal d = (threeGeneratorPairs d).card := by
  apply rank_count_from_pairs
  · intro x y z
    simp only [mem_threeGeneratorIdeal, triple_zero, triple_one, triple_two,
      threeGeneratorTest, decide_eq_true_eq]
  · intro m hm
    have h := (mem_threeGeneratorIdeal m).mp hm
    omega

theorem threeGenerator_counts :
    ((threeGeneratorPairs 54).card, (threeGeneratorPairs 55).card,
      (threeGeneratorPairs 56).card) = (532, 509, 487) := by
  decide +kernel

theorem threeGenerator_type : typePO threeGeneratorIdeal = 3 := by
  rw [threeGeneratorIdeal, type_pureGenerated]
  have h1 : triple 10 10 56 ≠ triple 15 15 46 := by
    intro h
    have := congrArg (fun m => m 0) h
    norm_num at this
  have h2 : triple 10 10 56 ≠ triple 27 27 22 := by
    intro h
    have := congrArg (fun m => m 0) h
    norm_num at this
  have h3 : triple 15 15 46 ≠ triple 27 27 22 := by
    intro h
    have := congrArg (fun m => m 0) h
    norm_num at this
  simp [threeGenerators, h1, h2, h3]

theorem threeGenerator_usesEveryVariable : UsesEveryVariable threeGeneratorIdeal := by
  intro i
  refine ⟨triple 10 10 56, ?_, ?_⟩
  · rw [mem_threeGeneratorIdeal]
    simp
  · fin_cases i <;> norm_num

theorem threeGenerator_not_logConcave :
    ¬ IsLogConcaveUpTo (socleDegree threeGeneratorIdeal)
      (pureOSequence threeGeneratorIdeal.ideal) := by
  have hs : socleDegree threeGeneratorIdeal = 76 := socle_pureGenerated _ _ _
  have hcounts := threeGenerator_counts
  have h54 : pureOSequence threeGeneratorIdeal.ideal 54 = 532 := by
    rw [threeGenerator_rank_count]
    exact congrArg Prod.fst hcounts
  have h55 : pureOSequence threeGeneratorIdeal.ideal 55 = 509 := by
    rw [threeGenerator_rank_count]
    exact congrArg (fun p => p.2.1) hcounts
  have h56 : pureOSequence threeGeneratorIdeal.ideal 56 = 487 := by
    rw [threeGenerator_rank_count]
    exact congrArg (fun p => p.2.2) hcounts
  intro h
  have hbad := h 55 (by rw [hs]; decide)
  norm_num [h54, h55, h56] at hbad

theorem exists_type_three_counterexample :
    ∃ P : PureOrderIdeal 3, typePO P = 3 ∧ UsesEveryVariable P ∧
      ¬ IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) :=
  ⟨threeGeneratorIdeal, threeGenerator_type, threeGenerator_usesEveryVariable,
    threeGenerator_not_logConcave⟩

end ResearchMain.PureOSequences
