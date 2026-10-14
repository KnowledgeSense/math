import MainTheorems.Chores.SpecialBuffer
import MainTheorems.Chores.SpecialRepairs

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

theorem reduce_to_unique_ordinary (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) :
    (∃ g : E → A, EFX M r g) ∨ ∃ a b, a ∈ S ∧ b ∈ S ∧
      UniqueBad M S f a b ∧ expensiveCount M f b b + 2 ≤ q := by
  classical
  by_cases hzero : Fintype.card (OrdinaryIndex M S f q) = 0
  · left
    apply all_special_pairs M hr hf hs
    intro i
    by_contra hi
    have hn : Nonempty (OrdinaryIndex M S f q) := ⟨⟨i, hi⟩⟩
    have hp := Fintype.card_pos_iff.mpr hn
    omega
  · by_cases htwo : 2 ≤ Fintype.card (OrdinaryIndex M S f q)
    · exact Or.inl (multiple_ordinary_pairs M hr hf hs htwo)
    · have hone : Fintype.card (OrdinaryIndex M S f q) = 1 := by omega
      obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hone
      by_cases hspecial : Nonempty (SpecialIndex M S f q)
      · obtain ⟨j⟩ := hspecial
        exact Or.inl (special_buffer M hr hf hs i hi j)
      · let I : PairIndex M S f := i.val
        have hI : expensiveCount M f I.low I.low + 1 ≠ q := i.property
        have hbad : UniqueBad M S f I.high I.low := by
          refine ⟨I.bad, ?_⟩
          intro a ha b hb hab
          obtain ⟨j, hja, hjb⟩ := PairIndex.of_bad ha hb hab
          have hj : expensiveCount M f j.low j.low + 1 ≠ q := by
            intro heq
            exact hspecial ⟨⟨j, heq⟩⟩
          have heq : j = I := congrArg Subtype.val (hi ⟨j, hj⟩)
          rw [heq] at hja hjb
          exact ⟨hja.symm, hjb.symm⟩
        exact Or.inr ⟨I.high, I.low, I.members.1, I.members.2, hbad,
          (optimal_ordinary_pair M hf hs I.members.1 I.members.2 I.bad hI).2⟩

end ResearchMain.Chores
