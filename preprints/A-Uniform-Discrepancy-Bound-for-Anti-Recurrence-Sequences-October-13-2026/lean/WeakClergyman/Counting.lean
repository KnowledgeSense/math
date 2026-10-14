import WeakClergyman.Definitions

namespace WeakClergyman.AntiRecurrence

variable {k : ℕ} {a : Fin k → ℕ} (S : AntiRecurrence k a)

 theorem disjoint_values (i j : ℕ) : S.A i ≠ S.B j := by
  intro h
  have hc := (S.complementary (S.A i) (S.A_pos i)).mp ⟨i, rfl⟩
  exact hc ⟨j, h.symm⟩

 theorem complementary_rank_A (j : ℕ) :
    S.A j = j + (valuesBelow S.B (S.A j)).card + 1 := by
  classical
  let b := S.A j
  have hd : Disjoint (valuesBelow S.B b) (valuesBelow S.A b) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨_, i, rfl⟩ := (mem_valuesBelow _ _ _).mp hx
    obtain ⟨_, t, ht⟩ := (mem_valuesBelow _ _ _).mp hy
    exact S.disjoint_values t i ht
  have hu : valuesBelow S.B b ∪ valuesBelow S.A b = (Finset.range b).erase 0 := by
    ext x
    simp only [Finset.mem_union, mem_valuesBelow, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro (⟨hx, i, rfl⟩ | ⟨hx, i, rfl⟩)
      · exact ⟨Nat.ne_of_gt (S.B_pos i), hx⟩
      · exact ⟨Nat.ne_of_gt (S.A_pos i), hx⟩
    · rintro ⟨hx, hb⟩
      by_cases ha : ∃ i, S.A i = x
      · exact Or.inr ⟨hb, ha⟩
      · left
        refine ⟨hb, ?_⟩
        by_contra hn
        exact ha ((S.complementary x (Nat.pos_of_ne_zero hx)).mpr hn)
  have hc := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd, card_valuesBelow_at S.A_strictMono] at hc
  have hz : 0 ∈ Finset.range b := Finset.mem_range.mpr (S.A_pos j)
  rw [Finset.card_erase_of_mem hz, Finset.card_range] at hc
  dsimp [b] at hc
  have := S.A_pos j
  omega

 theorem complementary_rank (j : ℕ) :
    S.B j = j + (valuesBelow S.A (S.B j)).card + 1 := by
  classical
  let b := S.B j
  have hd : Disjoint (valuesBelow S.A b) (valuesBelow S.B b) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨_, i, rfl⟩ := (mem_valuesBelow _ _ _).mp hx
    obtain ⟨_, t, ht⟩ := (mem_valuesBelow _ _ _).mp hy
    exact S.disjoint_values i t ht.symm
  have hu : valuesBelow S.A b ∪ valuesBelow S.B b = (Finset.range b).erase 0 := by
    ext x
    simp only [Finset.mem_union, mem_valuesBelow, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro (⟨hx, i, rfl⟩ | ⟨hx, i, rfl⟩)
      · exact ⟨Nat.ne_of_gt (S.A_pos i), hx⟩
      · exact ⟨Nat.ne_of_gt (S.B_pos i), hx⟩
    · rintro ⟨hx, hb⟩
      by_cases ha : ∃ i, S.A i = x
      · exact Or.inl ⟨hb, ha⟩
      · right
        refine ⟨hb, ?_⟩
        by_contra hn
        exact ha ((S.complementary x (Nat.pos_of_ne_zero hx)).mpr hn)
  have hc := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd, card_valuesBelow_at S.B_strictMono] at hc
  have hz : 0 ∈ Finset.range b := Finset.mem_range.mpr (S.B_pos j)
  rw [Finset.card_erase_of_mem hz, Finset.card_range] at hc
  dsimp [b] at hc
  have := S.B_pos j
  omega

 theorem initial_index_lower_A (n : ℕ) : n + 1 ≤ S.A n := by
  have hh := S.A_strictMono.add_le_nat n 0
  simp only [Nat.add_zero] at hh
  have hp := S.A_pos 0
  omega

 theorem initial_index_lower_B (n : ℕ) : n + 1 ≤ S.B n := by
  have hh := S.B_strictMono.add_le_nat n 0
  simp only [Nat.add_zero] at hh
  have hp := S.B_pos 0
  omega

end WeakClergyman.AntiRecurrence
