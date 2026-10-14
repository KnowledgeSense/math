import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace ResearchMain.Domination

open Classical

variable {V : Type*} [Fintype V]

def Dominates (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, ∃ u ∈ S, u = v ∨ G.Adj u v

noncomputable def dominatingSets (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) :=
  (Finset.univ.powersetCard k).filter (Dominates G)

noncomputable def dominationCount (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (dominatingSets G k).card

noncomputable def normalizedCount (G : SimpleGraph V) (k : ℕ) : ℚ :=
  dominationCount G k / Nat.choose (Fintype.card V) k

def UltraLogConcave (G : SimpleGraph V) : Prop :=
  ∀ k ∈ Finset.Ioo 0 (Fintype.card V),
    normalizedCount G (k - 1) * normalizedCount G (k + 1) ≤ normalizedCount G k ^ 2

omit [Fintype V] in
theorem dominates_mono {G : SimpleGraph V} {S T : Finset V}
    (hS : Dominates G S) (hst : S ⊆ T) : Dominates G T := by
  intro v
  obtain ⟨u, hu, hdom⟩ := hS v
  exact ⟨u, hst hu, hdom⟩

theorem dominates_univ (G : SimpleGraph V) : Dominates G Finset.univ := by
  intro v
  exact ⟨v, Finset.mem_univ v, Or.inl rfl⟩

theorem mem_dominatingSets (G : SimpleGraph V) (k : ℕ) (S : Finset V) :
    S ∈ dominatingSets G k ↔ S.card = k ∧ Dominates G S := by
  simp [dominatingSets, Finset.mem_powersetCard]

omit [Fintype V] in
theorem dominates_empty_iff (G : SimpleGraph V) :
    Dominates G ∅ ↔ IsEmpty V := by
  constructor
  · intro h
    exact ⟨fun v => by obtain ⟨_, hu, _⟩ := h v; exact Finset.notMem_empty _ hu⟩
  · intro h
    exact fun v => (h.false v).elim

theorem dominationCount_zero_of_nonempty (G : SimpleGraph V) [Nonempty V] :
    dominationCount G 0 = 0 := by
  have hempty : dominatingSets G 0 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro S hS
    obtain ⟨hcard, hdom⟩ := (mem_dominatingSets G 0 S).mp hS
    have he : S = ∅ := Finset.card_eq_zero.mp hcard
    rw [he] at hdom
    have hi := (dominates_empty_iff G).mp hdom
    exact hi.false (Classical.choice inferInstance)
  simp only [dominationCount, hempty, Finset.card_empty]

theorem dominationCount_full (G : SimpleGraph V) :
    dominationCount G (Fintype.card V) = 1 := by
  have hset : dominatingSets G (Fintype.card V) = {Finset.univ} := by
    ext S
    rw [mem_dominatingSets, Finset.mem_singleton]
    constructor
    · intro hS
      exact Finset.eq_univ_of_card S hS.1
    · rintro rfl
      exact ⟨Finset.card_univ, dominates_univ G⟩
  simp only [dominationCount, hset, Finset.card_singleton]

theorem dominationCount_above (G : SimpleGraph V) (k : ℕ)
    (hk : Fintype.card V < k) : dominationCount G k = 0 := by
  have hempty : dominatingSets G k = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro S hS
    have hcard := (mem_dominatingSets G k S).mp hS |>.1
    have hbound := Finset.card_le_card (Finset.subset_univ S)
    rw [hcard, Finset.card_univ] at hbound
    omega
  simp only [dominationCount, hempty, Finset.card_empty]

theorem dominationCount_le_choose (G : SimpleGraph V) (k : ℕ) :
    dominationCount G k ≤ Nat.choose (Fintype.card V) k := by
  have h := Finset.card_le_card (Finset.filter_subset (Dominates G) (Finset.univ.powersetCard k))
  simpa only [dominationCount, dominatingSets, Finset.card_powersetCard,
    Finset.card_univ] using h

theorem normalizedCount_nonneg (G : SimpleGraph V) (k : ℕ) :
    0 ≤ normalizedCount G k := by
  unfold normalizedCount
  positivity

theorem normalizedCount_le_one (G : SimpleGraph V) (k : ℕ) :
    normalizedCount G k ≤ 1 := by
  unfold normalizedCount
  by_cases h : Nat.choose (Fintype.card V) k = 0
  · simp [h]
  · have hp : (0 : ℚ) < Nat.choose (Fintype.card V) k := by exact_mod_cast Nat.pos_of_ne_zero h
    apply (div_le_one hp).mpr
    exact_mod_cast dominationCount_le_choose G k

end ResearchMain.Domination
