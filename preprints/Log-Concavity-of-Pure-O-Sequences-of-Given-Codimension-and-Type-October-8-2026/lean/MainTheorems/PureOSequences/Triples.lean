import MainTheorems.PureOSequences.Basic
import Mathlib.Data.Fin.Tuple.Basic

namespace ResearchMain.PureOSequences

noncomputable def triple (a b c : ℕ) : Monomial 3 :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] theorem triple_zero (a b c : ℕ) : triple a b c 0 = a := by simp [triple]
@[simp] theorem triple_one (a b c : ℕ) : triple a b c 1 = b := by simp [triple]
@[simp] theorem triple_two (a b c : ℕ) : triple a b c 2 = c := by simp [triple]

@[simp] theorem degree_triple (a b c : ℕ) : totalDeg (triple a b c) = a + b + c := by
  simp [totalDeg_eq_sum_univ, Fin.sum_univ_three]

theorem triple_ext (m : Monomial 3) : triple (m 0) (m 1) (m 2) = m := by
  ext i
  fin_cases i <;> simp

theorem triple_le {a b c : ℕ} {m : Monomial 3} :
    m ≤ triple a b c ↔ m 0 ≤ a ∧ m 1 ≤ b ∧ m 2 ≤ c := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> simp_all

@[simp] theorem triple_eq_iff {a b c x y z : ℕ} :
    triple a b c = triple x y z ↔ a = x ∧ b = y ∧ c = z := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun m => m 0) h,
      by simpa using congrArg (fun m => m 1) h,
      by simpa using congrArg (fun m => m 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def rankPairs (bound d : ℕ) (test : ℕ → ℕ → ℕ → Bool) : Finset (ℕ × ℕ) :=
  (Finset.range bound ×ˢ Finset.range bound).filter fun p =>
    p.1 + p.2 ≤ d ∧ test p.1 p.2 (d - p.1 - p.2) = true

theorem rank_count_from_pairs (I : OrderIdeal 3) (bound d : ℕ)
    (test : ℕ → ℕ → ℕ → Bool)
    (hmem : ∀ x y z, triple x y z ∈ I.carrier ↔ test x y z = true)
    (hbound : ∀ m ∈ I.carrier, m 0 < bound ∧ m 1 < bound) :
    pureOSequence I d = (rankPairs bound d test).card := by
  classical
  symm
  apply Finset.card_bij (fun p _ => triple p.1 p.2 (d - p.1 - p.2))
  · intro p hp
    obtain ⟨_, hd, hg⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨(hmem _ _ _).mpr hg, ?_⟩
    simp only [degree_triple]
    omega
  · intro p _ q _ heq
    exact Prod.ext
      (by simpa only [triple_zero] using congrArg (fun m => m 0) heq)
      (by simpa only [triple_one] using congrArg (fun m => m 1) heq)
  · intro m hm
    obtain ⟨hi, hdeg⟩ := Finset.mem_filter.mp hm
    have hsum : m 0 + m 1 + m 2 = d := by
      simpa only [totalDeg_eq_sum_univ, Fin.sum_univ_three] using hdeg
    have hz : d - m 0 - m 1 = m 2 := by omega
    refine ⟨(m 0, m 1), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (hbound m hi).1, Finset.mem_range.mpr (hbound m hi).2⟩
    · refine ⟨by omega, ?_⟩
      rw [hz]
      exact (hmem _ _ _).mp ((triple_ext m).symm ▸ hi)
    · rw [hz]
      exact triple_ext m

end ResearchMain.PureOSequences
