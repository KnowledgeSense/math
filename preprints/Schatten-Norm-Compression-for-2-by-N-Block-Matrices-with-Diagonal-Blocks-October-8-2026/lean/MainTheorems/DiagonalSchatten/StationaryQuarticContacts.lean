import MainTheorems.DiagonalSchatten.QuarticContacts

namespace ResearchMain.DiagonalSchatten

open scoped BigOperators Polynomial

theorem root_multiplicity_sum_le_natDegree (p : ℝ[X]) (s : Finset ℝ) :
    (∑ x ∈ s, p.rootMultiplicity x) ≤ p.natDegree := by
  classical
  calc
    (∑ x ∈ s, p.rootMultiplicity x) = ∑ x ∈ s, p.roots.count x := by simp
    _ ≤ ∑ x ∈ s ∪ p.roots.toFinset, p.roots.count x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => Nat.zero_le _)
    _ = p.roots.card := Multiset.sum_count_eq_card fun x hx =>
      Finset.mem_union_right s (Multiset.mem_toFinset.mpr hx)
    _ ≤ p.natDegree := Polynomial.card_roots' p

theorem stationary_root_multiplicity {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ}
    (hx : p.eval x = 0) (hdx : p.derivative.eval x = 0) :
    2 ≤ p.rootMultiplicity x := by
  have h := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hx, hdx⟩
  omega

theorem stationary_contact_mass {p : ℝ[X]} (hp : p ≠ 0) (s : Finset ℝ)
    (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0 ∧ p.derivative.eval x = 0) :
    2 * s.card ≤ p.natDegree := by
  calc
    2 * s.card = ∑ x ∈ s, 2 := by simp [mul_comm]
    _ ≤ ∑ x ∈ s, p.rootMultiplicity x := by
      apply Finset.sum_le_sum
      intro x hx
      exact stationary_root_multiplicity hp (hs x hx).2.1 (hs x hx).2.2
    _ ≤ p.natDegree := root_multiplicity_sum_le_natDegree p s

theorem stationary_contact_mass_with_zero {p : ℝ[X]} (hp : p ≠ 0)
    (hzero : p.eval 0 = 0) (s : Finset ℝ)
    (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0 ∧ p.derivative.eval x = 0) :
    2 * s.card + 1 ≤ p.natDegree := by
  classical
  have h0 : (0 : ℝ) ∉ s := by intro h; exact (lt_irrefl (0 : ℝ)) (hs 0 h).1
  have hcount0 : 1 ≤ p.rootMultiplicity 0 :=
    Nat.succ_le_iff.mpr ((Polynomial.rootMultiplicity_pos hp).mpr hzero)
  have hcounts : 2 * s.card ≤ ∑ x ∈ s, p.rootMultiplicity x := by
    calc
      2 * s.card = ∑ x ∈ s, 2 := by simp [mul_comm]
      _ ≤ ∑ x ∈ s, p.rootMultiplicity x := by
        apply Finset.sum_le_sum
        intro x hx
        exact stationary_root_multiplicity hp (hs x hx).2.1 (hs x hx).2.2
  calc
    2 * s.card + 1 ≤ (∑ x ∈ s, p.rootMultiplicity x) + p.rootMultiplicity 0 :=
      Nat.add_le_add hcounts hcount0
    _ = ∑ x ∈ insert (0 : ℝ) s, p.rootMultiplicity x := by
      rw [Finset.sum_insert h0]
      omega
    _ ≤ p.natDegree := root_multiplicity_sum_le_natDegree p _

theorem stationary_quartic_classification {p : ℝ[X]} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ 4) (s : Finset ℝ)
    (hs : ∀ x ∈ s, 0 < x ∧ p.eval x = 0 ∧ p.derivative.eval x = 0) :
    s.card + (if p.eval 0 = 0 then 1 else 0) + (if p.natDegree < 4 then 1 else 0) ≤ 2 ∨
      (s.card = 1 ∧ p.eval 0 = 0 ∧ p.natDegree < 4) := by
  classical
  have hmass := stationary_contact_mass hp s hs
  have hc : s.card ≤ 2 := by omega
  by_cases htwo : s.card = 2
  · have hz : p.eval 0 ≠ 0 := by
      intro hz
      have h := stationary_contact_mass_with_zero hp hz s hs
      omega
    have hd : p.natDegree = 4 := by omega
    exact Or.inl (by simp [htwo, hz, hd])
  · by_cases hzero : p.eval 0 = 0
    · by_cases hinfinity : p.natDegree < 4
      · by_cases hone : s.card = 1
        · exact Or.inr ⟨hone, hzero, hinfinity⟩
        · exact Or.inl (by simp only [hzero, hinfinity, ite_true]; omega)
      · exact Or.inl (by simp only [hzero, hinfinity, ite_true, ite_false]; omega)
    · left
      split_ifs <;> omega

end ResearchMain.DiagonalSchatten
