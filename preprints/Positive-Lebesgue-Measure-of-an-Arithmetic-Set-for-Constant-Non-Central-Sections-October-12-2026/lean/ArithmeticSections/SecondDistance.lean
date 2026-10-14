import ArithmeticSections.FirstDistance

namespace ArithmeticSections

def distinctPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range k) ×ˢ (Finset.range k)).filter (fun p => p.1 ≠ p.2)

theorem distinctPairs_nonempty {k : ℕ} (hk : 2 ≤ k) : (distinctPairs k).Nonempty := by
  refine ⟨(0, 1), ?_⟩
  simp only [distinctPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The second order statistic is the minimum of maxima over distinct pairs. -/
noncomputable def secondDistance (γ : ℝ) (k : ℕ) : ℝ :=
  if hk : 2 ≤ k then
    (distinctPairs k).inf' (distinctPairs_nonempty hk)
      (fun p => max (oddDistance γ (p.1 + 1)) (oddDistance γ (p.2 + 1)))
  else 0

theorem secondDistance_le_pair {γ : ℝ} {k i j : ℕ}
    (hi : i < k) (hj : j < k) (hij : i ≠ j) :
    secondDistance γ k ≤ max (oddDistance γ (i + 1)) (oddDistance γ (j + 1)) := by
  have hk : 2 ≤ k := by omega
  unfold secondDistance
  rw [dite_eq_left hk]
  apply Finset.inf'_le (b := (i, j)) _
  simp only [distinctPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨hi, hj⟩, hij⟩

theorem secondDistance_at_most_one_below {γ : ℝ} {k i j : ℕ}
    (hi : i < k) (hj : j < k)
    (h1 : oddDistance γ (i + 1) < secondDistance γ k)
    (h2 : oddDistance γ (j + 1) < secondDistance γ k) : i = j := by
  by_contra hij
  have h := secondDistance_le_pair hi hj hij (γ := γ)
  exact (not_lt_of_ge h) (max_lt h1 h2)

theorem firstDistance_lt_second {γ : ℝ} (hγ : Irrational γ) {k : ℕ} (hk : 2 ≤ k) :
    firstDistance γ k < secondDistance γ k := by
  unfold secondDistance
  rw [dite_eq_left hk, Finset.lt_inf'_iff]
  intro p hp
  simp only [distinctPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  have h1 := firstDistance_le (γ := γ) (by omega : 1 ≤ p.1 + 1) (by omega : p.1 + 1 ≤ k)
  have h2 := firstDistance_le (γ := γ) (by omega : 1 ≤ p.2 + 1) (by omega : p.2 + 1 ≤ k)
  have hn := oddDistance_ne hγ (by omega : 1 ≤ p.1 + 1)
    (by omega : 1 ≤ p.2 + 1) (by omega : p.1 + 1 ≠ p.2 + 1)
  rcases lt_or_gt_of_ne hn with h | h
  · exact lt_of_le_of_lt h1 (lt_of_lt_of_le h (le_max_right _ _))
  · exact lt_of_le_of_lt h2 (lt_of_lt_of_le h (le_max_left _ _))

theorem secondDistance_lt_half_pi {γ : ℝ} (hγ : Irrational γ) {k : ℕ} (hk : 2 ≤ k) :
    secondDistance γ k < Real.pi / 2 := by
  have h := secondDistance_le_pair (γ := γ) (by omega : 0 < k)
    (by omega : 1 < k) (by omega : (0 : ℕ) ≠ 1)
  exact lt_of_le_of_lt h (max_lt (oddDistance_bounds hγ (by omega)).2
    (oddDistance_bounds hγ (by omega)).2)

theorem continuous_secondDistance (k : ℕ) : Continuous (fun γ => secondDistance γ k) := by
  by_cases hk : 2 ≤ k
  · simp only [secondDistance, dite_eq_left hk]
    exact Continuous.finset_inf'_apply _ (fun _ _ =>
      (continuous_oddDistance _).max (continuous_oddDistance _))
  · simpa only [secondDistance, dite_eq_right hk] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

theorem secondDistance_attained {γ : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    ∃ i, i < k ∧ secondDistance γ k = oddDistance γ (i + 1) := by
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' (distinctPairs_nonempty hk)
    (fun p => max (oddDistance γ (p.1 + 1)) (oddDistance γ (p.2 + 1)))
  simp only [distinctPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  have he' : secondDistance γ k =
      max (oddDistance γ (p.1 + 1)) (oddDistance γ (p.2 + 1)) := by
    simpa only [secondDistance, dite_eq_left hk] using he
  rcases le_total (oddDistance γ (p.1 + 1)) (oddDistance γ (p.2 + 1)) with h | h
  · exact ⟨p.2, hp.1.2, he'.trans (max_eq_right h)⟩
  · exact ⟨p.1, hp.1.1, he'.trans (max_eq_left h)⟩

end ArithmeticSections
