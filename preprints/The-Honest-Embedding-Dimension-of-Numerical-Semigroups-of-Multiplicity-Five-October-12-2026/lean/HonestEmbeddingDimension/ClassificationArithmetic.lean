import HonestEmbeddingDimension.FourFiveArithmetic

namespace HonestEmbeddingDimension

/-- The five basis residues are distinct for every five-generator semigroup. -/
theorem five_generator_basis_residues_injective {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    Function.Injective (fun i : Fin 5 => ![0, a, b, c, d] i % 5) := by
  obtain ⟨_, ha, hb, hc, hd⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have ha0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
  have hb0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hb (by omega)
  have hc0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hc (by omega)
  have hd0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hd (by omega)
  have habr : a % 5 ≠ b % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hb hh
    omega
  have hacr : a % 5 ≠ c % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hc hh
    omega
  have hadr : a % 5 ≠ d % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hd hh
    omega
  have hbcr : b % 5 ≠ c % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hb hc hh
    omega
  have hbdr : b % 5 ≠ d % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hb hd hh
    omega
  have hcdr : c % 5 ≠ d % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hc hd hh
    omega
  intro i j hij
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;> first | rfl | omega

/-- For five minimal generators there are no additional nonzero Apéry elements. -/
theorem five_generator_apery_set {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    S.apery 5 = {0, a, b, c, d} := by
  obtain ⟨_, ha, hb, hc, hd⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have haA := NumericalSemigroup.minimalGenerator_mem_apery hm.1 hm.2.1 ha (by omega)
  have hbA := NumericalSemigroup.minimalGenerator_mem_apery hm.1 hm.2.1 hb (by omega)
  have hcA := NumericalSemigroup.minimalGenerator_mem_apery hm.1 hm.2.1 hc (by omega)
  have hdA := NumericalSemigroup.minimalGenerator_mem_apery hm.1 hm.2.1 hd (by omega)
  apply Set.Subset.antisymm
  · intro n hn
    let f : Fin 5 → Fin 5 := fun i => residueIndexFive (![0, a, b, c, d] i)
    have hf : Function.Injective f := by
      intro i j hij
      exact five_generator_basis_residues_injective hm h (congrArg Fin.val hij)
    obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf (residueIndexFive n)
    have hr : ![0, a, b, c, d] i % 5 = n % 5 := congrArg Fin.val hi
    fin_cases i <;> dsimp at hr
    · have := NumericalSemigroup.apery_eq_of_mod_eq hm.1 hm.2.1 (S.zero_mem_apery hm.1) hn hr
      simp [← this]
    · have := NumericalSemigroup.apery_eq_of_mod_eq hm.1 hm.2.1 haA hn hr
      simp [← this]
    · have := NumericalSemigroup.apery_eq_of_mod_eq hm.1 hm.2.1 hbA hn hr
      simp [← this]
    · have := NumericalSemigroup.apery_eq_of_mod_eq hm.1 hm.2.1 hcA hn hr
      simp [← this]
    · have := NumericalSemigroup.apery_eq_of_mod_eq hm.1 hm.2.1 hdA hn hr
      simp [← this]
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact S.zero_mem_apery hm.1
    · exact haA
    · exact hbA
    · exact hcA
    · exact hdA

/-- The unrestricted five-generator maximum and conductor formulas. -/
theorem five_generator_aperyMax_conductor_general {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    S.aperyMax 5 (by omega) = d ∧ S.conductor = d - 4 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have hmax : S.aperyMax 5 (by omega) = d := by
    apply le_antisymm
    · have hh := S.aperyMax_mem 5 (by omega)
      rw [five_generator_apery_set hm h] at hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      omega
    · apply NumericalSemigroup.le_aperyMax
      rw [five_generator_apery_set hm h]
      simp
  exact ⟨hmax, by rw [NumericalSemigroup.conductor_eq_aperyMax_sub_four hm, hmax]⟩

/-- The two necessary lower bounds force the full residue arrangement in embedding dimension five. -/
theorem five_generator_residues_of_bounds {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d)
    (hcgt : 2 * a < c) (hdgt : a + b < d) :
    b % 5 = (2 * a) % 5 ∧ c % 5 = (3 * a) % 5 ∧ d % 5 = (4 * a) % 5 := by
  obtain ⟨_, ha, hb, hc, hd⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have ha0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
  have hb0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hb (by omega)
  have hc0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hc (by omega)
  have hd0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hd (by omega)
  have habr : a % 5 ≠ b % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hb hh
    omega
  have hadr : a % 5 ≠ d % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hd hh
    omega
  have hbdr : b % 5 ≠ d % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hb hd hh
    omega
  have hcdr : c % 5 ≠ d % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hc hd hh
    omega
  have hb2 : b % 5 = (2 * a) % 5 := by
    have hmem := S.aperyMin_mem_apery 5 hm.1 (2 * a)
    rw [five_generator_apery_set hm h] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hmod := S.aperyMin_mod 5 hm.1 (2 * a)
    have hle : S.aperyMin 5 hm.1 (2 * a) ≤ 2 * a := by
      apply NumericalSemigroup.aperyMin_le _ rfl
      simpa [Nat.mul_comm] using NumericalSemigroup.mul_mem ha.2.1 2
    rcases hmem with heq | heq | heq | heq | heq <;> rw [heq] at hmod hle <;> omega
  have hc3 : c % 5 = (3 * a) % 5 := by
    have hmem := S.aperyMin_mem_apery 5 hm.1 (a + b)
    rw [five_generator_apery_set hm h] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hmod := S.aperyMin_mod 5 hm.1 (a + b)
    have hle : S.aperyMin 5 hm.1 (a + b) ≤ a + b :=
      NumericalSemigroup.aperyMin_le (S.monoid.add_mem ha.2.1 hb.2.1) rfl
    rcases hmem with heq | heq | heq | heq | heq <;> rw [heq] at hmod hle <;> omega
  refine ⟨hb2, hc3, ?_⟩
  have hacases : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  rcases hacases with hh | hh | hh | hh <;> norm_num [Nat.mul_mod, hh] at hb2 hc3 ⊢ <;> omega

/-- The first four basis residues are distinct in the five-generator case. -/
theorem five_generator_first_four_residues_injective {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    Function.Injective (fun i : Fin 4 => ![0, a, b, c] i % 5) := by
  have hvec (i : Fin 4) : ![0, a, b, c, d] i.castSucc = ![0, a, b, c] i := by
    fin_cases i <;> rfl
  intro i j hij
  have hh : ![0, a, b, c, d] i.castSucc % 5 = ![0, a, b, c, d] j.castSucc % 5 := by
    rwa [hvec, hvec]
  have hh := five_generator_basis_residues_injective hm h hh
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) hh)

/-- The actual least-outside data required by the formal normal-form theorem. -/
theorem HasFourGenerators.normalization_data {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c) (hm : HasMultiplicity S 5) :
    ¬5 ∣ a ∧ (∀ n ∈ S.monoid, ¬5 ∣ n → a ≤ n) ∧
      b ∉ generatedPair 5 a ∧ (∀ n ∈ S.monoid, n ∉ generatedPair 5 a → b ≤ n) ∧
      c ∉ generatedTriple a b ∧ (∀ n ∈ S.monoid, n ∉ generatedTriple a b → c ≤ n) := by
  obtain ⟨h5, ha, hb, hc⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    exact NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
      (Nat.mod_eq_zero_of_dvd hh)
  · intro n hn hnnot
    apply NumericalSemigroup.least_outside_of_minimalGenerators_below
      (T := AddSubmonoid.multiples 5) _ hn (by simpa using hnnot)
    intro g hg hglt
    change g ∈ S.minimalGenerators at hg
    rw [h.minimalGenerators_eq] at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hg5 : g = 5 := by omega
    simp [hg5]
  · exact NumericalSemigroup.minimalGenerator_not_mem_generatedPair
      h5.2.1 ha.2.1 hb (by omega) (by omega)
  · intro n hn hnnot
    apply NumericalSemigroup.least_outside_of_minimalGenerators_below _ hn hnnot
    intro g hg hglt
    change g ∈ S.minimalGenerators at hg
    rw [h.minimalGenerators_eq] at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hga : g = 5 ∨ g = a := by omega
    rcases hga with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · exact NumericalSemigroup.minimalGenerator_not_mem_generatedTriple
      h5.2.1 ha.2.1 hb.2.1 hc (by omega) (by omega) (by omega)
  · intro n hn hnnot
    apply NumericalSemigroup.least_outside_of_minimalGenerators_below _ hn hnnot
    intro g hg hglt
    change g ∈ S.minimalGenerators at hg
    rw [h.minimalGenerators_eq] at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hgab : g = 5 ∨ g = a ∨ g = b := by omega
    rcases hgab with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩

theorem HasFourGenerators.firstNonmultiple_eq {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c) (hm : HasMultiplicity S 5) :
    S.firstNonmultiple 5 (by omega) = a := by
  have hdata := h.normalization_data hm
  apply le_antisymm
  · exact NumericalSemigroup.firstNonmultiple_le h.minimal.2.1.2.1 hdata.1
  · exact hdata.2.1 _ (S.firstNonmultiple_spec 5 (by omega)).1
      (S.firstNonmultiple_spec 5 (by omega)).2

/-- The actual least-outside data required by the formal normal-form theorem. -/
theorem HasFiveGenerators.normalization_data {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d) (hm : HasMultiplicity S 5) :
    ¬5 ∣ a ∧ (∀ n ∈ S.monoid, ¬5 ∣ n → a ≤ n) ∧
      b ∉ generatedPair 5 a ∧ (∀ n ∈ S.monoid, n ∉ generatedPair 5 a → b ≤ n) ∧
      c ∉ generatedTriple a b ∧ (∀ n ∈ S.monoid, n ∉ generatedTriple a b → c ≤ n) := by
  obtain ⟨h5, ha, hb, hc, _⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    exact NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
      (Nat.mod_eq_zero_of_dvd hh)
  · intro n hn hnnot
    apply NumericalSemigroup.least_outside_of_minimalGenerators_below
      (T := AddSubmonoid.multiples 5) _ hn (by simpa using hnnot)
    intro g hg hglt
    change g ∈ S.minimalGenerators at hg
    rw [h.minimalGenerators_eq] at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hg5 : g = 5 := by omega
    simp [hg5]
  · exact NumericalSemigroup.minimalGenerator_not_mem_generatedPair
      h5.2.1 ha.2.1 hb (by omega) (by omega)
  · intro n hn hnnot
    apply NumericalSemigroup.least_outside_of_minimalGenerators_below _ hn hnnot
    intro g hg hglt
    change g ∈ S.minimalGenerators at hg
    rw [h.minimalGenerators_eq] at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hga : g = 5 ∨ g = a := by omega
    rcases hga with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · exact NumericalSemigroup.minimalGenerator_not_mem_generatedTriple
      h5.2.1 ha.2.1 hb.2.1 hc (by omega) (by omega) (by omega)
  · intro n hn hnnot
    apply NumericalSemigroup.least_outside_of_minimalGenerators_below _ hn hnnot
    intro g hg hglt
    change g ∈ S.minimalGenerators at hg
    rw [h.minimalGenerators_eq] at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hgab : g = 5 ∨ g = a ∨ g = b := by omega
    rcases hgab with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩

theorem HasFiveGenerators.firstNonmultiple_eq {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d) (hm : HasMultiplicity S 5) :
    S.firstNonmultiple 5 (by omega) = a := by
  have hdata := h.normalization_data hm
  apply le_antisymm
  · exact NumericalSemigroup.firstNonmultiple_le h.minimal.2.1.2.1 hdata.1
  · exact hdata.2.1 _ (S.firstNonmultiple_spec 5 (by omega)).1
      (S.firstNonmultiple_spec 5 (by omega)).2

/-- The explicit arithmetic alternatives in Theorem 1.1(a). -/
def FourGeneratorCriterion (a b c : ℕ) : Prop :=
  (b % 5 = (2 * a) % 5 ∧ 2 * a < c) ∨
  (b % 5 = (3 * a) % 5 ∧ c % 5 = (4 * a) % 5 ∧ 3 * a < c) ∨
  (b % 5 = (4 * a) % 5 ∧ c % 5 = (3 * a) % 5 ∧ a + b < c)

/-- Lemma 4.1: the genuine first-collision inequality is exactly the release criterion. -/
theorem four_generator_collision_iff {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    firstCollision a b < c ↔ FourGeneratorCriterion a b c := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm ha (by omega)).symm
  have hbnew := h.normalization_data hm |>.2.2.1
  have hcnew := NumericalSemigroup.minimalGenerator_not_mem_generatedPair
    h5.2.1 ha.2.1 hcgen (by omega) (by omega)
  have hdistinct : b % 5 ≠ c % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hbgen hcgen hh
    omega
  constructor
  · intro hgt
    obtain ⟨k, hk, hbk, hba⟩ := new_generator_residue_multiplier hcop hab hbnew
    rcases hk with rfl | rfl | rfl
    · left
      exact ⟨hbk, by rwa [firstCollision_eq_two (by omega) hab hba hcop hbk] at hgt⟩
    · obtain ⟨j, hj, hcj, hca⟩ := new_generator_residue_multiplier hcop (by omega) hcnew
      rw [firstCollision_eq_three (by omega) hab hba hcop hbk] at hgt
      rcases hj with rfl | rfl | rfl
      · omega
      · exact False.elim (hdistinct (hbk.trans hcj.symm))
      · right; left
        have hcab := (four_generator_bounds_4C h hbk hcj).2
        exact ⟨hbk, hcj, by omega⟩
    · obtain ⟨j, hj, hcj, hca⟩ := new_generator_residue_multiplier hcop (by omega) hcnew
      rw [firstCollision_eq_four (by omega) hab hba hcop hbk] at hgt
      rcases hj with rfl | rfl | rfl
      · omega
      · exact Or.inr (Or.inr ⟨hbk, hcj, by omega⟩)
      · exact False.elim (hdistinct (hbk.trans hcj.symm))
  · rintro (⟨hb, hc⟩ | ⟨hb, hcr, hc⟩ | ⟨hb, hcr, hc⟩)
    · have hba := NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
        hm.1 hm.2.1 hbgen (by omega) ha.2.1 ha.1 (by omega) hb
      rwa [firstCollision_eq_two (by omega) hab hba hcop hb]
    · have hba := (four_generator_bounds_4C h hb hcr).1
      rw [firstCollision_eq_three (by omega) hab hba hcop hb]
      omega
    · have hba := (four_generator_bounds_4D h hb hcr).1
      rw [firstCollision_eq_four (by omega) hab hba hcop hb]
      omega

/-- The four mutually exclusive residue cases used by the explicit realizations. -/
def FourGeneratorRealizationCases (a b c : ℕ) : Prop :=
  (b % 5 = (2 * a) % 5 ∧ c % 5 = (3 * a) % 5 ∧ 2 * a < c) ∨
  (b % 5 = (2 * a) % 5 ∧ c % 5 = (4 * a) % 5 ∧ 2 * a < c) ∨
  (b % 5 = (3 * a) % 5 ∧ c % 5 = (4 * a) % 5 ∧ 3 * a < c) ∨
  (b % 5 = (4 * a) % 5 ∧ c % 5 = (3 * a) % 5 ∧ a + b < c)

/-- The first-collision condition covers exactly the four source constructions. -/
theorem four_generator_realization_cases_iff {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    firstCollision a b < c ↔ FourGeneratorRealizationCases a b c := by
  rw [four_generator_collision_iff hm h]
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  constructor
  · rintro (⟨hb, hcgt⟩ | hh | hh)
    · have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm ha (by omega)).symm
      have hcnew := NumericalSemigroup.minimalGenerator_not_mem_generatedPair
        h5.2.1 ha.2.1 hcgen (by omega) (by omega)
      obtain ⟨j, hj, hcj, _⟩ := new_generator_residue_multiplier hcop (by omega) hcnew
      rcases hj with rfl | rfl | rfl
      · have heq := NumericalSemigroup.minimalGenerators_residue_injective hm hbgen hcgen (hb.trans hcj.symm)
        omega
      · exact Or.inl ⟨hb, hcj, hcgt⟩
      · exact Or.inr (Or.inl ⟨hb, hcj, hcgt⟩)
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inr (Or.inr hh))
  · rintro (⟨hb, _, hgt⟩ | ⟨hb, _, hgt⟩ | hh | hh)
    · exact Or.inl ⟨hb, hgt⟩
    · exact Or.inl ⟨hb, hgt⟩
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)

/-- The five-generator positive criterion, using natural residues of the actual generators. -/
def FiveGeneratorCriterion (a b c d : ℕ) : Prop :=
  b % 5 = (2 * a) % 5 ∧ c % 5 = (3 * a) % 5 ∧ d % 5 = (4 * a) % 5 ∧
    2 * a < c ∧ a + b < d

/-- Once five generators are intrinsic and sorted, the lower bounds force the residue clauses. -/
theorem five_generator_criterion_iff_bounds {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    FiveGeneratorCriterion a b c d ↔ 2 * a < c ∧ a + b < d := by
  constructor
  · exact fun h => h.2.2.2
  · rintro ⟨hc, hd⟩
    obtain ⟨hb2, hc3, hd4⟩ := five_generator_residues_of_bounds hm h hc hd
    exact ⟨hb2, hc3, hd4, hc, hd⟩

/-- The maximal-honest-dimension arithmetic uses the true extremal Apéry values. -/
theorem five_generator_extremal_bound_iff {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    S.aperyMax 5 (by omega) < 2 * S.firstNonmultiple 5 (by omega) ↔ d < 2 * a := by
  rw [(five_generator_aperyMax_conductor_general hm h).1, h.firstNonmultiple_eq hm]

/-- The equality case at the maximal-honest-dimension threshold is impossible. -/
theorem five_generator_last_ne_twice_first {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d) : d ≠ 2 * a := by
  obtain ⟨_, ha, _, _, hd⟩ := h.minimal
  intro hh
  have hddec := hd.2.2 a ha.2.1 a ha.2.1 (by omega)
  have h5a := h.five_lt_a
  omega

end HonestEmbeddingDimension
