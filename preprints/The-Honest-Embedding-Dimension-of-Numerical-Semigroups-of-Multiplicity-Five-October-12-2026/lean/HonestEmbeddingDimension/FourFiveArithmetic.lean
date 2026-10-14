import HonestEmbeddingDimension.MinimalGeneratorOrder

namespace HonestEmbeddingDimension

/-- Exactly the four sorted intrinsic minimal generators in the source theorem. -/
structure HasFourGenerators (S : NumericalSemigroup) (a b c : ℕ) : Prop where
  minimalGenerators_eq : S.minimalGenerators = {5, a, b, c}
  five_lt_a : 5 < a
  a_lt_b : a < b
  b_lt_c : b < c

/-- Exactly the five sorted intrinsic minimal generators in the source theorem. -/
structure HasFiveGenerators (S : NumericalSemigroup) (a b c d : ℕ) : Prop where
  minimalGenerators_eq : S.minimalGenerators = {5, a, b, c, d}
  five_lt_a : 5 < a
  a_lt_b : a < b
  b_lt_c : b < c
  c_lt_d : c < d

namespace HasFourGenerators

theorem minimal {S : NumericalSemigroup} {a b c : ℕ} (h : HasFourGenerators S a b c) :
    S.IsMinimalGenerator 5 ∧ S.IsMinimalGenerator a ∧ S.IsMinimalGenerator b ∧
      S.IsMinimalGenerator c := by
  have hh (n : ℕ) : S.IsMinimalGenerator n ↔ n ∈ ({5, a, b, c} : Set ℕ) := by
    change n ∈ S.minimalGenerators ↔ _
    rw [h.minimalGenerators_eq]
  exact ⟨(hh 5).mpr (by simp), (hh a).mpr (by simp),
    (hh b).mpr (by simp), (hh c).mpr (by simp)⟩

theorem generates {S : NumericalSemigroup} {a b c : ℕ} (h : HasFourGenerators S a b c) :
    AddSubmonoid.closure ({5, a, b, c} : Set ℕ) = S.monoid := by
  rw [← h.minimalGenerators_eq, S.closure_minimalGenerators]

end HasFourGenerators

namespace HasFiveGenerators

theorem minimal {S : NumericalSemigroup} {a b c d : ℕ} (h : HasFiveGenerators S a b c d) :
    S.IsMinimalGenerator 5 ∧ S.IsMinimalGenerator a ∧ S.IsMinimalGenerator b ∧
      S.IsMinimalGenerator c ∧ S.IsMinimalGenerator d := by
  have hh (n : ℕ) : S.IsMinimalGenerator n ↔ n ∈ ({5, a, b, c, d} : Set ℕ) := by
    change n ∈ S.minimalGenerators ↔ _
    rw [h.minimalGenerators_eq]
  exact ⟨(hh 5).mpr (by simp), (hh a).mpr (by simp), (hh b).mpr (by simp),
    (hh c).mpr (by simp), (hh d).mpr (by simp)⟩

theorem generates {S : NumericalSemigroup} {a b c d : ℕ} (h : HasFiveGenerators S a b c d) :
    AddSubmonoid.closure ({5, a, b, c, d} : Set ℕ) = S.monoid := by
  rw [← h.minimalGenerators_eq, S.closure_minimalGenerators]

end HasFiveGenerators

/-- Strict Kunz inequalities in the positive five-generator residue arrangement. -/
theorem five_generator_strict_bounds {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hd : d % 5 = (4 * a) % 5) :
    b < 2 * a ∧ c < a + b ∧ d < 2 * b ∧ d < a + c := by
  obtain ⟨h5, ha, hbgen, hcgen, hdgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have hba := NumericalSemigroup.minimalGenerator_lt_sum_of_same_residue
    (by omega : 0 < 5) h5.2.1 hbgen (by omega) ha.2.1 ha.2.1 ha.1 ha.1
    (show b % 5 = (a + a) % 5 by omega)
  have hcab := NumericalSemigroup.minimalGenerator_lt_sum_of_same_residue
    (by omega : 0 < 5) h5.2.1 hcgen (by omega) ha.2.1 hbgen.2.1 ha.1 hbgen.1
    (show c % 5 = (a + b) % 5 by omega)
  have hdb := NumericalSemigroup.minimalGenerator_lt_sum_of_same_residue
    (by omega : 0 < 5) h5.2.1 hdgen (by omega) hbgen.2.1 hbgen.2.1 hbgen.1 hbgen.1
    (show d % 5 = (b + b) % 5 by omega)
  have hdac := NumericalSemigroup.minimalGenerator_lt_sum_of_same_residue
    (by omega : 0 < 5) h5.2.1 hdgen (by omega) ha.2.1 hcgen.2.1 ha.1 hcgen.1
    (show d % 5 = (a + c) % 5 by omega)
  omega

/-- With five minimal generators the residue table consists precisely of those generators. -/
theorem five_generator_apery_table {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hd : d % 5 = (4 * a) % 5) :
    ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = ![0, a, b, c, d] r := by
  obtain ⟨h5, ha, hbgen, hcgen, hdgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  intro r
  fin_cases r
  · exact S.aperyMin_zero 5 (by omega)
  · change S.aperyMin 5 (by omega) (a * 1) = a
    exact NumericalSemigroup.aperyMin_eq_minimalGenerator (by omega) h5.2.1 ha (by omega) (by omega)
  · change S.aperyMin 5 (by omega) (a * 2) = b
    exact NumericalSemigroup.aperyMin_eq_minimalGenerator (by omega) h5.2.1 hbgen (by omega) (by omega)
  · change S.aperyMin 5 (by omega) (a * 3) = c
    exact NumericalSemigroup.aperyMin_eq_minimalGenerator (by omega) h5.2.1 hcgen (by omega) (by omega)
  · change S.aperyMin 5 (by omega) (a * 4) = d
    exact NumericalSemigroup.aperyMin_eq_minimalGenerator (by omega) h5.2.1 hdgen (by omega) (by omega)

/-- A finite Apéry table bounds every actual Apéry element. -/
theorem apery_le_of_rotated_table {S : NumericalSemigroup} {a W : ℕ}
    (ha : Nat.Coprime 5 a) (h5 : 5 ∈ S.monoid)
    (hbound : ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) ≤ W)
    {n : ℕ} (hn : n ∈ S.apery 5) : n ≤ W := by
  obtain ⟨r, hr⟩ := exists_residue_multiplier_five (n := n) ha
  have heq := (NumericalSemigroup.mem_apery_iff_eq_aperyMin (by omega) h5).mp hn
  rw [NumericalSemigroup.aperyMin_eq_of_mod_eq hr] at heq
  rw [heq]
  exact hbound r

/-- The largest Apéry value and the actual conductor in the positive five-generator case. -/
theorem five_generator_aperyMax_conductor {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hd : d % 5 = (4 * a) % 5) :
    S.aperyMax 5 (by omega) = d ∧ S.conductor = d - 4 := by
  obtain ⟨h5, ha, _, _, hdgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm ha (by omega)).symm
  have hmax : S.aperyMax 5 (by omega) = d := by
    apply le_antisymm
    · apply apery_le_of_rotated_table hcop h5.2.1 _ (S.aperyMax_mem 5 (by omega))
      intro r
      rw [five_generator_apery_table h hb hc hd r]
      fin_cases r <;> dsimp <;> omega
    · exact NumericalSemigroup.le_aperyMax
        (NumericalSemigroup.minimalGenerator_mem_apery (by omega) h5.2.1 hdgen (by omega))
  exact ⟨hmax, by rw [NumericalSemigroup.conductor_eq_aperyMax_sub_four hm, hmax]⟩

/-- Positive quotient parameters of all same-residue cancellation identities. -/
theorem positive_five_quotient {x y : ℕ} (hxy : x < y) (hr : x % 5 = y % 5) :
    0 < (y - x) / 5 ∧ 5 * ((y - x) / 5) + x = y := by
  have hdiv : 5 ∣ y - x := (Nat.modEq_iff_dvd' hxy.le).mp hr
  have heq := Nat.mul_div_cancel' hdiv
  constructor
  · have hh := Nat.ModEq.add_le_of_lt hr hxy
    omega
  · omega

/-- The exact positive parameters and tail bound needed by the rational five-generator germ. -/
theorem five_generator_positive_parameters {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hd : d % 5 = (4 * a) % 5) (hc2 : 2 * a < c) (hdab : a + b < d) :
    0 < c - 2 * a ∧ 0 < d - a - b ∧
      0 < (2 * a - b) / 5 ∧ 0 < (a + b - c) / 5 ∧
      5 * ((2 * a - b) / 5) + b = 2 * a ∧
      5 * ((a + b - c) / 5) + c = a + b ∧ d < 2 * b ∧ d < a + c := by
  obtain ⟨hba, hcab, hdb, hdac⟩ := five_generator_strict_bounds h hb hc hd
  obtain ⟨hu, hueq⟩ := positive_five_quotient hba hb
  obtain ⟨hv, hveq⟩ := positive_five_quotient hcab (show c % 5 = (a + b) % 5 by omega)
  omega

/-- Addition of a generator shifts the rotated residue index by its multiplier. -/
theorem rotated_residue_add {a g k : ℕ} (hg : g % 5 = (k * a) % 5) (r : Fin 5) :
    (a * (residueIndexFive (r.val + k)).val) % 5 = (a * r.val + g) % 5 := by
  change (a * ((r.val + k) % 5)) % 5 = (a * r.val + g) % 5
  calc
    _ = (a * (r.val + k)) % 5 := by simp [Nat.mul_mod]
    _ = (a * r.val + g) % 5 := by simp [Nat.mul_add, Nat.add_mod, hg, Nat.mul_comm]

/-- A four-generator transition table is a certificate for the genuine Apéry minima. -/
theorem four_generator_table_of_transitions {S : NumericalSemigroup} {a b c k j : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (k * a) % 5) (hc : c % 5 = (j * a) % 5)
    (u : Fin 5 → ℕ) (hzero : u 0 = 0) (hmem : ∀ r, u r ∈ S.monoid)
    (hmod : ∀ r, u r % 5 = (a * r.val) % 5)
    (hA : ∀ r, u (residueIndexFive (r.val + 1)) ≤ u r + a)
    (hB : ∀ r, u (residueIndexFive (r.val + k)) ≤ u r + b)
    (hC : ∀ r, u (residueIndexFive (r.val + j)) ≤ u r + c) :
    ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = u r := by
  have h5a := h.five_lt_a
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
  apply apery_table_of_generator_transitions S h.generates hcop u hzero hmem hmod
  intro g hg r
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨r, by omega, by omega⟩
  · exact ⟨residueIndexFive (r.val + 1), rotated_residue_add (by simp) r, hA r⟩
  · exact ⟨residueIndexFive (r.val + k), rotated_residue_add hb r, hB r⟩
  · exact ⟨residueIndexFive (r.val + j), rotated_residue_add hc r, hC r⟩

/-- The strict upper bounds for source case 4A. -/
theorem four_generator_bounds_4A {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5) :
    b < 2 * a ∧ c < a + b := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  refine ⟨NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
    (by omega) h5.2.1 hbgen (by omega) ha.2.1 ha.1 (by omega) hb, ?_⟩
  exact NumericalSemigroup.minimalGenerator_lt_sum_of_same_residue
    (by omega) h5.2.1 hcgen (by omega) ha.2.1 hbgen.2.1 ha.1 hbgen.1 (by omega)

/-- The strict upper bounds for source case 4B. -/
theorem four_generator_bounds_4B {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (4 * a) % 5) :
    b < 2 * a ∧ c < 2 * b := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  refine ⟨NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
    (by omega) h5.2.1 hbgen (by omega) ha.2.1 ha.1 (by omega) hb, ?_⟩
  exact NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
    (by omega) h5.2.1 hcgen (by omega) hbgen.2.1 hbgen.1 (by omega) (by omega)

/-- The strict upper bounds for source case 4C. -/
theorem four_generator_bounds_4C {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (3 * a) % 5) (hc : c % 5 = (4 * a) % 5) :
    b < 3 * a ∧ c < a + b := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  refine ⟨NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
    (by omega) h5.2.1 hbgen (by omega) ha.2.1 ha.1 (by omega) hb, ?_⟩
  exact NumericalSemigroup.minimalGenerator_lt_sum_of_same_residue
    (by omega) h5.2.1 hcgen (by omega) ha.2.1 hbgen.2.1 ha.1 hbgen.1 (by omega)

/-- The strict upper bounds for source case 4D. -/
theorem four_generator_bounds_4D {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (4 * a) % 5) (hc : c % 5 = (3 * a) % 5) :
    b < 4 * a ∧ c < 3 * a ∧ c < 2 * b := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  refine ⟨NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
    (by omega) h5.2.1 hbgen (by omega) ha.2.1 ha.1 (by omega) hb, ?_, ?_⟩
  · exact NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
      (by omega) h5.2.1 hcgen (by omega) ha.2.1 ha.1 (by omega) hc
  · exact NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
      (by omega) h5.2.1 hcgen (by omega) hbgen.2.1 hbgen.1 (by omega) (by omega)

/-- The actual Apéry table of the source realization case 4A. -/
theorem four_generator_apery_table_4A {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hcgt : 2 * a < c) :
    ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = ![0, a, b, c, min (a + c) (2 * b)] r := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  obtain ⟨hba, hcab⟩ := four_generator_bounds_4A h hb hc
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  apply four_generator_table_of_transitions hm h hb hc
  · rfl
  · intro r
    fin_cases r
    · exact S.monoid.zero_mem
    · exact ha.2.1
    · exact hbgen.2.1
    · exact hcgen.2.1
    · rcases le_total (a + c) (2 * b) with hh | hh
      · change min (a + c) (2 * b) ∈ S.monoid
        rw [min_eq_left hh]
        exact S.monoid.add_mem ha.2.1 hcgen.2.1
      · change min (a + c) (2 * b) ∈ S.monoid
        rw [min_eq_right hh]
        simpa [Nat.mul_comm] using NumericalSemigroup.mul_mem hbgen.2.1 2
  · intro r
    fin_cases r <;> dsimp <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega

/-- The actual Apéry table of the source realization case 4B. -/
theorem four_generator_apery_table_4B {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (4 * a) % 5)
    (hcgt : 2 * a < c) :
    ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = ![0, a, b, a + b, c] r := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  obtain ⟨hba, hcb⟩ := four_generator_bounds_4B h hb hc
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  apply four_generator_table_of_transitions hm h hb hc
  · rfl
  · intro r
    fin_cases r
    · exact S.monoid.zero_mem
    · exact ha.2.1
    · exact hbgen.2.1
    · exact S.monoid.add_mem ha.2.1 hbgen.2.1
    · exact hcgen.2.1
  · intro r
    fin_cases r <;> dsimp <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega

/-- The actual Apéry table of the source realization case 4C. -/
theorem four_generator_apery_table_4C {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (3 * a) % 5) (hc : c % 5 = (4 * a) % 5)
    (hcgt : 3 * a < c) :
    ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = ![0, a, 2 * a, b, c] r := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  obtain ⟨hba, hcab⟩ := four_generator_bounds_4C h hb hc
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  apply four_generator_table_of_transitions hm h hb hc
  · rfl
  · intro r
    fin_cases r
    · exact S.monoid.zero_mem
    · exact ha.2.1
    · simpa [Nat.mul_comm] using NumericalSemigroup.mul_mem ha.2.1 2
    · exact hbgen.2.1
    · exact hcgen.2.1
  · intro r
    fin_cases r <;> dsimp <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega

/-- The actual Apéry table of the source realization case 4D. -/
theorem four_generator_apery_table_4D {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (4 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hcgt : a + b < c) :
    ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = ![0, a, 2 * a, c, b] r := by
  obtain ⟨h5, ha, hbgen, hcgen⟩ := h.minimal
  obtain ⟨hba, hca, hcb⟩ := four_generator_bounds_4D h hb hc
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  apply four_generator_table_of_transitions hm h hb hc
  · rfl
  · intro r
    fin_cases r
    · exact S.monoid.zero_mem
    · exact ha.2.1
    · simpa [Nat.mul_comm] using NumericalSemigroup.mul_mem ha.2.1 2
    · exact hcgen.2.1
    · exact hbgen.2.1
  · intro r
    fin_cases r <;> dsimp <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega
  · intro r
    fin_cases r <;> dsimp [residueIndexFive] <;> omega

/-- The orders `0,a,b,c` in a four-generator semigroup are pairwise incongruent. -/
theorem four_generator_basis_residues_injective {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    Function.Injective (fun i : Fin 4 => ![0, a, b, c] i % 5) := by
  obtain ⟨_, ha, hb, hc⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have ha0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
  have hb0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hb (by omega)
  have hc0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 hc (by omega)
  have habr : a % 5 ≠ b % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hb hh
    omega
  have hacr : a % 5 ≠ c % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm ha hc hh
    omega
  have hbcr : b % 5 ≠ c % 5 := by
    intro hh
    have := NumericalSemigroup.minimalGenerators_residue_injective hm hb hc hh
    omega
  intro i j hij
  fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;> first | rfl | omega

/-- The positive cancellation parameters of source case 4A. -/
theorem four_generator_parameters_4A {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hcgt : 2 * a < c) :
    0 < c - 2 * a ∧ 0 < (2 * a - b) / 5 ∧ 0 < (a + b - c) / 5 ∧
      5 * ((2 * a - b) / 5) + b = 2 * a ∧
      5 * ((a + b - c) / 5) + c = a + b ∧
      c < min (a + c) (2 * b) ∧ min (a + c) (2 * b) ≤ 2 * b := by
  obtain ⟨hba, hcab⟩ := four_generator_bounds_4A h hb hc
  obtain ⟨hu, hueq⟩ := positive_five_quotient hba hb
  obtain ⟨hv, hveq⟩ := positive_five_quotient hcab (show c % 5 = (a + b) % 5 by omega)
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  omega

/-- The exact largest Apéry element and conductor in source case 4A. -/
theorem four_generator_conductor_4A {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hcgt : 2 * a < c) :
    S.aperyMax 5 (by omega) = min (a + c) (2 * b) ∧ S.conductor = (min (a + c) (2 * b)) - 4 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  obtain ⟨hba, hcab⟩ := four_generator_bounds_4A h hb hc
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
  have htable := four_generator_apery_table_4A hm h hb hc hcgt
  have hmax : S.aperyMax 5 (by omega) = min (a + c) (2 * b) := by
    apply le_antisymm
    · apply apery_le_of_rotated_table hcop hm.2.1 _ (S.aperyMax_mem 5 (by omega))
      intro r
      rw [htable r]
      fin_cases r <;> dsimp <;> omega
    · have h3 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 3))
      have h4 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 4))
      have ht3 := htable 3
      have ht4 := htable 4
      dsimp at ht3 ht4
      rw [ht3] at h3
      rw [ht4] at h4
      omega
  exact ⟨hmax, by rw [NumericalSemigroup.conductor_eq_aperyMax_sub_four hm, hmax]⟩

/-- The exact largest Apéry element and conductor in source case 4B. -/
theorem four_generator_conductor_4B {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (4 * a) % 5)
    (hcgt : 2 * a < c) :
    S.aperyMax 5 (by omega) = max (a + b) c ∧ S.conductor = (max (a + b) c) - 4 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  obtain ⟨hba, hcb⟩ := four_generator_bounds_4B h hb hc
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
  have htable := four_generator_apery_table_4B hm h hb hc hcgt
  have hmax : S.aperyMax 5 (by omega) = max (a + b) c := by
    apply le_antisymm
    · apply apery_le_of_rotated_table hcop hm.2.1 _ (S.aperyMax_mem 5 (by omega))
      intro r
      rw [htable r]
      fin_cases r <;> dsimp <;> omega
    · have h3 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 3))
      have h4 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 4))
      have ht3 := htable 3
      have ht4 := htable 4
      dsimp at ht3 ht4
      rw [ht3] at h3
      rw [ht4] at h4
      omega
  exact ⟨hmax, by rw [NumericalSemigroup.conductor_eq_aperyMax_sub_four hm, hmax]⟩

/-- The exact largest Apéry element and conductor in source case 4C. -/
theorem four_generator_conductor_4C {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (3 * a) % 5) (hc : c % 5 = (4 * a) % 5)
    (hcgt : 3 * a < c) :
    S.aperyMax 5 (by omega) = c ∧ S.conductor = (c) - 4 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  obtain ⟨hba, hcab⟩ := four_generator_bounds_4C h hb hc
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
  have htable := four_generator_apery_table_4C hm h hb hc hcgt
  have hmax : S.aperyMax 5 (by omega) = c := by
    apply le_antisymm
    · apply apery_le_of_rotated_table hcop hm.2.1 _ (S.aperyMax_mem 5 (by omega))
      intro r
      rw [htable r]
      fin_cases r <;> dsimp <;> omega
    · have h3 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 3))
      have h4 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 4))
      have ht3 := htable 3
      have ht4 := htable 4
      dsimp at ht3 ht4
      rw [ht3] at h3
      rw [ht4] at h4
      omega
  exact ⟨hmax, by rw [NumericalSemigroup.conductor_eq_aperyMax_sub_four hm, hmax]⟩

/-- The exact largest Apéry element and conductor in source case 4D. -/
theorem four_generator_conductor_4D {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (4 * a) % 5) (hc : c % 5 = (3 * a) % 5)
    (hcgt : a + b < c) :
    S.aperyMax 5 (by omega) = c ∧ S.conductor = (c) - 4 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  obtain ⟨hba, hca, hcb⟩ := four_generator_bounds_4D h hb hc
  have hcop := (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
  have htable := four_generator_apery_table_4D hm h hb hc hcgt
  have hmax : S.aperyMax 5 (by omega) = c := by
    apply le_antisymm
    · apply apery_le_of_rotated_table hcop hm.2.1 _ (S.aperyMax_mem 5 (by omega))
      intro r
      rw [htable r]
      fin_cases r <;> dsimp <;> omega
    · have h3 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 3))
      have h4 := NumericalSemigroup.le_aperyMax (hm := hm.1) (S.aperyMin_mem_apery 5 (by omega) (a * 4))
      have ht3 := htable 3
      have ht4 := htable 4
      dsimp at ht3 ht4
      rw [ht3] at h3
      rw [ht4] at h4
      omega
  exact ⟨hmax, by rw [NumericalSemigroup.conductor_eq_aperyMax_sub_four hm, hmax]⟩

end HonestEmbeddingDimension
