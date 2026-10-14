import HonestEmbeddingDimension.GeneratorEnumeration

namespace HonestEmbeddingDimension

/-- Any actual Apéry table in rotated coprime residues is residue-injective. -/
theorem residues_injective_of_apery_table {S : NumericalSemigroup} {a : ℕ}
    (ha : Nat.Coprime 5 a) {u : Fin 5 → ℕ}
    (hu : ∀ r : Fin 5, S.aperyMin 5 (by omega) (a * r.val) = u r) :
    Function.Injective (fun r => u r % 5) := by
  intro i j hij
  change u i % 5 = u j % 5 at hij
  rw [← hu i, ← hu j, S.aperyMin_mod, S.aperyMin_mod] at hij
  have hh := Nat.ModEq.cancel_left_of_coprime ha hij
  apply Fin.ext
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hh

/-- The five residue basis orders of source case 4B are genuinely independent. -/
theorem four_generator_basis_residues_4B {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (4 * a) % 5) (hcgt : 2 * a < c) :
    Function.Injective (fun r : Fin 5 => ![0, a, b, a + b, c] r % 5) := by
  have h5a := h.five_lt_a
  exact residues_injective_of_apery_table
    (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
    (four_generator_apery_table_4B hm h hb hc hcgt)

/-- The four residue basis orders of source case 4C are genuinely independent. -/
theorem four_generator_basis_residues_4C {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (3 * a) % 5) (hc : c % 5 = (4 * a) % 5) (hcgt : 3 * a < c) :
    Function.Injective (fun r : Fin 4 => ![0, a, 2 * a, b] r % 5) := by
  have h5a := h.five_lt_a
  have hfull := residues_injective_of_apery_table
    (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
    (four_generator_apery_table_4C hm h hb hc hcgt)
  have hvec (i : Fin 4) : ![0, a, 2 * a, b, c] i.castSucc = ![0, a, 2 * a, b] i := by
    fin_cases i <;> rfl
  intro i j hij
  have hh : ![0, a, 2 * a, b, c] i.castSucc % 5 = ![0, a, 2 * a, b, c] j.castSucc % 5 := by
    rwa [hvec, hvec]
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) (hfull hh))

/-- The four residue basis orders of source case 4D are genuinely independent. -/
theorem four_generator_basis_residues_4D {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c)
    (hb : b % 5 = (4 * a) % 5) (hc : c % 5 = (3 * a) % 5) (hcgt : a + b < c) :
    Function.Injective (fun r : Fin 4 => ![0, a, 2 * a, b] r % 5) := by
  have h5a := h.five_lt_a
  have hfull := residues_injective_of_apery_table
    (NumericalSemigroup.minimalGenerator_coprime_five hm h.minimal.2.1 (by omega)).symm
    (four_generator_apery_table_4D hm h hb hc hcgt)
  let f : Fin 4 → Fin 5 := ![0, 1, 2, 4]
  have hf : Function.Injective f := by decide
  have hvec (i : Fin 4) : ![0, a, 2 * a, c, b] (f i) = ![0, a, 2 * a, b] i := by
    fin_cases i <;> rfl
  intro i j hij
  apply hf
  apply hfull
  change ![0, a, 2 * a, c, b] (f i) % 5 = ![0, a, 2 * a, c, b] (f j) % 5
  rwa [hvec, hvec]

/-- Every positive quotient and tail inequality required by the binomial case 4B. -/
theorem four_generator_parameters_4B {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (2 * a) % 5) (hc : c % 5 = (4 * a) % 5) (hcgt : 2 * a < c) :
    0 < c - 2 * a ∧ 0 < (2 * a - b) / 5 ∧
      5 * ((2 * a - b) / 5) + b = 2 * a ∧
      max (a + b) c ≤ 2 * a + b ∧ max (a + b) c ≤ a + c ∧
      max (a + b) c ≤ 2 * b ∧ max (a + b) c ≤ a + 2 * b ∧
      max (a + b) c ≤ b + c := by
  obtain ⟨hba, hcb⟩ := four_generator_bounds_4B h hb hc
  obtain ⟨hu, hueq⟩ := positive_five_quotient hba hb
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  omega

/-- Every positive quotient and tail inequality required by the binomial case 4C. -/
theorem four_generator_parameters_4C {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (3 * a) % 5) (hc : c % 5 = (4 * a) % 5) (hcgt : 3 * a < c) :
    0 < c - 3 * a ∧ 0 < (3 * a - b) / 5 ∧
      5 * ((3 * a - b) / 5) + b = 3 * a ∧
      c ≤ a + b ∧ c ≤ 2 * a + b ∧ c ≤ 2 * b := by
  obtain ⟨hba, hcab⟩ := four_generator_bounds_4C h hb hc
  obtain ⟨hu, hueq⟩ := positive_five_quotient hba hb
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  omega

/-- Every positive quotient and tail inequality required by the binomial case 4D. -/
theorem four_generator_parameters_4D {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c)
    (hb : b % 5 = (4 * a) % 5) (hc : c % 5 = (3 * a) % 5) (hcgt : a + b < c) :
    0 < c - a - b ∧ 0 < (a + b) / 5 ∧ 5 * ((a + b) / 5) = a + b ∧
      c ≤ 3 * a ∧ c ≤ 2 * a + b ∧ c ≤ 2 * b := by
  obtain ⟨_, hca, hcb⟩ := four_generator_bounds_4D h hb hc
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hdiv : 5 ∣ a + b := Nat.dvd_of_mod_eq_zero (by omega)
  have hueq := Nat.mul_div_cancel' hdiv
  omega

/-- Step 2 of five-generator necessity uses only the first quadratic lower bound. -/
theorem five_generator_second_of_first_bound {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) (hcgt : 2 * a < c) :
    b % 5 = (2 * a) % 5 ∧ b < 2 * a := by
  obtain ⟨_, ha, hb, _, _⟩ := h.minimal
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have ha0 := NumericalSemigroup.minimalGenerator_mod_ne_zero hm.1 hm.2.1 ha (by omega)
  have hb2 : b % 5 = (2 * a) % 5 := by
    have hmem := S.aperyMin_mem_apery 5 hm.1 (2 * a)
    rw [five_generator_apery_set hm h] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hmod := S.aperyMin_mod 5 hm.1 (2 * a)
    have hle : S.aperyMin 5 hm.1 (2 * a) ≤ 2 * a := by
      apply NumericalSemigroup.aperyMin_le _ rfl
      simpa [Nat.mul_comm] using NumericalSemigroup.mul_mem ha.2.1 2
    rcases hmem with heq | heq | heq | heq | heq <;> rw [heq] at hmod hle <;> omega
  exact ⟨hb2, NumericalSemigroup.minimalGenerator_lt_multiple_of_same_residue
    hm.1 hm.2.1 hb (by omega) ha.2.1 ha.1 (by omega) hb2⟩

end HonestEmbeddingDimension
