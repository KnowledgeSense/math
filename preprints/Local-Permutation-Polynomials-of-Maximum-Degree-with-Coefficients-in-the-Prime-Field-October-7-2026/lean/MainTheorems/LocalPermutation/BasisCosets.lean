import MainTheorems.LocalPermutation.NormalBasis

namespace ResearchMain.LocalPermutation

open Classical Module

variable {F K I : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype I]

omit [Fintype F] in
theorem normalized_coordinates_one (b : Basis I F K) (hsum : (∑ i, b i) = 1) (j : I) :
    b.equivFun 1 j = 1 := by
  rw [← hsum, map_sum]
  simp only [Finset.sum_apply, Basis.equivFun_self]
  simp

omit [Fintype F] in
theorem normalized_coordinates_scalar (b : Basis I F K) (hsum : (∑ i, b i) = 1) (c : F) (j : I) :
    b.equivFun (algebraMap F K c) j = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  simp only [Pi.smul_apply, normalized_coordinates_one b hsum, smul_eq_mul, mul_one]

omit [Fintype F] in
theorem normalized_coordinates_coset (b : Basis I F K) (hsum : (∑ i, b i) = 1) (i j : I) (c : F) :
    b.equivFun (b i + algebraMap F K c) j = (if i = j then 1 else 0) + c := by
  rw [map_add]
  simp only [Pi.add_apply, Basis.equivFun_self, normalized_coordinates_scalar b hsum]

omit [Fintype F] in
theorem normalized_coordinates_twice (b : Basis I F K) (i j : I) :
    b.equivFun (2 * b i) j = if i = j then 2 else 0 := by
  rw [show (2 : K) * b i = (2 : F) • b i by
    rw [Algebra.smul_def, show (2 : F) = 1 + 1 by ring, map_add, map_one]
    ring, map_smul]
  simp only [Pi.smul_apply, Basis.equivFun_self, smul_eq_mul]
  split_ifs <;> simp

noncomputable def basisCosets (b : Basis I F K) : Finset K :=
  Finset.univ.image (fun x : I × F => b x.1 + algebraMap F K x.2)

theorem mem_basisCosets (b : Basis I F K) (x : K) : x ∈ basisCosets b ↔
    ∃ i c, b i + algebraMap F K c = x := by
  simp only [basisCosets, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]

omit [Fintype F] in
theorem basisCosets_injective (b : Basis I F K) (hsum : (∑ i, b i) = 1) (h2 : (2 : F) ≠ 0) :
    Function.Injective (fun x : I × F => b x.1 + algebraMap F K x.2) := by
  rintro ⟨i, c⟩ ⟨j, d⟩ h
  change b i + algebraMap F K c = b j + algebraMap F K d at h
  by_cases hij : i = j
  · subst j
    have hcd : c = d := (algebraMap F K).injective (add_left_cancel h)
    exact Prod.ext rfl hcd
  · have hi := congrArg (fun x => b.equivFun x i) h
    have hj := congrArg (fun x => b.equivFun x j) h
    simp only [normalized_coordinates_coset b hsum, hij, Ne.symm hij, ite_true, ite_false,
      zero_add] at hi hj
    apply False.elim
    apply h2
    linear_combination hi - hj

theorem twice_basis_not_mem_cosets [Nontrivial I] (b : Basis I F K) (hsum : (∑ i, b i) = 1)
    (h3 : (3 : F) ≠ 0) (i : I) : 2 * b i ∉ basisCosets b := by
  intro h
  obtain ⟨j, c, hc⟩ := (mem_basisCosets b _).mp h
  have hi := congrArg (fun x => b.equivFun x i) hc
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hk⟩ := exists_ne i
    have hki : i ≠ k := hk.symm
    have hk' := congrArg (fun x => b.equivFun x k) hc
    simp only [normalized_coordinates_coset b hsum, normalized_coordinates_twice,
      hki, ite_true, ite_false, zero_add] at hi hk'
    have h10 : (1 : F) = 0 := by linear_combination hk' - hi
    exact one_ne_zero h10
  · have hj := congrArg (fun x => b.equivFun x j) hc
    simp only [normalized_coordinates_coset b hsum, normalized_coordinates_twice,
      hij, Ne.symm hij, ite_true, ite_false, zero_add] at hi hj
    apply h3
    linear_combination hj - hi

theorem basisCosets_shift (b : Basis I F K) (x : K) (hx : x ∈ basisCosets b) :
    x + 1 ∈ basisCosets b := by
  obtain ⟨i, c, hc⟩ := (mem_basisCosets b x).mp hx
  apply (mem_basisCosets b (x + 1)).mpr
  refine ⟨i, c + 1, ?_⟩
  rw [map_add, map_one, ← hc]
  ring

theorem basisCosets_sum (b : Basis I F K) (hsum : (∑ i, b i) = 1) (h2 : (2 : F) ≠ 0)
    (hq : 2 < Fintype.card F) : (∑ x ∈ basisCosets b, x) = 0 := by
  have hcard : (Fintype.card F : K) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg (algebraMap F K) (FiniteField.cast_card_eq_zero F)
  have hF : (∑ c : F, algebraMap F K c) = 0 := by
    rw [← map_sum, show (∑ c : F, c) = 0 from by
      simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one F 1 (by omega), map_zero]
  unfold basisCosets
  rw [Finset.sum_image (fun a _ b _ h => basisCosets_injective _ hsum h2 h), Fintype.sum_prod_type]
  have hs (i : I) : (∑ c : F, (b i + algebraMap F K c)) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, zero_mul, hF, zero_add]
  simp_rw [hs]
  simp

end ResearchMain.LocalPermutation
