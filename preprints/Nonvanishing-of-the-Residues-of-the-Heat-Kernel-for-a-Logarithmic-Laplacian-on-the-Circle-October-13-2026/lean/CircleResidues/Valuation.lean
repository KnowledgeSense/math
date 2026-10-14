import CircleResidues.Definitions

noncomputable section
open PowerSeries Finset
namespace CircleResidues

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A finite sum with a unique term of minimum valuation cannot cancel. -/
theorem valuation_sum_unique_min {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℚ) {j : ι} (hj : j ∈ s) (hj0 : f j ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ j → f i ≠ 0 ∧ padicValRat 2 (f j) < padicValRat 2 (f i)) :
    (∑ i ∈ s, f i) ≠ 0 ∧ padicValRat 2 (∑ i ∈ s, f i) = padicValRat 2 (f j) := by
  have hval := (Rat.padicValuation 2).map_sum_eq_of_lt hj (fun i hi => by
    have hi' := Finset.mem_sdiff.mp hi
    have hi0 := (hmin i hi'.1 (by simpa using hi'.2)).1
    have hlt := (hmin i hi'.1 (by simpa using hi'.2)).2
    change (if f i = 0 then 0 else WithZero.exp (-padicValRat 2 (f i))) <
      (if f j = 0 then 0 else WithZero.exp (-padicValRat 2 (f j)))
    simp only [hi0, hj0, ↓reduceIte, WithZero.exp_lt_exp]
    omega)
  have hnz : (∑ i ∈ s, f i) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hval
    exact hj0 ((Rat.padicValuation_eq_zero_iff).mp hval.symm)
  refine ⟨hnz, ?_⟩
  change (if (∑ i ∈ s, f i) = 0 then 0 else WithZero.exp (-padicValRat 2 (∑ i ∈ s, f i))) =
      (if f j = 0 then 0 else WithZero.exp (-padicValRat 2 (f j))) at hval
  simpa only [hnz, hj0, ↓reduceIte, WithZero.exp_inj, neg_inj] using hval

theorem bernoulli_even_nonzero {r : ℕ} (hr : 0 < r) : bernoulli (2 * r) ≠ 0 := by
  have hv := Bernoulli.padicValRat_bernoulli (p := 2) hr (by simp)
  intro hz
  rw [hz, padicValRat.zero] at hv
  norm_num at hv

/-- The derivative coefficient has valuation `-2r-1`, independently of the parameter's odd part. -/
theorem exponent_derivative_valuation (a : ℚ) (ha : a ≠ 0)
    (hva : padicValRat 2 a = -1) {r : ℕ} (hr : 0 < r) :
    let c := coeff r (evenExponent a) * (r : ℚ)
    c ≠ 0 ∧ padicValRat 2 c = -2 * (r : ℤ) - 1 := by
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hpow : (2 : ℚ) ^ (1 - 2 * (r : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hpval : padicValRat 2 ((2 : ℚ) ^ (1 - 2 * (r : ℤ))) = 1 - 2 * (r : ℤ) := by
    have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (p := 2) (by norm_num)
    rw [padicValRat.zpow, htwo]
    ring
  have hpnot : (1 : ℚ) - 2 ^ (1 - 2 * (r : ℤ)) ≠ 0 := by
    intro heq
    have heq' := sub_eq_zero.mp heq
    rw [← heq', padicValRat.one] at hpval
    omega
  have hsubval : padicValRat 2 ((1 : ℚ) - 2 ^ (1 - 2 * (r : ℤ))) =
      1 - 2 * (r : ℤ) := by
    have heq := (Rat.padicValuation 2).map_sub_eq_of_lt_right (x := 1)
      (y := (2 : ℚ) ^ (1 - 2 * (r : ℤ))) (by
        change (if (1 : ℚ) = 0 then 0 else WithZero.exp (-padicValRat 2 (1 : ℚ))) <
          (if (2 : ℚ) ^ (1 - 2 * (r : ℤ)) = 0 then 0 else WithZero.exp _)
        simp only [one_ne_zero, hpow, ↓reduceIte, padicValRat.one, hpval,
          WithZero.exp_lt_exp]
        omega)
    change (if (1 : ℚ) - 2 ^ (1 - 2 * (r : ℤ)) = 0 then 0 else
      WithZero.exp (-padicValRat 2 ((1 : ℚ) - 2 ^ (1 - 2 * (r : ℤ))))) =
      (if (2 : ℚ) ^ (1 - 2 * (r : ℤ)) = 0 then 0 else WithZero.exp _) at heq
    simpa only [hpnot, hpow, ↓reduceIte, hpval, WithZero.exp_inj, neg_inj] using heq
  dsimp only
  simp only [evenExponent, coeff_mk, div_mul_cancel₀ _ hr0]
  have hB := bernoulli_even_nonzero hr
  refine ⟨mul_ne_zero (mul_ne_zero ha hpnot) hB, ?_⟩
  rw [padicValRat.mul (mul_ne_zero ha hpnot) hB,
    padicValRat.mul ha hpnot, hva, hsubval,
    Bernoulli.padicValRat_bernoulli (p := 2) hr (by simp)]
  ring

end CircleResidues
