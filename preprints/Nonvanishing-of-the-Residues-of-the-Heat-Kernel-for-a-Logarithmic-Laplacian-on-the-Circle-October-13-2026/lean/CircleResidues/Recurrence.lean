import CircleResidues.Valuation

noncomputable section
open PowerSeries Finset
namespace CircleResidues
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The coefficient recurrence obtained by differentiating the actual formal exponential. -/
theorem evenResidue_recurrence (a : ℚ) (n : ℕ) :
    evenResidue a (n + 1) * (n + 1 : ℚ) =
      ∑ i ∈ range (n + 1),
        (coeff (i + 1) (evenExponent a) * (i + 1 : ℚ)) * evenResidue a (n - i) := by
  have h := congrArg (coeff n) (derivative_subst (f := exp ℚ) (evenExponent_hasSubst a))
  rw [derivative_exp, mul_comm] at h
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [evenResidue, coeff_derivative, Nat.cast_add, Nat.cast_one] using h

theorem factorial_valuation_mono {k n : ℕ} (h : k ≤ n) :
    padicValNat 2 k.factorial ≤ padicValNat 2 n.factorial := by
  apply (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
  exact (pow_padicValNat_dvd).trans (Nat.factorial_dvd_factorial h)

/-- Every reduced coefficient is nonzero and has its exact valuation. -/
theorem evenResidue_valuation (a : ℚ) (ha : a ≠ 0)
    (hva : padicValRat 2 a = -1) (n : ℕ) :
    evenResidue a n ≠ 0 ∧
      padicValRat 2 (evenResidue a n) = -3 * (n : ℤ) - padicValNat 2 n.factorial := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      let f : ℕ → ℚ := fun i =>
        (coeff (i + 1) (evenExponent a) * (i + 1 : ℚ)) * evenResidue a (n - i)
      have hf (i : ℕ) (hi : i ≤ n) :
          f i ≠ 0 ∧ padicValRat 2 (f i) =
            -3 * ((n : ℤ) + 1) + (i : ℤ) - padicValNat 2 (n - i).factorial := by
        have hc := exponent_derivative_valuation a ha hva (Nat.succ_pos i)
        dsimp only at hc
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hc
        have hp := ih (n - i) (by omega)
        refine ⟨mul_ne_zero hc.1 hp.1, ?_⟩
        dsimp [f]
        rw [padicValRat.mul hc.1 hp.1, hc.2, hp.2, Nat.cast_sub hi]
        push_cast
        ring
      have hs := valuation_sum_unique_min (range (n + 1)) f (j := 0)
        (by simp) (hf 0 (by omega)).1 (by
          intro i hi hi0
          have hin : i ≤ n := by have hi' := Finset.mem_range.mp hi; omega
          refine ⟨(hf i hin).1, ?_⟩
          rw [(hf 0 (by omega)).2, (hf i hin).2]
          simp only [Nat.sub_zero, Nat.cast_zero, add_zero]
          have hm := factorial_valuation_mono (Nat.sub_le n i)
          have hm' : (padicValNat 2 (n - i).factorial : ℤ) ≤ padicValNat 2 n.factorial := by
            exact_mod_cast hm
          have hip : (0 : ℤ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi0
          omega)
      have hrec : evenResidue a (n + 1) * (n + 1 : ℚ) = ∑ i ∈ range (n + 1), f i :=
        evenResidue_recurrence a n
      have hp0 : evenResidue a (n + 1) ≠ 0 := by
        intro heq
        rw [heq, zero_mul] at hrec
        exact hs.1 hrec.symm
      refine ⟨hp0, ?_⟩
      have hn0 : (n + 1 : ℚ) ≠ 0 := by positivity
      have heq := congrArg (padicValRat 2) hrec
      rw [padicValRat.mul hp0 hn0, hs.2, (hf 0 (by omega)).2] at heq
      simp only [Nat.sub_zero, Nat.cast_zero, add_zero] at heq
      have hfac : padicValNat 2 (n + 1).factorial =
          padicValNat 2 (n + 1) + padicValNat 2 n.factorial := by
        rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
      rw [hfac]
      have hcast : padicValRat 2 (n + 1 : ℚ) = (padicValNat 2 (n + 1) : ℤ) := by
        norm_cast
      rw [hcast] at heq
      simp only [Nat.cast_add, Nat.cast_one]
      omega

end CircleResidues
