import HonestEmbeddingDimension.MontgomeryArithmetic
import HonestEmbeddingDimension.BinomialRealization
import HonestEmbeddingDimension.LowDegreeJets

namespace HonestEmbeddingDimension

/-- Montgomery's exceptional binomial coordinate; the other coordinates stay monomial. -/
noncomputable def montgomeryAux (w : Fin 3 → ℕ) (δ : ℕ) (s : Fin 3) : Fin 3 → PowerSeries ℂ :=
  fun i => if i = s then binomialCoordinate (w i) δ else PowerSeries.X ^ (w i)

theorem order_montgomeryAux (w : Fin 3 → ℕ) (δ : ℕ) (s i : Fin 3) (hδ : 0 < δ) :
    (montgomeryAux w δ s i).order = w i := by
  by_cases hi : i = s
  · simp only [montgomeryAux, ite_eq_left hi, order_binomialCoordinate _ _ hδ]
  · simp [montgomeryAux, hi, PowerSeries.order_pow, nsmul_eq_mul]

theorem formalJet_add_high {N : ℕ} (f g : PowerSeries ℂ) (hg : (N : ℕ∞) ≤ g.order) :
    formalJet N (f + g) = formalJet N f := by
  ext i
  have hcoeff := PowerSeries.coeff_of_lt_order (φ := g) i.val
    (lt_of_lt_of_le (by exact_mod_cast i.isLt) hg)
  simp [formalJet, hcoeff]

/-- A shifted binomial error is invisible after the certified cutoff. -/
theorem montgomery_unit_jet (n δ N : ℕ) (hcut : N ≤ n + δ) :
    formalJet N (PowerSeries.X ^ n * (1 + PowerSeries.X ^ δ)) =
      formalJet N (PowerSeries.X ^ n) := by
  rw [mul_add, mul_one, ← pow_add]
  apply formalJet_add_high
  simpa [PowerSeries.order_pow, nsmul_eq_mul] using (show (N : ℕ∞) ≤ (n + δ : ℕ) by exact_mod_cast hcut)

/-- A parameter shift of any coordinate agrees with its leading monomial past the cutoff. -/
theorem montgomery_shifted_jet (w : Fin 3 → ℕ) (δ N k : ℕ) (s i : Fin 3)
    (hcut : N ≤ k + w i + δ) :
    formalJet N (PowerSeries.X ^ k * montgomeryAux w δ s i) =
      formalJet N (PowerSeries.X ^ (k + w i)) := by
  by_cases hi : i = s
  · simp only [montgomeryAux, ite_eq_left hi, binomialCoordinate]
    rw [← mul_assoc, ← pow_add]
    exact montgomery_unit_jet _ _ _ hcut
  · simp [montgomeryAux, hi, ← pow_add]

/-- Products of two nonparameter coordinates have only their monomial jet below the cutoff. -/
theorem montgomery_product_jet (w : Fin 3 → ℕ) (δ N : ℕ) (s i j : Fin 3)
    (hcut : N ≤ w i + w j + δ) :
    formalJet N (montgomeryAux w δ s i * montgomeryAux w δ s j) =
      formalJet N (PowerSeries.X ^ (w i + w j)) := by
  have hmono : formalJet N (montgomeryAux w δ s i * PowerSeries.X ^ (w j)) =
      formalJet N (PowerSeries.X ^ (w i + w j)) := by
    simpa [mul_comm, Nat.add_comm] using montgomery_shifted_jet w δ N (w j) s i (by omega)
  by_cases hj : j = s
  · have hjval : montgomeryAux w δ s j = PowerSeries.X ^ (w j) * (1 + PowerSeries.X ^ δ) := by
      simp [montgomeryAux, hj, binomialCoordinate]
    rw [hjval, ← mul_assoc]
    exact (formalJet_mul hmono rfl).trans (montgomery_unit_jet _ _ _ hcut)
  · simpa only [montgomeryAux, ite_eq_right hj] using hmono

/-- Every high enough semigroup monomial reduces to the four-element parameter basis. -/
theorem montgomery_monomial_in_span (S : AddSubmonoid ℕ) (w : Fin 3 → ℕ)
    (a δ d : ℕ) (s : Fin 3) (hd : 2 * a + δ = d)
    (hreduce : ∀ n ∈ S, n < d → ∃ j : Fin 4, ∃ q : ℕ, n = 5 * q + (Fin.cons (α := fun _ => ℕ) 0 w) j)
    {n : ℕ} (hn : n ∈ S) (hna : 2 * a ≤ n) :
    InParameterJetSpan 5 (by omega) (linearParameterBasis (montgomeryAux w δ s)) d
      (PowerSeries.X ^ n) := by
  let B := linearParameterBasis (montgomeryAux w δ s)
  by_cases hnd : n < d
  · obtain ⟨j, q, hrepr⟩ := hreduce n hn hnd
    have hp := (parameterJetSpan_basis (N := d) (by omega : 5 ≠ 0) B j).parameter_mul
      (PowerSeries.X ^ q)
    have hp' : InParameterJetSpan 5 (by omega) B d (PowerSeries.X ^ (5 * q) * B j) := by
      simpa [← pow_mul, Nat.mul_comm] using hp
    apply hp'.congr
    have hshift : formalJet d (PowerSeries.X ^ (5 * q) * B j) = formalJet d (PowerSeries.X ^ n) := by
      cases j using Fin.cases with
      | zero => simpa [B, linearParameterBasis] using congrArg (fun k : ℕ => formalJet d (PowerSeries.X ^ k)) hrepr.symm
      | succ i =>
        change n = 5 * q + w i at hrepr
        rw [hrepr]
        exact montgomery_shifted_jet w δ d (5 * q) s i (by omega)
    exact hshift.symm
  · apply parameterJetSpan_of_order_ge
    simp only [PowerSeries.order_pow, PowerSeries.order_X, nsmul_eq_mul, mul_one]
    exact_mod_cast (show d ≤ n by omega)

/-- The finite multiplication certificate for Montgomery's actual four-coordinate construction. -/
theorem montgomery_basis_multiplication (S : AddSubmonoid ℕ) (w : Fin 3 → ℕ)
    (a δ d : ℕ) (s : Fin 3) (hd : 2 * a + δ = d)
    (hw : ∀ i, a ≤ w i) (hwS : ∀ i, w i ∈ S)
    (hreduce : ∀ n ∈ S, n < d → ∃ j : Fin 4, ∃ q : ℕ, n = 5 * q + (Fin.cons (α := fun _ => ℕ) 0 w) j) :
    ∀ i j, InParameterJetSpan 5 (by omega) (linearParameterBasis (montgomeryAux w δ s)) d
      (linearParameterBasis (montgomeryAux w δ s) j * parameterCoordinates 5 (montgomeryAux w δ s) i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    have hh := (parameterJetSpan_basis (N := d) (by omega : 5 ≠ 0)
      (linearParameterBasis (montgomeryAux w δ s)) j).parameter_mul PowerSeries.X
    simpa [parameterCoordinates, mul_comm] using hh
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [linearParameterBasis, parameterCoordinates] using
        parameterJetSpan_basis (N := d) (by omega : 5 ≠ 0)
          (linearParameterBasis (montgomeryAux w δ s)) i.succ
    · have hsum : 2 * a ≤ w j + w i := by have := hw i; have := hw j; omega
      apply (montgomery_monomial_in_span S w a δ d s hd hreduce
        (S.add_mem (hwS j) (hwS i)) hsum).congr
      exact montgomery_product_jet w δ d s j i (by omega)

end HonestEmbeddingDimension
