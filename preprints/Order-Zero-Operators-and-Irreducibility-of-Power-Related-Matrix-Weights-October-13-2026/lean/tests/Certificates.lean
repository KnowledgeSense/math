import PowerWeights

open PowerWeights

example {N : ℕ} (hN : 0<N) (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (B : PolynomialMatrix N) :
    InOrderZeroAlgebra H a B ↔
      ∃ c : ℂ, B=constant (c • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
  order_zero_algebra_eq_scalars hN s a ha H B

example (s : Schedule) (a : ℕ → ℝ) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight 1 s I w) :
    ¬ReducibleByConstantCongruence I (weight 1 s a w) :=
  not_reducible_by_constant_congruence (by omega) s a (by omega) H

example (a : ℕ → ℝ) (ha : a 0≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight 2 .printed I w) (B : PolynomialMatrix 2) :
    InOrderZeroAlgebra H a B ↔
      ∃ c : ℂ, B=constant (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  order_zero_algebra_eq_scalars (by omega) .printed a
    (by
      intro i hi
      have hi0 : i=0 := by omega
      simpa only [hi0] using ha) H B

example (n N : ℕ) (s : Schedule) (a : ℕ → ℝ) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (m : ℕ) (hm : m<n) :
    moment I w ((orthogonalSequence H a).Q n*polynomialWeight N s a) m=0 :=
  (orthogonalSequence H a).orthogonal n m hm
