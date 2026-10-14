import MainTheorems.AHOConstants.CounterexampleMatrices
import MainTheorems.AHOConstants.ActiveCompression
import MainTheorems.AHOConstants.RealMatrixProducts

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable def activeEigenvector (z : ℝ) (large : Bool) (i : Fin 2) : ℝ :=
  if large then largeEigenvector z (activeCoordinate i) else smallEigenvector z (activeCoordinate i)

theorem activeEigenvector_positive {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1 / 8)
    (large : Bool) (i : Fin 2) : 0 < activeEigenvector z large i := by
  obtain ⟨hv₀, hv₂, hu₀, hu₂⟩ := active_overlaps_positive hz hz'
  cases large <;> fin_cases i <;> simp [activeEigenvector, activeCoordinate] <;> linarith

theorem activeEigenvector_lower {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1 / 8)
    (large : Bool) (i : Fin 2) :
    (1 / 4 : ℝ) * (if large = true ∧ i = 1 then z else 1) ≤ activeEigenvector z large i := by
  obtain ⟨hv₀, hv₂, hu₀, hu₂⟩ := active_overlaps_positive hz hz'
  cases large <;> fin_cases i <;> simp [activeEigenvector, activeCoordinate] <;> linarith

theorem counterexampleA_entry {ε p : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) (hp : 0 < p)
    (z : ℝ) (i j : Fin 3) :
    spectralPower (counterexampleA ε z) p i j =
      ((ε ^ p * smallEigenvector z i * smallEigenvector z j +
        largeEigenvector z i * largeEigenvector z j : ℝ) : ℂ) := by
  rw [counterexampleA_power hε₀ hε₁ hp]
  apply Complex.ext <;> simp [realProjection, rankOne, realVector,
    Complex.mul_re, Complex.mul_im]
  ring

theorem counterexampleB_power_diagonal {ε q : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hq : 0 < q) :
    spectralPower (counterexampleB ε) q = Matrix.diagonal (fun j : Fin 3 =>
      if j = 0 then ((ε ^ q : ℝ) : ℂ) else if j = 2 then 1 else 0) := by
  rw [counterexampleB_power hε₀ hε₁ hq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realProjection, rankOne, realVector, coordinateVector]

noncomputable def counterexampleActivePair (ε z p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    (ε ^ p * activeEigenvector z false i * activeEigenvector z false j +
      activeEigenvector z true i * activeEigenvector z true j) *
      (if j = 0 then ε ^ q else 1)

theorem counterexample_pair_middleColumnZero {ε p q : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hq : 0 < q) (z : ℝ) :
    MiddleColumnZero (spectralPower (counterexampleA ε z) p * spectralPower (counterexampleB ε) q) := by
  intro i
  rw [counterexampleB_power_diagonal hε₀ hε₁ hq, Matrix.mul_diagonal]
  simp

theorem counterexample_pair_compression {ε p q : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hp : 0 < p) (hq : 0 < q) (z : ℝ) :
    activeCompression (spectralPower (counterexampleA ε z) p * spectralPower (counterexampleB ε) q) =
      realCastMatrix (counterexampleActivePair ε z p q) := by
  rw [counterexampleB_power_diagonal hε₀ hε₁ hq]
  ext i j
  fin_cases j <;>
    simp [activeCompression, activeCoordinate, Matrix.mul_diagonal,
      counterexampleA_entry hε₀ hε₁ hp, realCastMatrix, counterexampleActivePair,
      activeEigenvector, Complex.ofReal_mul, Complex.ofReal_add]

theorem counterexampleActivePair_nonnegative {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) (hz' : z ≤ 1 / 8) (p q : ℝ) :
    EntryNonnegative (counterexampleActivePair ε z p q) := by
  intro i j
  have hp := (Real.rpow_pos_of_pos hε p).le
  have hq := (Real.rpow_pos_of_pos hε q).le
  have hvi := (activeEigenvector_positive hz hz' false i).le
  have hvj := (activeEigenvector_positive hz hz' false j).le
  have hui := (activeEigenvector_positive hz hz' true i).le
  have huj := (activeEigenvector_positive hz hz' true j).le
  have hc : 0 ≤ (if j = 0 then ε ^ q else 1) := by split_ifs <;> positivity
  exact mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hp hvi) hvj) (mul_nonneg hui huj)) hc

theorem counterexample_paired_product_trace {m : ℕ} {ε : ℝ} (hε₀ : 0 < ε)
    (hε₁ : ε < 1) (z : ℝ) (p q : Fin (m + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    Matrix.trace (List.ofFn (fun i => spectralPower (counterexampleA ε z) (p i) *
      spectralPower (counterexampleB ε) (q i))).prod =
      ((Matrix.trace (List.ofFn (fun i => counterexampleActivePair ε z (p i) (q i))).prod : ℝ) : ℂ) := by
  let xs := List.ofFn (fun i => spectralPower (counterexampleA ε z) (p i) *
    spectralPower (counterexampleB ε) (q i))
  let ys := List.ofFn (fun i => counterexampleActivePair ε z (p i) (q i))
  have hne : xs ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [xs, List.length_ofFn, List.length_nil] at hl
    omega
  have hcols : ∀ N ∈ xs, MiddleColumnZero N := by
    intro N hN
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hN
    exact counterexample_pair_middleColumnZero hε₀ hε₁ (hq i) z
  have hmaps : xs.map activeCompression = ys.map realCastMatrix := by
    simp only [xs, ys, ← List.ofFn_comp']
    apply congrArg List.ofFn
    funext i
    exact counterexample_pair_compression hε₀ hε₁ (hp i) (hq i) z
  have h := trace_activeCompression_product_nonempty xs hne hcols
  rw [hmaps, realCastMatrix_product, realCastMatrix_trace] at h
  exact h

theorem counterexample_paired_product_trace_norm {m : ℕ} {ε z : ℝ} (hε₀ : 0 < ε)
    (hε₁ : ε < 1) (hz : 0 < z) (hz' : z ≤ 1 / 8) (p q : Fin (m + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ‖Matrix.trace (List.ofFn (fun i => spectralPower (counterexampleA ε z) (p i) *
      spectralPower (counterexampleB ε) (q i))).prod‖ =
      Matrix.trace (List.ofFn (fun i => counterexampleActivePair ε z (p i) (q i))).prod := by
  rw [counterexample_paired_product_trace hε₀ hε₁ z p q hp hq, Complex.norm_real]
  apply Real.norm_of_nonneg
  apply EntryNonnegative.trace
  apply entryNonnegative_product
  intro M hM
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hM
  exact counterexampleActivePair_nonnegative hε₀ hz hz' (p i) (q i)

theorem counterexample_paired_trace_norm_eq_re {m : ℕ} {ε z : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hz : 0 < z) (hz' : z ≤ 1 / 8)
    (p q : Fin (m + 1) → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ‖Matrix.trace (List.ofFn (fun i => spectralPower (counterexampleA ε z) (p i) *
      spectralPower (counterexampleB ε) (q i))).prod‖ =
      (Matrix.trace (List.ofFn (fun i => spectralPower (counterexampleA ε z) (p i) *
        spectralPower (counterexampleB ε) (q i))).prod).re := by
  rw [counterexample_paired_product_trace_norm hε₀ hε₁ hz hz' p q hp hq,
    counterexample_paired_product_trace hε₀ hε₁ z p q hp hq, Complex.ofReal_re]

end ResearchMain.AHOConstants
