import MainTheorems.AHOConstants.FlowFactorization
import MainTheorems.AHOConstants.ZeroWeightFactors
import MainTheorems.AHOConstants.PowerTraceBound

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open ResearchMain.DiagonalSchatten

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def forwardFactor {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (r : ℝ) : SchattenFactor I where
  matrix := spectralPower A r * spectralPower B r
  weight := r
  invertible := (spectralPower_isUnit hA r).mul (spectralPower_isUnit hB r)

noncomputable def backwardFactor {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (r : ℝ) : SchattenFactor I where
  matrix := spectralPower B r * spectralPower A r
  weight := r
  invertible := (spectralPower_isUnit hB r).mul (spectralPower_isUnit hA r)

noncomputable def flowFactors {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (xs : List (ℝ × ℝ)) : List (SchattenFactor I) :=
  xs.flatMap (fun ab => [forwardFactor hA hB ab.1, backwardFactor hA hB ab.2])

theorem flowFactors_weight_sum {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (xs : List (ℝ × ℝ)) :
    ((flowFactors hA hB xs).map SchattenFactor.weight).sum =
      (xs.map (fun ab => ab.1 + ab.2)).sum := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
    simp only [flowFactors, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      forwardFactor, backwardFactor, add_zero]
    exact congrArg (fun x => ab.1 + ab.2 + x) ih

theorem flowFactors_product {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (xs : List (ℝ × ℝ)) :
    ((flowFactors hA hB xs).map SchattenFactor.matrix).prod = flowProduct A B xs := by
  induction xs with
  | nil => rfl
  | cons ab xs ih =>
    simp only [flowFactors, List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      forwardFactor, backwardFactor, Matrix.mul_one]
    change ((spectralPower A ab.1 * spectralPower B ab.1) *
      (spectralPower B ab.2 * spectralPower A ab.2)) *
      ((flowFactors hA hB xs).map SchattenFactor.matrix).prod =
      ((spectralPower A ab.1 * spectralPower B ab.1) *
      (spectralPower B ab.2 * spectralPower A ab.2)) * flowProduct A B xs
    rw [ih]

theorem reverse_small_product_bound [Nonempty I] {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {r : ℝ} (hr : 0 < r) (hrh : r ≤ 1 / 2) :
    schattenNorm (1 / r) (spectralPower B r * spectralPower A r) ≤
      (Matrix.trace (A * B)).re ^ r := by
  have he : (spectralPower A r * spectralPower B r).conjTranspose =
      spectralPower B r * spectralPower A r := by
    rw [Matrix.conjTranspose_mul]
    change star (spectralPower B r) * star (spectralPower A r) = _
    rw [(spectralPower_positiveSemidefinite B r).isHermitian.isSelfAdjoint.star_eq,
      (spectralPower_positiveSemidefinite A r).isHermitian.isSelfAdjoint.star_eq]
  rw [← he, schattenNorm_conjTranspose (one_div_pos.mpr hr)]
  exact schattenNorm_small_product hA hB hr hrh

theorem feasible_trace_bound [Nonempty I] {m : ℕ} {p q : Fin (m + 1) → ℝ}
    (hq : (∑ i, q i) = 1) (hfeas : Feasible p q)
    {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    ‖wordTrace A B (pairWord (List.ofFn (fun i => (p i, q i))))‖ ≤
      (Matrix.trace (A * B)).re := by
  obtain ⟨a, b, hab⟩ := hfeas
  let xs := List.ofFn (fun i => (a i, b i))
  let fs := flowFactors hA hB xs
  have hsum : (fs.map SchattenFactor.weight).sum = 1 := by
    rw [flowFactors_weight_sum]
    simpa only [xs, ← List.ofFn_comp', List.sum_ofFn] using hab.weight_sum hq
  have hcaps : ∀ f ∈ fs, 0 ≤ f.weight ∧ f.weight ≤ 1 / 2 := by
    intro f hf
    obtain ⟨ab, habm, hf⟩ := List.mem_flatMap.mp hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp habm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨(hab.1 i).1, (hab.1 i).2.1⟩
    · exact ⟨(hab.1 i).2.2.1, (hab.1 i).2.2.2⟩
  have hzero : ∀ f ∈ fs, f.weight = 0 → f.matrix = 1 := by
    intro f hf hw
    obtain ⟨ab, habm, hf⟩ := List.mem_flatMap.mp hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · change ab.1 = 0 at hw
      simp only [forwardFactor, hw, spectralPower_zero A hA.posSemidef,
        spectralPower_zero B hB.posSemidef, Matrix.one_mul]
    · change ab.2 = 0 at hw
      simp only [backwardFactor, hw, spectralPower_zero A hA.posSemidef,
        spectralPower_zero B hB.posSemidef, Matrix.one_mul]
  have hbound : ∀ f ∈ fs, 0 < f.weight →
      schattenNorm (1 / f.weight) f.matrix ≤ (Matrix.trace (A * B)).re ^ f.weight := by
    intro f hf hp
    have hc := (hcaps f hf).2
    obtain ⟨ab, habm, hf⟩ := List.mem_flatMap.mp hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact schattenNorm_small_product hA hB hp hc
    · exact reverse_small_product_bound hA hB hp hc
  have h := weighted_schatten_trace_bound (trace_product_positive hA hB) fs
    (fun f hf => (hcaps f hf).1) hsum hzero hbound
  rw [flowFactors_product] at h
  rw [circulation_trace_factorization hab hA hB]
  exact h

end ResearchMain.AHOConstants
