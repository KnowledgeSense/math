import SphericalTreeFailures.LatticeInversion
import SphericalTreeFailures.HardCoreWeights

set_option backward.isDefEq.respectTransparency false

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

 theorem pmf_map_toReal_sum {V : Type*} [Fintype V] (P : PMF V) (N : V → ℤ) (j : ℤ) :
    (P.map N j).toReal = ∑ v, if N v = j then (P v).toReal else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · apply sum_congr rfl
    intro v _
    by_cases h : N v = j <;> simp [h, Ne.symm]
  · intro v _
    split_ifs <;> simp [P.apply_ne_top]

noncomputable def graphLatticeMass (m k : ℕ) (activity : ℝ) (ha : 0 < activity) (j : ℤ) : ℝ :=
  (((hardCore (sphericalTree m (2 * k + 1)).graph activity ha).map
    (fun s => (s.val.card : ℤ))) j).toReal

theorem graphLatticeMass_nat (m k j : ℕ) (activity : ℝ) (ha : 0 < activity) :
    graphLatticeMass m k activity ha j = sizeProbability m (2 * k + 1) j activity := by
  unfold graphLatticeMass
  have he : ((hardCore (sphericalTree m (2 * k + 1)).graph activity ha).map
      (fun s => (s.val.card : ℤ))) (j : ℤ) =
      ((hardCore (sphericalTree m (2 * k + 1)).graph activity ha).map (fun s => s.val.card)) j := by
    rw [PMF.map_apply, PMF.map_apply]
    simp only [Nat.cast_inj]
    apply tsum_congr
    intro s
    split_ifs <;> rfl
  have hz := configurationPartition_pos (sphericalTree m (2 * k + 1)).graph ha
  rw [he, hardCore_size_probability, ENNReal.toReal_ofReal (by positivity),
    configurationPartition_polynomial]
  rfl

theorem graphLatticeMass_neg (m k : ℕ) (activity : ℝ) (ha : 0 < activity)
    {j : ℤ} (hj : j < 0) : graphLatticeMass m k activity ha j = 0 := by
  unfold graphLatticeMass
  rw [pmf_map_toReal_sum]
  apply sum_eq_zero
  intro s _
  rw [ite_eq_right (by have := Int.natCast_nonneg s.val.card; omega)]

theorem graphLatticeMass_inversion (m k : ℕ) (activity : ℝ) (ha : 0 < activity) (j : ℤ) :
    (∫ t : ℝ in -Real.pi..Real.pi,
      sizeExponential (-j : ℝ) t * totalCharacteristic m k activity t) =
        ((2 * Real.pi : ℝ) : ℂ) * (graphLatticeMass m k activity ha j : ℂ) := by
  let P := hardCore (sphericalTree m (2 * k + 1)).graph activity ha
  have he (t : ℝ) : totalCharacteristic m k activity t =
      ∑ s, ((P s).toReal : ℂ) * sizeExponential (s.val.card : ℝ) t := by
    rw [totalCharacteristic_graph, ← hardCore_characteristic _ activity ha t, PMF.integral_eq_sum]
    apply sum_congr rfl
    intro s _
    simp only [sizeExponential, Complex.ofReal_natCast, Complex.real_smul]
    rfl
  simp_rw [he]
  have h := finite_fourier_inversion (fun s => (P s).toReal) (fun s => (s.val.card : ℤ)) j
  rw [show graphLatticeMass m k activity ha j = (P.map (fun s => (s.val.card : ℤ)) j).toReal from rfl,
    pmf_map_toReal_sum]
  have hc (s) : ((if (s.val.card : ℤ) = j then (P s).toReal else 0 : ℝ) : ℂ) =
      if (s.val.card : ℤ) = j then ((P s).toReal : ℂ) else 0 := by split_ifs <;> rfl
  push_cast
  simp_rw [hc]
  simpa only [Int.cast_natCast, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

end SphericalTreeFailures
