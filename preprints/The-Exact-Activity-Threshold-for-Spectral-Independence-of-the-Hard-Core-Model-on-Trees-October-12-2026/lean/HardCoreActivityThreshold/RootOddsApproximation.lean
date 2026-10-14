import HardCoreActivityThreshold.RootOddsConstruction

/-! Root-odds approximation by actual finite trees, using mixed-child brackets. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

structure OddsBracket (a omega : ℝ) where
  lower : ForestExpr
  upper : ForestExpr
  lower_le : rootOdds lower a ≤ omega
  upper_ge : omega ≤ rootOdds upper a

noncomputable def OddsBracket.error {a omega : ℝ} (B : OddsBracket a omega) : ℝ :=
  rootOdds B.upper a / rootOdds B.lower a - 1

theorem OddsBracket.error_nonneg {a omega : ℝ} (ha : 0 < a) (B : OddsBracket a omega) :
    0 ≤ B.error :=
  sub_nonneg.mpr ((one_le_div (rootOdds_pos B.lower ha)).mpr (B.lower_le.trans B.upper_ge))

@[simp] theorem rootOdds_empty (a : ℝ) : rootOdds .empty a = a := by
  simp [rootOdds, forestTotal, forestAvoid, ForestExpr.polynomials]

theorem activity_ge_fixedpoint {a omega : ℝ} (hw : 0 < omega) (b : ℕ)
    (hfix : a = omega * (1+omega)^b) : omega ≤ a := by
  rw [hfix]
  have hp : 1 ≤ (1+omega)^b := one_le_pow₀ (by linarith)
  nlinarith

noncomputable def initialOddsBracket {a omega : ℝ} (ha : 0 < a) (hw : 0 < omega)
    (b : ℕ) (hfix : a = omega * (1+omega)^b) : OddsBracket a omega where
  lower := mixedChildren .empty .empty b b
  upper := .empty
  lower_le := by
    rw [rootOdds_mixedChildren .empty .empty ha, rootOdds_empty]
    exact mixedOdds_last ha ha.le hw (activity_ge_fixedpoint hw b hfix) b hfix
  upper_ge := by simpa using activity_ge_fixedpoint hw b hfix

/-- A finite list crossing a level has a first adjacent crossing. -/
theorem first_adjacent_crossing (f : ℕ → ℝ) (omega : ℝ) (b : ℕ)
    (hfirst : omega < f 0) (hlast : f b ≤ omega) :
    ∃ k < b, omega < f k ∧ f (k+1) ≤ omega := by
  let hex : ∃ n, f n ≤ omega := ⟨b, hlast⟩
  let j := Nat.find hex
  have hj : f j ≤ omega := Nat.find_spec hex
  have hjb : j ≤ b := Nat.find_min' hex hlast
  have hjpos : 0 < j := by
    by_contra! h
    have hj0 : j = 0 := by omega
    rw [hj0] at hj
    linarith
  refine ⟨j-1, by omega, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (by omega))
  · have he : j-1+1 = j := by omega
    rwa [he]

/-- Every bracket is replaced by another made from finite mixed-child trees,
with a uniform geometric improvement of its relative width. -/
theorem improveOddsBracket {a omega : ℝ} (ha : 0 < a) (hw : 0 < omega)
    (b : ℕ) (hfix : a = omega * (1+omega)^b) (B : OddsBracket a omega) :
    ∃ B' : OddsBracket a omega, B'.error ≤ (a/(1+a)) * B.error := by
  let f : ℕ → ℝ := mixedOdds a (rootOdds B.lower a) (rootOdds B.upper a) b
  have hf0 : omega ≤ f 0 :=
    mixedOdds_first ha (rootOdds_pos B.lower ha).le hw B.lower_le b hfix
  have hfb : f b ≤ omega :=
    mixedOdds_last ha (rootOdds_pos B.upper ha).le hw B.upper_ge b hfix
  by_cases heq : f 0 = omega
  · let A := mixedChildren B.lower B.upper b 0
    have hA : rootOdds A a = omega := by
      rw [rootOdds_mixedChildren B.lower B.upper ha]
      exact heq
    refine ⟨⟨A, A, hA.le, hA.ge⟩, ?_⟩
    change rootOdds A a / rootOdds A a - 1 ≤ _
    rw [div_self (rootOdds_pos A ha).ne', sub_self]
    exact mul_nonneg (by positivity) (B.error_nonneg ha)
  · obtain ⟨k, hk, hkup, hklo⟩ := first_adjacent_crossing f omega b (lt_of_le_of_ne hf0 (Ne.symm heq)) hfb
    let L := mixedChildren B.lower B.upper b (k+1)
    let U := mixedChildren B.lower B.upper b k
    have hl : rootOdds L a ≤ omega := by
      rw [rootOdds_mixedChildren B.lower B.upper ha]
      exact hklo
    have hu : omega ≤ rootOdds U a := by
      rw [rootOdds_mixedChildren B.lower B.upper ha]
      exact hkup.le
    refine ⟨⟨L, U, hl, hu⟩, ?_⟩
    change rootOdds U a / rootOdds L a - 1 ≤ _
    rw [rootOdds_mixedChildren B.lower B.upper ha, rootOdds_mixedChildren B.lower B.upper ha,
      mixedOdds_adjacent_ratio ha (rootOdds_pos B.lower ha) (rootOdds_pos B.upper ha) hk]
    exact odds_ratio_contraction ha (rootOdds_pos B.lower ha) (B.lower_le.trans B.upper_ge)
      (rootOdds_le_activity B.lower ha)

theorem oddsBracket_geometric {a omega : ℝ} (ha : 0 < a) (hw : 0 < omega)
    (b : ℕ) (hfix : a = omega * (1+omega)^b) (B₀ : OddsBracket a omega) (n : ℕ) :
    ∃ B : OddsBracket a omega, B.error ≤ (a/(1+a))^n * B₀.error := by
  induction n with
  | zero => exact ⟨B₀, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨B', hB'⟩ := improveOddsBracket ha hw b hfix B
    refine ⟨B', hB'.trans ?_⟩
    calc
      (a/(1+a)) * B.error ≤ (a/(1+a)) * ((a/(1+a))^n * B₀.error) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (a/(1+a))^(n+1) * B₀.error := by rw [pow_succ]; ring

theorem exists_narrow_oddsBracket {a omega : ℝ} (ha : 0 < a) (hw : 0 < omega)
    (b : ℕ) (hfix : a = omega * (1+omega)^b) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ B : OddsBracket a omega, B.error < epsilon := by
  let B₀ := initialOddsBracket ha hw b hfix
  have hq0 : 0 ≤ a/(1+a) := by positivity
  have hq1 : a/(1+a) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B₀.error
  simp only [zero_mul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const he).exists
  obtain ⟨B, hB⟩ := oddsBracket_geometric ha hw b hfix B₀ n
  exact ⟨B, hB.trans_lt hn⟩

/-- Approximation of the fixed-point odds by genuine finite constant-activity trees. -/
theorem exists_rootOdds_approximation {a omega : ℝ} (ha : 0 < a) (hw : 0 < omega)
    (b : ℕ) (hfix : a = omega * (1+omega)^b) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ A : ForestExpr, |rootOdds A a - omega| < epsilon := by
  obtain ⟨B, hB⟩ := exists_narrow_oddsBracket ha hw b hfix (div_pos he ha)
  refine ⟨B.upper, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr B.upper_ge)]
  have hl := rootOdds_pos B.lower ha
  have hu := rootOdds_pos B.upper ha
  have heq : rootOdds B.upper a - rootOdds B.lower a = rootOdds B.lower a * B.error := by
    unfold OddsBracket.error
    field_simp
  calc
    rootOdds B.upper a - omega ≤ rootOdds B.upper a - rootOdds B.lower a := by linarith [B.lower_le]
    _ = rootOdds B.lower a * B.error := heq
    _ ≤ a * B.error := mul_le_mul_of_nonneg_right (rootOdds_le_activity B.lower ha) (B.error_nonneg ha)
    _ < a * (epsilon/a) := mul_lt_mul_of_pos_left hB ha
    _ = epsilon := mul_div_cancel₀ _ ha.ne'

end HardCoreActivityThreshold
