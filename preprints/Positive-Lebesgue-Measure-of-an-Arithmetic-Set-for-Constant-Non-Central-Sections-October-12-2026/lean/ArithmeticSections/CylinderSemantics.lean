import ArithmeticSections.CylinderIntervals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Order.IntermediateValue

namespace ArithmeticSections
open MeasureTheory Set

/-- The cylinder defined by the digits of the actual Gauss algorithm. -/
def digitCylinder (b : ℕ → ℕ) (L : ℕ) : Set ℝ :=
  {θ | Irrational θ ∧ θ ∈ Ioo (0 : ℝ) 1 ∧ ∀ k, 1 ≤ k → k ≤ L → actualDigit θ k = b k}

def boundedTailCylinder (b : ℕ → ℕ) (L : ℕ) : Set ℝ :=
  {θ ∈ digitCylinder b L | ∀ l, L < l → actualDigit θ l ≤ l ^ 2}

theorem measurable_completeQuotient (n : ℕ) : Measurable (fun θ => completeQuotient θ n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact ih.fract.inv

theorem measurable_actualDigit (n : ℕ) : Measurable (fun θ => actualDigit θ n) :=
  (measurable_of_countable (f := Int.toNat)).comp (measurable_completeQuotient n).floor

theorem measurableSet_digitCylinder (b : ℕ → ℕ) (L : ℕ) :
    MeasurableSet (digitCylinder b L) := by
  have hi : MeasurableSet {θ : ℝ | Irrational θ} :=
    (Set.countable_range (fun q : ℚ => (q : ℝ))).measurableSet.compl
  simp only [digitCylinder, Set.ofPred_and, Set.ofPred_forall]
  exact hi.inter (measurableSet_Ioo.inter (MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (measurable_actualDigit k) (measurableSet_singleton (b k))))

theorem measurableSet_boundedTailCylinder (b : ℕ → ℕ) (L : ℕ) :
    MeasurableSet (boundedTailCylinder b L) := by
  simp only [boundedTailCylinder, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_digitCylinder b L).inter (MeasurableSet.iInter fun l =>
    MeasurableSet.iInter fun _ => (measurable_actualDigit l) measurableSet_Iic)

theorem denominator_eq_of_prefix {b c : ℕ → ℕ} {L : ℕ}
    (h : ∀ k, 1 ≤ k → k ≤ L → b k = c k) {n : ℕ} (hn : n ≤ L) :
    denominator b n = denominator c n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simpa only [denominator] using h 1 (by omega) hn
  | more n h0 h1 =>
    simp only [denominator]
    rw [h (n + 2) (by omega) hn, h0 (by omega), h1 (by omega)]

theorem actualDenominator_eq_of_mem_digitCylinder {b : ℕ → ℕ} {L n : ℕ} {θ : ℝ}
    (hθ : θ ∈ digitCylinder b L) (hn : n ≤ L) :
    actualDenominator θ n = denominator b n :=
  denominator_eq_of_prefix hθ.2.2 hn

theorem cylinderMap_succ {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    cylinderMap b (n + 1) t = cylinderMap b n ((b (n + 2) : ℝ) + t)⁻¹ := by
  have ha : (0 : ℝ) < (b (n + 2) : ℝ) + t := by
    have hb' := hb (n + 1)
    have : (1 : ℝ) ≤ b (n + 2) := by exact_mod_cast hb'
    linarith
  unfold cylinderMap
  rw [numerator, denominator]
  push_cast
  field_simp
  ring

lemma inv_nat_add_mem_Ioo {a : ℕ} (ha : 1 ≤ a) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((a : ℝ) + t)⁻¹ ∈ Ioo (0 : ℝ) 1 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  exact ⟨inv_pos.mpr (by linarith [ht.1]), (inv_lt_one₀ (by linarith [ht.1])).mpr (by linarith [ht.1])⟩

lemma floor_nat_add_tail (a : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ⌊(a : ℝ) + t⌋ = (a : ℤ) := by
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith [ht.1, ht.2]

lemma fract_nat_add_tail (a : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Int.fract ((a : ℝ) + t) = t := by
  rw [Int.fract, floor_nat_add_tail a ht]
  push_cast
  ring

/-- The Möbius parametrization really has the prescribed Gauss digits and tail. -/
theorem cylinderMap_actual {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ)
    {t : ℝ} (hti : Irrational t) (ht : t ∈ Ioo (0 : ℝ) 1) :
    cylinderMap b n t ∈ digitCylinder b (n + 1) ∧
      Int.fract (completeQuotient (cylinderMap b n t) (n + 1)) = t := by
  induction n generalizing t with
  | zero =>
    have hmap : cylinderMap b 0 t = ((b 1 : ℝ) + t)⁻¹ := by
      simp [cylinderMap, numerator, denominator, one_div]
    have hx := inv_nat_add_mem_Ioo (hb 0) ht
    have hq : completeQuotient (((b 1 : ℝ) + t)⁻¹) 1 = (b 1 : ℝ) + t := by
      simp only [completeQuotient, Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩, inv_inv]
    rw [hmap]
    constructor
    · refine ⟨(hti.natCast_add _).inv, hx, ?_⟩
      intro k hk hk'
      have hk1 : k = 1 := by omega
      subst k
      simp only [actualDigit, hq, floor_nat_add_tail _ ht, Int.toNat_natCast]
    · rw [hq, fract_nat_add_tail _ ht]
  | succ n ih =>
    let u : ℝ := ((b (n + 2) : ℝ) + t)⁻¹
    have hui : Irrational u := (hti.natCast_add _).inv
    have hu : u ∈ Ioo (0 : ℝ) 1 := inv_nat_add_mem_Ioo (hb (n + 1)) ht
    obtain ⟨hx, htail⟩ := ih hui hu
    have hmap : cylinderMap b (n + 1) t = cylinderMap b n u := cylinderMap_succ hb n ht.1.le
    have hq : completeQuotient (cylinderMap b n u) (n + 2) = (b (n + 2) : ℝ) + t := by
      change (Int.fract (completeQuotient (cylinderMap b n u) (n + 1)))⁻¹ = _
      rw [htail, inv_inv]
    rw [hmap]
    constructor
    · refine ⟨hx.1, hx.2.1, ?_⟩
      intro k hk hk'
      by_cases hkn : k ≤ n + 1
      · exact hx.2.2 k hk hkn
      · have hk2 : k = n + 2 := by omega
        subst k
        simp only [actualDigit, hq, floor_nat_add_tail _ ht, Int.toNat_natCast]
    · exact (congrArg Int.fract hq).trans (fract_nat_add_tail _ ht)

theorem completeQuotient_fract_irrational {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    Irrational (Int.fract (completeQuotient θ n)) := by
  simpa only [Int.fract] using
    (completeQuotient_irrational hθ n).sub_intCast ⌊completeQuotient θ n⌋

theorem completeQuotient_eq_digit_add_fract {θ : ℝ} (hθ : Irrational θ) (n : ℕ) :
    completeQuotient θ (n + 1) =
      (actualDigit θ (n + 1) : ℝ) + Int.fract (completeQuotient θ (n + 1)) := by
  rw [actualDigit_cast hθ n, Int.fract]
  ring

/-- Recover the tail coordinate from any real with the prescribed actual digits. -/
theorem cylinderMap_recover {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ)
    {θ : ℝ} (hθ : θ ∈ digitCylinder b (n + 1)) :
    cylinderMap b n (Int.fract (completeQuotient θ (n + 1))) = θ := by
  induction n with
  | zero =>
    have hd := hθ.2.2 1 (by omega) (by omega)
    have hq := completeQuotient_eq_digit_add_fract hθ.1 0
    rw [hd] at hq
    have hq' : completeQuotient θ 1 = θ⁻¹ := by
      simp only [completeQuotient, Int.fract_eq_self.mpr ⟨hθ.2.1.1.le, hθ.2.1.2⟩]
    simp only [cylinderMap, numerator, denominator, Nat.cast_one, Nat.cast_zero,
      zero_mul, one_mul, add_zero, one_div]
    rw [← hq, hq', inv_inv]
  | succ n ih =>
    have hθ' : θ ∈ digitCylinder b (n + 1) :=
      ⟨hθ.1, hθ.2.1, fun k hk hk' => hθ.2.2 k hk (by omega)⟩
    have hq := completeQuotient_eq_digit_add_fract hθ.1 (n + 1)
    rw [hθ.2.2 (n + 2) (by omega) (by omega)] at hq
    rw [cylinderMap_succ hb n (Int.fract_nonneg _), ← hq]
    simpa only [completeQuotient, inv_inv] using ih hθ'

lemma cylinderMap_eq_rat_of_rat {b : ℕ → ℕ} (n : ℕ) {t : ℝ} (ht : ¬ Irrational t) :
    ¬ Irrational (cylinderMap b n t) := by
  obtain ⟨r, rfl⟩ := exists_rat_of_not_irrational ht
  intro hi
  apply hi
  refine ⟨((numerator b (n + 1) : ℚ) + numerator b n * r) /
    ((denominator b (n + 1) : ℚ) + denominator b n * r), ?_⟩
  push_cast
  rfl

theorem cylinderMap_strictMonoOn_or_strictAntiOn {b : ℕ → ℕ}
    (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    StrictMonoOn (cylinderMap b n) (Ici 0) ∨ StrictAntiOn (cylinderMap b n) (Ici 0) := by
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  rcases neg_one_pow_eq_or ℝ (n + 1) with he | he
  · left
    intro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    apply sub_pos.mp
    rw [cylinderMap_sub hb n hx hy, he, one_mul]
    exact div_pos (sub_pos.mpr hxy) (by positivity)
  · right
    intro x hx y hy hxy
    change 0 ≤ x at hx
    change 0 ≤ y at hy
    apply sub_neg.mp
    rw [cylinderMap_sub hb n hx hy, he, neg_one_mul]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hxy)) (by positivity)

theorem cylinderMap_injOn {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    InjOn (cylinderMap b n) (Ici 0) := by
  rcases cylinderMap_strictMonoOn_or_strictAntiOn hb n with h | h
  · exact h.injOn
  · exact h.injOn

theorem continuousOn_cylinderMap {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    ContinuousOn (cylinderMap b n) (Ici 0) := by
  have hq : (0 : ℝ) < denominator b (n + 1) := by exact_mod_cast denominator_pos hb (n + 1)
  apply ContinuousOn.div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
  intro t ht
  exact ne_of_gt (add_pos_of_pos_of_nonneg hq (mul_nonneg (by positivity) ht))

theorem cylinderMap_image_Ioo {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ)
    {z : ℝ} (hz : 0 < z) :
    cylinderMap b n '' Ioo 0 z = uIoo (cylinderMap b n 0) (cylinderMap b n z) := by
  have hsub : Icc (0 : ℝ) z ⊆ Ici 0 := fun _ hx => hx.1
  have hc := (continuousOn_cylinderMap hb n).mono hsub
  rcases cylinderMap_strictMonoOn_or_strictAntiOn hb n with hm | hm
  · rw [uIoo_of_lt (hm (by simp) (by exact hz.le) hz)]
    exact hc.image_Ioo_of_strictMonoOn hz.le (hm.mono hsub)
  · rw [uIoo_of_gt (hm (by simp) (by exact hz.le) hz)]
    exact hc.image_Ioo_of_strictAntiOn hz.le (hm.mono hsub)

theorem cylinderInterval_eq_image {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ)
    {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    cylinderInterval b n z = cylinderMap b n '' {t : ℝ | Irrational t ∧ t ∈ Ioo 0 z} := by
  ext θ
  constructor
  · intro hθ
    obtain ⟨t, ht, rfl⟩ := (cylinderMap_image_Ioo hb n hz).symm ▸ hθ.1
    refine ⟨t, ⟨?_, ht⟩, rfl⟩
    by_contra hti
    exact cylinderMap_eq_rat_of_rat n hti hθ.2
  · rintro ⟨t, ⟨hti, ht⟩, rfl⟩
    exact ⟨cylinderMap_image_Ioo hb n hz ▸ mem_image_of_mem _ ht,
      (cylinderMap_actual hb n hti ⟨ht.1, ht.2.trans_le hz1⟩).1.1⟩

/-- The interval cylinder and the prescribed actual-digit cylinder are identical. -/
theorem digitCylinder_eq_cylinderInterval {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) :
    digitCylinder b (n + 1) = cylinderInterval b n 1 := by
  rw [cylinderInterval_eq_image hb n (by norm_num) le_rfl]
  ext θ
  constructor
  · intro hθ
    exact ⟨Int.fract (completeQuotient θ (n + 1)),
      ⟨completeQuotient_fract_irrational hθ.1 _,
        completeQuotient_fract_pos hθ.1 _, Int.fract_lt_one _⟩,
      cylinderMap_recover hb n hθ⟩
  · rintro ⟨t, ⟨hti, ht⟩, rfl⟩
    exact (cylinderMap_actual hb n hti ht).1

theorem actualDigit_gt_iff_fract_lt {θ : ℝ} (hθ : Irrational θ) (n a : ℕ) :
    a < actualDigit θ (n + 1) ↔
      Int.fract (completeQuotient θ n) < 1 / ((a : ℝ) + 1) := by
  have hp := completeQuotient_fract_pos hθ n
  have hapos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hnrat : completeQuotient θ (n + 1) ≠ (a : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (completeQuotient_irrational hθ (n + 1)).ne_nat (a + 1)
  have hle : a < actualDigit θ (n + 1) ↔ (a : ℝ) + 1 ≤ completeQuotient θ (n + 1) := by
    rw [show (a : ℝ) + 1 = (((a : ℤ) + 1 : ℤ) : ℝ) by push_cast; rfl, ← Int.le_floor]
    unfold actualDigit
    omega
  rw [hle, le_iff_lt_or_eq]
  simp only [eq_comm (a := (a : ℝ) + 1), hnrat, or_false]
  change (a : ℝ) + 1 < (Int.fract (completeQuotient θ n))⁻¹ ↔ _
  rw [lt_inv_comm₀ hapos hp, one_div]

theorem cylinderInterval_eq_tail_restriction {b : ℕ → ℕ}
    (hb : ∀ n, 1 ≤ b (n + 1)) (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    cylinderInterval b n z =
      {θ ∈ digitCylinder b (n + 1) | Int.fract (completeQuotient θ (n + 1)) < z} := by
  rw [cylinderInterval_eq_image hb n hz hz1]
  ext θ
  constructor
  · rintro ⟨t, ⟨hti, ht⟩, rfl⟩
    obtain ⟨hc, htail⟩ := cylinderMap_actual hb n hti ⟨ht.1, ht.2.trans_le hz1⟩
    exact ⟨hc, by rw [htail]; exact ht.2⟩
  · rintro ⟨hc, htail⟩
    exact ⟨Int.fract (completeQuotient θ (n + 1)),
      ⟨completeQuotient_fract_irrational hc.1 _, completeQuotient_fract_pos hc.1 _, htail⟩,
      cylinderMap_recover hb n hc⟩

theorem digitCylinder_next_exclusion {b : ℕ → ℕ}
    (hb : ∀ n, 1 ≤ b (n + 1)) (n a : ℕ) :
    {θ ∈ digitCylinder b (n + 1) | a < actualDigit θ (n + 2)} =
      cylinderInterval b n (1 / ((a : ℝ) + 1)) := by
  rw [cylinderInterval_eq_tail_restriction hb n (by positivity)
    ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) a]))]
  ext θ
  constructor
  · rintro ⟨hθ, hd⟩
    exact ⟨hθ, (actualDigit_gt_iff_fract_lt hθ.1 (n + 1) a).mp hd⟩
  · rintro ⟨hθ, hd⟩
    exact ⟨hθ, (actualDigit_gt_iff_fract_lt hθ.1 (n + 1) a).mpr hd⟩

theorem volume_digitCylinder_next_exclusion_le {b : ℕ → ℕ}
    (hb : ∀ n, 1 ≤ b (n + 1)) (n a : ℕ) :
    volume {θ ∈ digitCylinder b (n + 1) | a < actualDigit θ (n + 2)} ≤
      ENNReal.ofReal (2 / ((a : ℝ) + 1)) * volume (digitCylinder b (n + 1)) := by
  rw [digitCylinder_next_exclusion hb n a, digitCylinder_eq_cylinderInterval hb n]
  simpa only [mul_one_div] using
    volume_cylinderInterval_le hb n (show (0 : ℝ) ≤ 1 / ((a : ℝ) + 1) by positivity)

end ArithmeticSections
