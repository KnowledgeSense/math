import ArithmeticSections.CylinderSemantics

namespace ArithmeticSections
open MeasureTheory Set Function
open scoped BigOperators ENNReal

abbrev CFWord (m : ℕ) := Fin m → ℕ+

def wordDigits {m : ℕ} (w : CFWord m) (k : ℕ) : ℕ :=
  if h : k - 1 < m then (w ⟨k - 1, h⟩ : ℕ) else 1

theorem wordDigits_pos {m : ℕ} (w : CFWord m) (k : ℕ) : 1 ≤ wordDigits w (k + 1) := by
  unfold wordDigits
  split
  · exact (w _).pos
  · exact le_rfl

@[simp] theorem wordDigits_at {m : ℕ} (w : CFWord m) (i : Fin m) :
    wordDigits w (i.val + 1) = (w i : ℕ) := by
  simp [wordDigits]

noncomputable def actualWord {θ : ℝ} (hθ : Irrational θ) (m : ℕ) : CFWord m :=
  fun i => ⟨actualDigit θ (i.val + 1), one_le_actualDigit_succ hθ i.val⟩

theorem actualWord_prefix {θ : ℝ} (hθ : Irrational θ) {m k : ℕ}
    (hk : 1 ≤ k) (hkm : k ≤ m) : wordDigits (actualWord hθ m) k = actualDigit θ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change wordDigits (actualWord hθ m) (j + 1) = _
  simpa [actualWord] using wordDigits_at (actualWord hθ m) (⟨j, by omega⟩ : Fin m)

abbrev RefiningWord (b : ℕ → ℕ) (L m : ℕ) :=
  {w : CFWord m // ∀ k, 1 ≤ k → k ≤ L → wordDigits w k = b k}

theorem digitCylinder_refining_disjoint (b : ℕ → ℕ) (L m : ℕ) :
    Pairwise (Disjoint on (fun w : RefiningWord b L m => digitCylinder (wordDigits w.val) m)) := by
  intro w v hne
  apply Set.disjoint_left.mpr
  intro θ hw hv
  apply hne
  apply Subtype.ext
  funext i
  apply PNat.coe_injective
  have hw' := hw.2.2 (i.val + 1) (by omega) (by omega)
  have hv' := hv.2.2 (i.val + 1) (by omega) (by omega)
  simpa only [wordDigits_at] using hw'.symm.trans hv'

theorem digitCylinder_refining_union (b : ℕ → ℕ) {L m : ℕ} (hLm : L ≤ m) :
    (⋃ w : RefiningWord b L m, digitCylinder (wordDigits w.val) m) = digitCylinder b L := by
  ext θ
  constructor
  · intro hθ
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hθ
    refine ⟨hw.1, hw.2.1, ?_⟩
    intro k hk hkL
    exact (hw.2.2 k hk (hkL.trans hLm)).trans (w.property k hk hkL)
  · intro hθ
    let w : RefiningWord b L m := ⟨actualWord hθ.1 m, fun k hk hkL =>
      (actualWord_prefix hθ.1 hk (hkL.trans hLm)).trans (hθ.2.2 k hk hkL)⟩
    refine Set.mem_iUnion.mpr ⟨w, hθ.1, hθ.2.1, ?_⟩
    intro k hk hkm
    exact (actualWord_prefix hθ.1 hk hkm).symm

/-- Summing the conditional next-digit estimate over every deeper prefix. -/
theorem volume_digitCylinder_exclusion_le (b : ℕ → ℕ) {L l : ℕ}
    (hLl : L < l) (hl : 2 ≤ l) (a : ℕ) :
    volume {θ ∈ digitCylinder b L | a < actualDigit θ l} ≤
      ENNReal.ofReal (2 / ((a : ℝ) + 1)) * volume (digitCylinder b L) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 2 := ⟨l - 2, by omega⟩
  let W := RefiningWord b L (n + 1)
  let C : W → Set ℝ := fun w => digitCylinder (wordDigits w.val) (n + 1)
  have hUnion : (⋃ w, C w) = digitCylinder b L := digitCylinder_refining_union b (by omega)
  have hBadUnion : (⋃ w, {θ ∈ C w | a < actualDigit θ (n + 2)}) =
      {θ ∈ digitCylinder b L | a < actualDigit θ (n + 2)} := by
    rw [← hUnion]
    ext θ
    simp only [mem_iUnion, mem_ofPred_eq]
    aesop
  rw [← hBadUnion]
  calc
    volume (⋃ w, {θ ∈ C w | a < actualDigit θ (n + 2)}) ≤
        ∑' w, volume {θ ∈ C w | a < actualDigit θ (n + 2)} := measure_iUnion_le _
    _ ≤ ∑' w, ENNReal.ofReal (2 / ((a : ℝ) + 1)) * volume (C w) := by
      apply ENNReal.tsum_le_tsum
      intro w
      exact volume_digitCylinder_next_exclusion_le (wordDigits_pos w.val) n a
    _ = ENNReal.ofReal (2 / ((a : ℝ) + 1)) * ∑' w, volume (C w) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 / ((a : ℝ) + 1)) * volume (digitCylinder b L) := by
      congr 1
      rw [← measure_iUnion (digitCylinder_refining_disjoint b L (n + 1))
        (fun w => measurableSet_digitCylinder (wordDigits w.val) (n + 1)), hUnion]

lemma quadratic_tail_term_le (x : ℝ) (hx : 0 < x) :
    2 / ((x + 1) ^ 2 + 1) ≤ 2 / x - 2 / (x + 1) := by
  calc
    2 / ((x + 1) ^ 2 + 1) ≤ 2 / (x * (x + 1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ = 2 / x - 2 / (x + 1) := by field_simp; ring

lemma quadratic_tail_sum_le {L : ℕ} (hL : 1 ≤ L) (N : ℕ) :
    (∑ i ∈ Finset.range N, (2 : ℝ) / (((L : ℝ) + i + 1) ^ 2 + 1)) ≤
      2 / L - 2 / ((L : ℝ) + N) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have ht := quadratic_tail_term_le ((L : ℝ) + N) (by positivity)
    push_cast
    simp only [← add_assoc]
    linarith

lemma quadratic_tail_tsum_le {L : ℕ} (hL : 1 ≤ L) :
    (∑' i : ℕ, ENNReal.ofReal (2 / (((L : ℝ) + i + 1) ^ 2 + 1))) ≤
      ENNReal.ofReal (2 / (L : ℝ)) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact (quadratic_tail_sum_le hL N).trans (sub_le_self _ (by positivity))

/-- The complete countable union of forbidden actual digits loses at most 2/L of a cylinder. -/
theorem volume_digitCylinder_bad_tail_le (b : ℕ → ℕ) {L : ℕ} (hL : 1 ≤ L) :
    volume (digitCylinder b L \ boundedTailCylinder b L) ≤
      ENNReal.ofReal (2 / (L : ℝ)) * volume (digitCylinder b L) := by
  have hbad : digitCylinder b L \ boundedTailCylinder b L =
      ⋃ i : ℕ, {θ ∈ digitCylinder b L | (L + i + 1) ^ 2 < actualDigit θ (L + i + 1)} := by
    ext θ
    simp only [mem_sdiff, boundedTailCylinder, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hc, ht⟩
      obtain ⟨l, hl, hd⟩ : ∃ l, L < l ∧ l ^ 2 < actualDigit θ l := by
        have hn : ¬ ∀ l, L < l → actualDigit θ l ≤ l ^ 2 := fun h => ht ⟨hc, h⟩
        push Not at hn
        exact hn
      refine ⟨l - L - 1, hc, ?_⟩
      have he : L + (l - L - 1) + 1 = l := by omega
      simpa only [he] using hd
    · rintro ⟨i, hc, hd⟩
      exact ⟨hc, fun ht => (not_lt_of_ge (ht.2 (L + i + 1) (by omega))) hd⟩
  rw [hbad]
  calc
    volume (⋃ i : ℕ, {θ ∈ digitCylinder b L | (L + i + 1) ^ 2 < actualDigit θ (L + i + 1)}) ≤
      ∑' i : ℕ, volume {θ ∈ digitCylinder b L | (L + i + 1) ^ 2 < actualDigit θ (L + i + 1)} :=
        measure_iUnion_le _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (2 / (((L : ℝ) + i + 1) ^ 2 + 1)) *
        volume (digitCylinder b L) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have h := volume_digitCylinder_exclusion_le b (show L < L + i + 1 by omega)
        (show 2 ≤ L + i + 1 by omega) ((L + i + 1) ^ 2)
      convert h using 1
      push_cast
      rfl
    _ = (∑' i : ℕ, ENNReal.ofReal (2 / (((L : ℝ) + i + 1) ^ 2 + 1))) *
        volume (digitCylinder b L) := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (2 / (L : ℝ)) * volume (digitCylinder b L) :=
      mul_le_mul' (quadratic_tail_tsum_le hL) le_rfl

theorem volume_digitCylinder_lt_top (b : ℕ → ℕ) (L : ℕ) :
    volume (digitCylinder b L) < ∞ := by
  exact lt_of_le_of_lt (measure_mono (show digitCylinder b L ⊆ Ioo (0 : ℝ) 1 from
    fun _ h => h.2.1)) (by simp)

theorem volume_digitCylinder_pos {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    {L : ℕ} (hL : 1 ≤ L) : 0 < volume (digitCylinder b L) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  rw [digitCylinder_eq_cylinderInterval hb n]
  exact volume_cylinderInterval_pos hb n

/-- The relative measure lower bound in Lemma 5.1, for actual continued-fraction digits. -/
theorem volume_boundedTailCylinder_ge (b : ℕ → ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ENNReal.ofReal (1 - 2 / (L : ℝ)) * volume (digitCylinder b L) ≤
      volume (boundedTailCylinder b L) := by
  have hs : boundedTailCylinder b L ⊆ digitCylinder b L := fun _ h => h.1
  have hid : digitCylinder b L \ (digitCylinder b L \ boundedTailCylinder b L) =
      boundedTailCylinder b L := by
    ext θ
    constructor
    · rintro ⟨hc, hn⟩
      by_contra ht
      exact hn ⟨hc, ht⟩
    · intro ht
      exact ⟨hs ht, fun hn => hn.2 ht⟩
  have he := (le_measure_sdiff (μ := volume)
    (s₁ := digitCylinder b L) (s₂ := digitCylinder b L \ boundedTailCylinder b L))
  rw [hid] at he
  have hlower := (tsub_le_tsub_left (volume_digitCylinder_bad_tail_le b hL)
    (volume (digitCylinder b L))).trans he
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
    ENNReal.sub_mul (fun _ _ => (volume_digitCylinder_lt_top b L).ne), one_mul]
  exact hlower

theorem volume_boundedTailCylinder_pos {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
    {L : ℕ} (hL : 3 ≤ L) : 0 < volume (boundedTailCylinder b L) := by
  have hL' : (2 : ℝ) < L := by exact_mod_cast (show 2 < L by omega)
  apply lt_of_lt_of_le _ (volume_boundedTailCylinder_ge b (by omega))
  apply ENNReal.mul_pos_iff.mpr
  constructor
  · rw [ENNReal.ofReal_pos]
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hL')
  · exact volume_digitCylinder_pos hb (by omega)

end ArithmeticSections
