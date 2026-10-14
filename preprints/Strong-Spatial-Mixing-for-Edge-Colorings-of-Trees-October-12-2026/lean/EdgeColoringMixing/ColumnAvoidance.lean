import EdgeColoringMixing.PartitionBounds
import EdgeColoringMixing.ColumnBlocks

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- Forbid one color while keeping the original finite row and color types. -/
def withoutColor (W : Fin d → Fin q → ℝ) (c : Fin q) (i : Fin d) (b : Fin q) : ℝ :=
  if b = c then 0 else W i b

theorem weight_withoutColor (W : Fin d → Fin q → ℝ) (c : Fin q) (σ : Injection d q) :
    weight (withoutColor W c) σ = if c ∉ Set.range σ then weight W σ else 0 := by
  classical
  by_cases hc : c ∈ Set.range σ
  · simp only [hc, not_true_eq_false, ite_false]
    obtain ⟨i, hi⟩ := hc
    apply Finset.prod_eq_zero (mem_univ i)
    simp [withoutColor, hi]
  · rw [ite_eq_left hc]
    unfold weight
    apply Finset.prod_congr rfl
    intro i _
    have hi : σ i ≠ c := fun h => hc ⟨i,h⟩
    simp [withoutColor, hi]

theorem sum_withoutColor (w : Fin q → ℝ) (c : Fin q) :
    (∑ b, if b = c then 0 else w b) = (∑ b, w b) - w c := by
  classical
  calc
    _ = (∑ b, w b) - ∑ b, if b = c then w b else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b = c <;> simp [hb]
    _ = _ := by simp

/-- A quantitative partition bound using the full admissible row-mass range. -/
theorem partition_ge_power_of_mass (W : Fin d → Fin q → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hn : ∀ i c, 0 ≤ W i c) (h1 : ∀ i c, W i c ≤ 1)
    (hm : ∀ i, (d : ℝ) - 1 + t ≤ ∑ c, W i c) : t^d ≤ partition W := by
  induction d with
  | zero => simp [partition, weight]
  | succ d ih =>
    have htail : ∀ i : Fin d, (d : ℝ) - 1 + t ≤ ∑ c, W i.succ c := by
      intro i
      have h := hm i.succ
      push_cast at h
      linarith
    have hstep (τ : Injection d q) : t ≤
        ∑ c : {c : Fin q // c ∉ Set.range τ}, W 0 c := by
      have h := unused_mass_ge (W 0) (h1 0) τ
      have hrow := hm 0
      push_cast at hrow
      linarith
    rw [partition_succ]
    calc
      t^(d + 1) = t * t^d := by ring
      _ ≤ t * partition (fun i : Fin d => W i.succ) :=
        mul_le_mul_of_nonneg_left
          (ih _ (fun i c => hn _ c) (fun i c => h1 _ c) htail) ht
      _ = ∑ τ : Injection d q, t * weight (fun i => W i.succ) τ := by
        rw [partition, Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro τ _
        exact mul_le_mul_of_nonneg_right (hstep τ)
          (weight_nonneg _ (fun i c => hn _ c) τ)

/-- Deleting a color leaves a strictly positive partition even when the surplus is below one. -/
theorem partition_withoutColor_pos (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) : 0 < partition (withoutColor W c) := by
  have hn : ∀ i b, 0 ≤ withoutColor W c i b := by
    intro i b
    unfold withoutColor
    split_ifs
    · rfl
    · exact hW.nonneg i b
  have h1 : ∀ i b, withoutColor W c i b ≤ 1 := by
    intro i b
    unfold withoutColor
    split_ifs
    · norm_num
    · exact hW.le_one i b
  have hm : ∀ i, (d : ℝ) - 1 + s ≤ ∑ b, withoutColor W c i b := by
    intro i
    rw [show (fun b => withoutColor W c i b) =
      (fun b => if b = c then 0 else W i b) from rfl, sum_withoutColor]
    linarith [hW.row_mass i, hW.le_one i c]
  exact (pow_pos hW.positive d).trans_le (partition_ge_power_of_mass _ hW.positive.le hn h1 hm)

/-- The exact event numerator for a specified first-row color. -/
theorem head_numerator_eq (W : Fin (d + 1) → Fin q → ℝ) (c : Fin q) :
    (∑ σ : Injection (d + 1) q, weight W σ * cell 0 c σ) =
      W 0 c * partition (withoutColor (fun i : Fin d => W i.succ) c) := by
  classical
  rw [Fintype.sum_equiv (Equiv.embeddingFinSucc d (Fin q))
    (fun σ => weight W σ * cell 0 c σ)
    (fun x => W 0 x.2 * weight (fun i => W i.succ) x.1 *
      if (x.2 : Fin q) = c then 1 else 0) ?_]
  · rw [Fintype.sum_sigma, partition, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    let f : Fin q → ℝ := fun b => W 0 b * weight (fun i => W i.succ) τ *
      if b = c then 1 else 0
    let S : Finset (Fin q) := univ.filter (fun b => b ∉ Set.range τ)
    have hmem (b : Fin q) : b ∈ S ↔ b ∉ Set.range τ := by simp [S]
    change (∑ b : {b : Fin q // b ∉ Set.range τ}, f b) = _
    rw [← Finset.sum_subtype S hmem f, weight_withoutColor]
    simp [f, mul_ite, S]
  · intro σ
    rw [weight, Fin.prod_univ_succ]
    rfl

/-- The deleted-color partition is exactly the weight of the unused-color event. -/
theorem color_unused_probability (W : Fin d → Fin q → ℝ)
    (hW : ∀ i c, 0 ≤ W i c) (hZ : 0 < partition W) (c : Fin q) :
    partition (withoutColor W c) / partition W =
      1 - colorMean (law W hW hZ) c := by
  classical
  let μ := law W hW hZ
  have hpoint (σ : Injection d q) : (if c ∉ Set.range σ then (1 : ℝ) else 0) =
      1 - if c ∈ Set.range σ then 1 else 0 := by
    by_cases hc : c ∈ Set.range σ <;> simp [hc]
  calc
    _ = μ.expectation (fun σ => if c ∉ Set.range σ then 1 else 0) := by
      unfold FiniteLaw.expectation μ law
      rw [partition, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro σ _
      rw [weight_withoutColor]
      by_cases hc : c ∈ Set.range σ <;> simp [hc]
    _ = 1 - colorMean μ c := by
      simp_rw [hpoint]
      rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_const,
        ← colorMean_eq_expectation]

theorem partition_withoutColor_succ_ge (W : Fin (d + 1) → Fin q → ℝ)
    {s : ℝ} (hW : RowSurplus W s) (c : Fin q) :
    s * partition (withoutColor (fun i : Fin d => W i.succ) c) ≤
      partition (withoutColor W c) := by
  have hstep (τ : Injection d q) : s ≤
      ∑ b : {b : Fin q // b ∉ Set.range τ}, withoutColor W c 0 b := by
    have h1 (b : Fin q) : withoutColor W c 0 b ≤ 1 := by
      unfold withoutColor
      split_ifs
      · norm_num
      · exact hW.le_one 0 b
    have h := unused_mass_ge (withoutColor W c 0) h1 τ
    have hm := hW.row_mass 0
    change (∑ b, if b = c then 0 else W 0 b) - d ≤ _ at h
    rw [sum_withoutColor] at h
    push_cast at hm
    linarith [hW.le_one 0 c]
  rw [partition_succ]
  change s * partition (fun i : Fin d => withoutColor W c i.succ) ≤ _
  rw [partition, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  apply mul_le_mul_of_nonneg_right (hstep τ)
  apply weight_nonneg
  intro i b
  unfold withoutColor
  split_ifs
  · rfl
  · exact hW.nonneg _ b

theorem head_marginal_surplus_le (W : Fin (d + 1) → Fin q → ℝ)
    {s : ℝ} (hW : RowSurplus W s) (c : Fin q) :
    s * mean (law W hW.nonneg (partition_pos W hW)) 0 c ≤
      W 0 c * (partition (withoutColor W c) / partition W) := by
  have hZ := partition_pos W hW
  have heq : mean (law W hW.nonneg hZ) 0 c =
      (W 0 c * partition (withoutColor (fun i : Fin d => W i.succ) c)) / partition W := by
    unfold mean FiniteLaw.expectation law
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [head_numerator_eq]
  rw [heq]
  calc
    _ = W 0 c * ((s * partition (withoutColor (fun i : Fin d => W i.succ) c)) /
        partition W) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (partition_withoutColor_succ_ge W hW c) hZ.le)
      (hW.nonneg 0 c)

theorem marginal_surplus_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    s * mean (law W hW.nonneg (partition_pos W hW)) i c ≤
      partition (withoutColor W c) / partition W := by
  have hraw : s * mean (law W hW.nonneg (partition_pos W hW)) i c ≤
      W i c * (partition (withoutColor W c) / partition W) := by
    cases d with
    | zero => exact Fin.elim0 i
    | succ d =>
      let e := Equiv.swap (0 : Fin (d + 1)) i
      have hW' : RowSurplus (fun j => W (e j)) s :=
        ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
          fun j => hW.row_mass (e j)⟩
      have h := head_marginal_surplus_le (fun j => W (e j)) hW' c
      rw [marginal_reindex W hW e 0 c, partition_reindex] at h
      change s * mean (law W hW.nonneg (partition_pos W hW)) (e 0) c ≤
        W (e 0) c * (partition (fun j => withoutColor W c (e j)) / partition W) at h
      rw [partition_reindex] at h
      simpa [e] using h
  apply hraw.trans
  have hnonneg : 0 ≤ partition (withoutColor W c) / partition W :=
    div_nonneg (partition_withoutColor_pos W hW c).le (partition_pos W hW).le
  simpa using mul_le_mul_of_nonneg_right (hW.le_one i c) hnonneg

/-- Lemma 2.1(iii): the actual color-occupancy bound retaining d in the denominator. -/
theorem colorMean_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    colorMean (law W hW.nonneg (partition_pos W hW)) c ≤ (d : ℝ) / (d + s) := by
  have hsum : s * colorMean (law W hW.nonneg (partition_pos W hW)) c ≤
      (d : ℝ) * (partition (withoutColor W c) / partition W) := by
    unfold colorMean
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _i : Fin d, partition (withoutColor W c) / partition W :=
        Finset.sum_le_sum (fun i _ => marginal_surplus_le W hW i c)
      _ = _ := by simp
  rw [color_unused_probability W hW.nonneg (partition_pos W hW) c] at hsum
  have hds : 0 < (d : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg d) hW.positive
  apply (le_div_iff₀ hds).mpr
  nlinarith

end EdgeColoringMixing.WeightedInjection
