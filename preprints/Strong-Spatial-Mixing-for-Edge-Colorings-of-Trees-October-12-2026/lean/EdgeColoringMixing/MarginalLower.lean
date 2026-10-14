import EdgeColoringMixing.ColumnAvoidance

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

theorem partition_succ_le (W : Fin (d + 1) → Fin q → ℝ)
    (hn : ∀ i c, 0 ≤ W i c) (h1 : ∀ i c, W i c ≤ 1) :
    partition W ≤ (q : ℝ) * partition (fun i : Fin d => W i.succ) := by
  classical
  have hstep (τ : Injection d q) :
      (∑ c : {c : Fin q // c ∉ Set.range τ}, W 0 c) ≤ (q : ℝ) := by
    calc
      _ ≤ ∑ _c : {c : Fin q // c ∉ Set.range τ}, (1 : ℝ) :=
        Finset.sum_le_sum (fun c _ => h1 0 c)
      _ = (Fintype.card {c : Fin q // c ∉ Set.range τ} : ℝ) := by simp
      _ ≤ q := by
        exact_mod_cast (show Fintype.card {c : Fin q // c ∉ Set.range τ} ≤ q by
          simpa using Fintype.card_subtype_le (fun c : Fin q => c ∉ Set.range τ))
  rw [partition_succ, partition, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_right (hstep τ)
    (weight_nonneg _ (fun i c => hn _ c) τ)

theorem head_marginal_eq (W : Fin (d + 1) → Fin q → ℝ)
    (hn : ∀ i c, 0 ≤ W i c) (hZ : 0 < partition W) (c : Fin q) :
    mean (law W hn hZ) 0 c =
      W 0 c * partition (withoutColor (fun i : Fin d => W i.succ) c) / partition W := by
  unfold mean FiniteLaw.expectation law
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [head_numerator_eq]

theorem head_marginal_ge (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    W 0 c * (s + 1) / ((q : ℝ) * ((d + 1 : ℕ) + s)) ≤
      mean (law W hW.nonneg (partition_pos W hW)) 0 c := by
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have htail : RowSurplus (fun i : Fin d => W i.succ) (s + 1) := by
    refine ⟨ht, fun i b => hW.nonneg _ b, fun i b => hW.le_one _ b, ?_⟩
    intro i
    have h := hW.row_mass i.succ
    push_cast at h
    linarith
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt c.isLt
  have hds : 0 < (d : ℝ) + (s + 1) :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg d) ht
  have htailZ := partition_pos _ htail
  have hZ := partition_pos W hW
  have hU := partition_withoutColor_pos _ htail c
  have hratio : (s + 1) / ((d : ℝ) + (s + 1)) ≤
      partition (withoutColor (fun i : Fin d => W i.succ) c) /
        partition (fun i : Fin d => W i.succ) := by
    rw [color_unused_probability _ htail.nonneg htailZ c]
    have h := colorMean_le _ htail c
    have heq : 1 - (d : ℝ) / (d + (s + 1)) = (s + 1) / (d + (s + 1)) := by
      field_simp
      ring
    linarith
  rw [head_marginal_eq]
  calc
    _ = W 0 c * ((s + 1) / ((d : ℝ) + (s + 1))) / q := by
      push_cast
      rw [mul_div_assoc, mul_div_assoc, div_div]
      congr 2
      ring
    _ ≤ W 0 c * (partition (withoutColor (fun i : Fin d => W i.succ) c) /
        partition (fun i : Fin d => W i.succ)) / q :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (hW.nonneg 0 c)) hq.le
    _ = (W 0 c * partition (withoutColor (fun i : Fin d => W i.succ) c)) /
        ((q : ℝ) * partition (fun i : Fin d => W i.succ)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (hW.nonneg 0 c) hU.le) hZ
      (partition_succ_le W hW.nonneg hW.le_one)

/-- Lemma 2.1(iv) for every actual cell, with no positivity assumption on that cell's weight. -/
theorem marginal_ge (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    W i c * (s + 1) / ((q : ℝ) * ((d : ℝ) + s)) ≤
      mean (law W hW.nonneg (partition_pos W hW)) i c := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    let e := Equiv.swap (0 : Fin (d + 1)) i
    have hW' : RowSurplus (fun j => W (e j)) s :=
      ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
        fun j => hW.row_mass (e j)⟩
    have h := head_marginal_ge (fun j => W (e j)) hW' c
    rw [marginal_reindex W hW e 0 c] at h
    simpa [e] using h

end EdgeColoringMixing.WeightedInjection
