import EdgeColoringMixing.WeightedInjections
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- Exact insertion of the first row, summed over injections of the remaining rows. -/
theorem partition_succ (W : Fin (d + 1) → Fin q → ℝ) :
    partition W = ∑ τ : Injection d q,
      (∑ c : {c : Fin q // c ∉ Set.range τ}, W 0 c) * weight (fun i => W i.succ) τ := by
  classical
  unfold partition
  rw [Fintype.sum_equiv (Equiv.embeddingFinSucc d (Fin q)) (weight W)
    (fun x => W 0 x.2 * weight (fun i => W i.succ) x.1) ?_]
  · rw [Fintype.sum_sigma]
    simp only [← Finset.sum_mul]
  · intro σ
    rw [weight, Fin.prod_univ_succ]
    rfl

/-- Deleting the colors already used by d rows costs at most d units of row mass. -/
theorem unused_mass_ge (w : Fin q → ℝ) (hw : ∀ c, w c ≤ 1)
    (τ : Injection d q) :
    (∑ c, w c) - d ≤ ∑ c : {c : Fin q // c ∉ Set.range τ}, w c := by
  classical
  let used : Finset (Fin q) := univ.image τ
  have hmem (c : Fin q) : c ∈ univ \ used ↔ c ∉ Set.range τ := by
    simp [used, Set.mem_range]
  have hused : (∑ c ∈ used, w c) ≤ (d : ℝ) := by
    rw [show used = univ.image τ from rfl,
      Finset.sum_image (fun _ _ _ _ h => τ.injective h)]
    calc
      ∑ i, w (τ i) ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hw _)
      _ = d := by simp
  rw [← Finset.sum_subtype (univ \ used) hmem w]
  have hsum := Finset.sum_sdiff (f := w) (Finset.subset_univ used)
  linarith

theorem partition_succ_ge (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) :
    (s + 1) * partition (fun i : Fin d => W i.succ) ≤ partition W := by
  have hstep (τ : Injection d q) : s + 1 ≤
      ∑ c : {c : Fin q // c ∉ Set.range τ}, W 0 c := by
    have h := unused_mass_ge (W 0) (hW.le_one 0) τ
    have hm := hW.row_mass 0
    push_cast at hm
    linarith
  rw [partition_succ, partition, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_right (hstep τ)
    (weight_nonneg _ (fun i c => hW.nonneg _ c) τ)

/-- The first-row event numerator is bounded by the unconstrained tail partition. -/
theorem head_numerator_bound (W : Fin (d + 1) → Fin q → ℝ)
    (hW : ∀ i c, 0 ≤ W i c) (c : Fin q) :
    (∑ σ : Injection (d + 1) q, weight W σ * cell 0 c σ) ≤
      W 0 c * partition (fun i : Fin d => W i.succ) := by
  classical
  rw [Fintype.sum_equiv (Equiv.embeddingFinSucc d (Fin q))
    (fun σ => weight W σ * cell 0 c σ)
    (fun x => W 0 x.2 * weight (fun i => W i.succ) x.1 *
      if (x.2 : Fin q) = c then 1 else 0) ?_]
  · rw [Fintype.sum_sigma, partition, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro τ _
    let f : Fin q → ℝ := fun b => W 0 b * weight (fun i => W i.succ) τ *
      if b = c then 1 else 0
    let S : Finset (Fin q) := univ.filter (fun b => b ∉ Set.range τ)
    have hmem (b : Fin q) : b ∈ S ↔ b ∉ Set.range τ := by simp [S]
    change (∑ b : {b : Fin q // b ∉ Set.range τ}, f b) ≤ _
    rw [← Finset.sum_subtype S hmem f]
    calc
      ∑ b ∈ S, f b ≤ ∑ b : Fin q, f b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro b _ _
        dsimp only [f]
        apply mul_nonneg (mul_nonneg (hW 0 b)
          (weight_nonneg _ (fun i a => hW _ a) τ))
        split_ifs <;> norm_num
      _ = W 0 c * weight (fun i => W i.succ) τ := by
        simp [f, mul_ite]
  · intro σ
    rw [weight, Fin.prod_univ_succ]
    rfl

/-- The actual normalized first-row marginal bound, Lemma 2.1(ii). -/
theorem head_marginal_le (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    mean (law W hW.nonneg (partition_pos W hW)) 0 c ≤ W 0 c / (s + 1) := by
  have ht : 0 < s + 1 := by linarith [hW.positive]
  have hZ := partition_pos W hW
  have heq : mean (law W hW.nonneg hZ) 0 c =
      (∑ σ : Injection (d + 1) q, weight W σ * cell 0 c σ) / partition W := by
    unfold mean FiniteLaw.expectation law
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [heq]
  apply (div_le_div_iff₀ hZ ht).mpr
  calc
    _ ≤ (W 0 c * partition (fun i : Fin d => W i.succ)) * (s + 1) :=
      mul_le_mul_of_nonneg_right (head_numerator_bound W hW.nonneg c) ht.le
    _ = W 0 c * ((s + 1) * partition (fun i : Fin d => W i.succ)) := by ring
    _ ≤ W 0 c * partition W :=
      mul_le_mul_of_nonneg_left (partition_succ_ge W hW) (hW.nonneg 0 c)

theorem weight_reindex (W : Fin d → Fin q → ℝ) (e : Fin d ≃ Fin d)
    (σ : Injection d q) :
    weight (fun i => W (e i)) ((e.symm.embeddingCongr (Equiv.refl (Fin q))) σ) =
      weight W σ := by
  unfold weight
  simpa using e.prod_comp (fun i => W i (σ i))

theorem partition_reindex (W : Fin d → Fin q → ℝ) (e : Fin d ≃ Fin d) :
    partition (fun i => W (e i)) = partition W := by
  symm
  exact Fintype.sum_equiv (e.symm.embeddingCongr (Equiv.refl (Fin q)))
    (weight W) (weight (fun i => W (e i))) (fun σ => (weight_reindex W e σ).symm)

theorem marginal_reindex (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (e : Fin d ≃ Fin d) (i : Fin d) (c : Fin q) :
    let hW' : RowSurplus (fun j => W (e j)) s :=
      ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
        fun j => hW.row_mass (e j)⟩
    mean (law (fun j => W (e j)) hW'.nonneg (partition_pos _ hW')) i c =
      mean (law W hW.nonneg (partition_pos W hW)) (e i) c := by
  dsimp only
  unfold mean FiniteLaw.expectation law
  simp only [partition_reindex]
  symm
  apply Fintype.sum_equiv (e.symm.embeddingCongr (Equiv.refl (Fin q)))
  intro σ
  rw [weight_reindex]
  rfl

/-- Lemma 2.1(ii) for every row and color of the actual weighted-injection law. -/
theorem marginal_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    mean (law W hW.nonneg (partition_pos W hW)) i c ≤ W i c / (s + 1) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    let e := Equiv.swap (0 : Fin (d + 1)) i
    have hW' : RowSurplus (fun j => W (e j)) s :=
      ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
        fun j => hW.row_mass (e j)⟩
    have h := head_marginal_le (fun j => W (e j)) hW' c
    rw [marginal_reindex W hW e 0 c] at h
    simpa [e] using h

/-- Lemma 2.1(i): the quantitative partition lower bound, for every number of rows. -/
theorem partition_lower_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) : (s + 1)^d ≤ partition W := by
  induction d with
  | zero => simp [partition, weight]
  | succ d ih =>
    have htail : RowSurplus (fun i : Fin d => W i.succ) s := by
      refine ⟨hW.positive, fun i c => hW.nonneg _ c, fun i c => hW.le_one _ c, ?_⟩
      intro i
      have h := hW.row_mass i.succ
      push_cast at h
      linarith
    have hstep (τ : Injection d q) : s + 1 ≤
        ∑ c : {c : Fin q // c ∉ Set.range τ}, W 0 c := by
      have h := unused_mass_ge (W 0) (hW.le_one 0) τ
      have hm := hW.row_mass 0
      push_cast at hm
      linarith
    rw [partition_succ]
    calc
      (s + 1)^(d + 1) = (s + 1) * (s + 1)^d := by ring
      _ ≤ (s + 1) * partition (fun i : Fin d => W i.succ) :=
        mul_le_mul_of_nonneg_left (ih _ htail) (by linarith [hW.positive])
      _ = ∑ τ : Injection d q, (s + 1) * weight (fun i => W i.succ) τ := by
        rw [partition, Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro τ _
        exact mul_le_mul_of_nonneg_right (hstep τ)
          (weight_nonneg _ htail.nonneg τ)

end EdgeColoringMixing.WeightedInjection
