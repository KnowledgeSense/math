import EdgeColoringMixing.MarginalLower
import EdgeColoringMixing.Derivatives
import EdgeColoringMixing.PosteriorMoments

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

/-- Delete the first row of an injection. -/
def tailInjection (σ : Injection (d + 1) q) : Injection d q :=
  ⟨fun i => σ i.succ, fun _ _ h => Fin.succ_injective _ (σ.injective h)⟩

/-- Deleting a row increases the surplus by one. -/
theorem RowSurplus.tail (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) : RowSurplus (fun i : Fin d => W i.succ) (s + 1) := by
  refine ⟨by linarith [hW.positive], fun i c => hW.nonneg _ c,
    fun i c => hW.le_one _ c, ?_⟩
  intro i
  have h := hW.row_mass i.succ
  push_cast at h
  linarith

/-- Forbidding one color costs at most one unit of surplus. -/
theorem RowSurplus.forbid (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hs : 1 < s) (c : Fin q) :
    RowSurplus (withoutColor W c) (s - 1) := by
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · intro i b
    unfold withoutColor
    split_ifs
    · rfl
    · exact hW.nonneg i b
  · intro i b
    unfold withoutColor
    split_ifs
    · norm_num
    · exact hW.le_one i b
  · intro i
    change (d : ℝ) + (s - 1) ≤ ∑ b, if b = c then 0 else W i b
    rw [sum_withoutColor]
    linarith [hW.row_mass i, hW.le_one i c]

/-- The remaining matrix after fixing the first row still has the original surplus. -/
theorem RowSurplus.tail_withoutColor (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    RowSurplus (withoutColor (fun i : Fin d => W i.succ) c) s := by
  have h := (hW.tail W).forbid _ (by linarith [hW.positive]) c
  simpa using h

/-- Exact factorization of a first-row event, with every remaining-row observable. -/
theorem head_observable_numerator (W : Fin (d + 1) → Fin q → ℝ) (c : Fin q)
    (f : Injection d q → ℝ) :
    numerator W (fun σ => cell 0 c σ * f (tailInjection σ)) =
      W 0 c * numerator (withoutColor (fun i : Fin d => W i.succ) c) f := by
  classical
  unfold numerator
  rw [Fintype.sum_equiv (Equiv.embeddingFinSucc d (Fin q))
    (fun σ => weight W σ * (cell 0 c σ * f (tailInjection σ)))
    (fun x => W 0 x.2 * weight (fun i => W i.succ) x.1 *
      (if (x.2 : Fin q) = c then 1 else 0) * f x.1) ?_]
  · rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    let g : Fin q → ℝ := fun b => W 0 b * weight (fun i => W i.succ) τ *
      (if b = c then 1 else 0) * f τ
    let S : Finset (Fin q) := univ.filter (fun b => b ∉ Set.range τ)
    have hmem (b : Fin q) : b ∈ S ↔ b ∉ Set.range τ := by simp [S]
    change (∑ b : {b : Fin q // b ∉ Set.range τ}, g b) = _
    rw [← Finset.sum_subtype S hmem g, weight_withoutColor]
    by_cases hc : c ∈ Set.range τ
    · simp [g, mul_ite, ite_mul, S, Set.mem_range, mul_assoc]
    · simp [g, mul_ite, ite_mul, S, Set.mem_range, mul_assoc] at hc ⊢
  · intro σ
    rw [weight, Fin.prod_univ_succ]
    change W 0 (σ 0) * (∏ i : Fin d, W i.succ (σ i.succ)) *
      (cell 0 c σ * f (tailInjection σ)) =
      W 0 (σ 0) * weight (fun i : Fin d => W i.succ) (tailInjection σ) *
      (if σ 0 = c then 1 else 0) * f (tailInjection σ)
    unfold weight
    change W 0 (σ 0) * (∏ i : Fin d, W i.succ (σ i.succ)) *
      ((if σ 0 = c then 1 else 0) * f (tailInjection σ)) =
      W 0 (σ 0) * (∏ i : Fin d, W i.succ (σ i.succ)) *
      (if σ 0 = c then 1 else 0) * f (tailInjection σ)
    ring

/-- Conditioning on a positive first-row cell gives exactly the smaller injection law. -/
theorem head_condition_expectation (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) (hc : 0 < W 0 c)
    (f : Injection d q → ℝ) :
    weightedExpectation W (fun σ => cell 0 c σ * f (tailInjection σ)) /
      mean (law W hW.nonneg (partition_pos W hW)) 0 c =
    weightedExpectation (withoutColor (fun i : Fin d => W i.succ) c) f := by
  have hZ := partition_pos W hW
  have hZc := partition_pos _ (hW.tail_withoutColor W c)
  rw [head_marginal_eq]
  unfold weightedExpectation
  rw [head_observable_numerator]
  field_simp

/-- A cell has positive probability exactly when its weight is positive. -/
theorem marginal_pos_iff (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    0 < mean (law W hW.nonneg (partition_pos W hW)) i c ↔ 0 < W i c := by
  constructor
  · intro h
    have hm := marginal_le W hW i c
    have ht : 0 < s + 1 := by linarith [hW.positive]
    exact (div_pos_iff.mp (h.trans_le hm)).resolve_right (fun h => (not_lt_of_ge ht.le) h.2) |>.1
  · intro h
    have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt c.isLt
    have hds : 0 < (d : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg d) hW.positive
    have ht : 0 < s + 1 := by linarith [hW.positive]
    exact (div_pos (mul_pos h ht) (mul_pos hq hds)).trans_le (marginal_ge W hW i c)

theorem conditionalMean_eq_mixed_div (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hx : 0 < mean μ x.1 x.2) :
    conditionalMean μ x y =
      μ.expectation (fun σ => cell x.1 x.2 σ * cell y.1 y.2 σ) / mean μ x.1 x.2 := by
  rw [conditionalMean, covariance, FiniteLaw.covariance_eq_mixed_moment]
  change mean μ y.1 y.2 +
    (μ.expectation (fun σ => cell y.1 y.2 σ * cell x.1 x.2 σ) -
      mean μ y.1 y.2 * mean μ x.1 x.2) / mean μ x.1 x.2 = _
  simp_rw [mul_comm (cell y.1 y.2 _)]
  field_simp
  ring

theorem conditionalMean_nonneg (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hx : 0 < mean μ x.1 x.2) :
    0 ≤ conditionalMean μ x y := by
  rw [conditionalMean_eq_mixed_div μ x y hx]
  exact div_nonneg (μ.expectation_nonneg (fun σ =>
    mul_nonneg (cell_nonneg _ _ σ) (cell_nonneg _ _ σ))) hx.le

/-- The actual conditional cell marginal equals the corresponding smaller-law marginal. -/
theorem head_conditionalMean_tail (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) (hc : 0 < W 0 c) (i : Fin d) (b : Fin q) :
    conditionalMean (law W hW.nonneg (partition_pos W hW)) (0,c) (i.succ,b) =
      mean (law (withoutColor (fun j : Fin d => W j.succ) c)
        (hW.tail_withoutColor W c).nonneg
        (partition_pos _ (hW.tail_withoutColor W c))) i b := by
  rw [conditionalMean_eq_mixed_div _ _ _ ((marginal_pos_iff W hW 0 c).mpr hc)]
  rw [← weightedExpectation_eq]
  change weightedExpectation W (fun σ => cell 0 c σ * cell i b (tailInjection σ)) /
    mean (law W hW.nonneg (partition_pos W hW)) 0 c = _
  rw [head_condition_expectation W hW c hc, weightedExpectation_eq]
  rfl

/-- Row relabeling preserves the exact covariance entries. -/
theorem covariance_reindex (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (e : Fin d ≃ Fin d) (i j : Fin d) (c b : Fin q) :
    let hW' : RowSurplus (fun k => W (e k)) s :=
      ⟨hW.positive, fun k a => hW.nonneg (e k) a, fun k a => hW.le_one (e k) a,
        fun k => hW.row_mass (e k)⟩
    covariance (law (fun k => W (e k)) hW'.nonneg (partition_pos _ hW')) (i,c) (j,b) =
      covariance (law W hW.nonneg (partition_pos W hW)) (e i,c) (e j,b) := by
  dsimp only
  rw [covariance, covariance, FiniteLaw.covariance_eq_mixed_moment,
    FiniteLaw.covariance_eq_mixed_moment]
  change _ - mean (law (fun k => W (e k)) _ _) i c *
    mean (law (fun k => W (e k)) _ _) j b =
    _ - mean (law W _ _) (e i) c * mean (law W _ _) (e j) b
  rw [marginal_reindex W hW e i c, marginal_reindex W hW e j b]
  congr 1
  unfold FiniteLaw.expectation law
  simp only [partition_reindex]
  symm
  apply Fintype.sum_equiv (e.symm.embeddingCongr (Equiv.refl (Fin q)))
  intro σ
  rw [weight_reindex]
  rfl

theorem conditionalMean_reindex (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (e : Fin d ≃ Fin d) (i j : Fin d) (c b : Fin q) :
    let hW' : RowSurplus (fun k => W (e k)) s :=
      ⟨hW.positive, fun k a => hW.nonneg (e k) a, fun k a => hW.le_one (e k) a,
        fun k => hW.row_mass (e k)⟩
    conditionalMean (law (fun k => W (e k)) hW'.nonneg (partition_pos _ hW')) (i,c) (j,b) =
      conditionalMean (law W hW.nonneg (partition_pos W hW)) (e i,c) (e j,b) := by
  dsimp only
  unfold conditionalMean
  rw [marginal_reindex W hW e j b, covariance_reindex W hW e j i b c,
    marginal_reindex W hW e i c]

/-- A remaining cell retains the same surplus-dependent upper bound after conditioning. -/
theorem conditionalMean_le (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i j : Fin d) (c b : Fin q) (hc : 0 < W i c) (hij : i ≠ j) :
    conditionalMean (law W hW.nonneg (partition_pos W hW)) (i,c) (j,b) ≤
      W j b / (s + 1) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    let e := Equiv.swap (0 : Fin (d + 1)) i
    let W' := fun k => W (e k)
    have hW' : RowSurplus W' s :=
      ⟨hW.positive, fun k a => hW.nonneg (e k) a, fun k a => hW.le_one (e k) a,
        fun k => hW.row_mass (e k)⟩
    have hei : e 0 = i := by simp [e]
    have hej : e j ≠ 0 := by
      intro h
      have h' := congrArg e h
      simp [e] at h'
      exact hij h'.symm
    obtain ⟨k,hk⟩ := Fin.exists_succ_eq.mpr hej
    have hkc : 0 < W' 0 c := by simpa [W', hei] using hc
    have h := head_conditionalMean_tail W' hW' c hkc k b
    rw [conditionalMean_reindex W hW e 0 k.succ c b] at h
    have hj : e k.succ = j := by rw [hk]; simp [e]
    rw [hei, hj] at h
    rw [h]
    have hm := marginal_le _ (hW'.tail_withoutColor W' c) k b
    apply hm.trans
    apply div_le_div_of_nonneg_right _ (by linarith [hW.positive])
    unfold withoutColor
    split_ifs
    · exact hW.nonneg j b
    · exact le_of_eq (by change W (e k.succ) b = W j b; rw [hj])

end EdgeColoringMixing.WeightedInjection
