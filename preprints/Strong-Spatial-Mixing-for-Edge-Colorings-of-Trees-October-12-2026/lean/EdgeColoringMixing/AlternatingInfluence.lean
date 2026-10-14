import EdgeColoringMixing.MarginalDistance

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset

variable {d q : ℕ}

noncomputable def marginalVector (μ : FiniteLaw (Injection d q)) : Fin d × Fin q → ℝ :=
  fun x => mean μ x.1 x.2

/-- Coordinate distance splits into the first row and the remaining rows. -/
theorem coordinateDistance_rows (p p' : Fin (d + 1) × Fin q → ℝ) :
    coordinateDistance p p' = coordinateDistance (fun c => p (0,c)) (fun c => p' (0,c)) +
      coordinateDistance (fun x : Fin d × Fin q => p (x.1.succ,x.2))
        (fun x : Fin d × Fin q => p' (x.1.succ,x.2)) := by
  unfold coordinateDistance
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ, Fintype.sum_prod_type]

/-- One alternating-path step, expressed directly as a bound on all cell marginals. -/
theorem head_conditional_distance_le (W : Fin (d + 1) → Fin q → ℝ) {t : ℝ}
    (hW : RowSurplus W t) (ht : 1 < t) (c : Fin q) (hc : 0 < W 0 c)
    (ih : ∀ (U : Fin d → Fin q → ℝ) (hU : RowSurplus U t) (b : Fin q),
      coordinateDistance (marginalVector (law U hU.nonneg (partition_pos U hU)))
        (marginalVector (law (withoutColor U b) (hU.forbid U ht b).nonneg
          (partition_pos _ (hU.forbid U ht b)))) ≤ 2 * (d : ℝ) / t) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let hWc := hW.forbid W ht c
    let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
    coordinateDistance (conditionalMean μ (0,c)) (marginalVector μc) ≤
      2 + 2 * (d : ℝ) / t := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let hWc := hW.forbid W ht c
  let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
  let U := withoutColor (fun i : Fin d => W i.succ) c
  have hU : RowSurplus U t := hW.tail_withoutColor W c
  let ν := law U hU.nonneg (partition_pos U hU)
  have hx : 0 < mean μ 0 c := (marginal_pos_iff W hW 0 c).mpr hc
  have hhead : coordinateDistance (fun b => conditionalMean μ (0,c) (0,b))
      (fun b => mean μc 0 b) ≤ 2 :=
    coordinateDistance.probabilities_le_two _ _
      (fun b => conditionalMean_nonneg μ (0,c) (0,b) hx) (mean_nonneg μc 0)
      (conditionalMean_row_sum μ (0,c) hx 0) (mean_row_sum μc 0)
  have htail_eq (x : Fin d × Fin q) : conditionalMean μ (0,c) (x.1.succ,x.2) =
      marginalVector ν x := head_conditionalMean_tail W hW c hc x.1 x.2
  have hmix (x : Fin d × Fin q) : mean μc x.1.succ x.2 =
      ∑ b, mean μc 0 b * conditionalMean μc (0,b) (x.1.succ,x.2) :=
    mean_row_mixture μc 0 (x.1.succ,x.2)
  have htail : coordinateDistance (marginalVector ν)
      (fun x : Fin d × Fin q => mean μc x.1.succ x.2) ≤ 2 * (d : ℝ) / t := by
    simp_rw [hmix]
    apply (coordinateDistance.mixture_right (marginalVector ν)
      (fun (b : Fin q) (x : Fin d × Fin q) => conditionalMean μc (0,b) (x.1.succ,x.2))
      (mean μc 0) (mean_nonneg μc 0) (mean_row_sum μc 0)).trans
    calc
      _ ≤ ∑ b, mean μc 0 b * (2 * (d : ℝ) / t) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : mean μc 0 b = 0
        · simp [hb]
        · have hbpos := lt_of_le_of_ne (mean_nonneg μc 0 b) (Ne.symm hb)
          have hbW : 0 < withoutColor W c 0 b :=
            (marginal_pos_iff _ hWc 0 b).mp hbpos
          have hpost (x : Fin d × Fin q) :
              conditionalMean μc (0,b) (x.1.succ,x.2) =
                mean (law (withoutColor U b) (hU.forbid U ht b).nonneg
                  (partition_pos _ (hU.forbid U ht b))) x.1 x.2 := by
            exact head_conditionalMean_tail (withoutColor W c) hWc b hbW x.1 x.2
          apply mul_le_mul_of_nonneg_left _ (mean_nonneg μc 0 b)
          simp_rw [hpost]
          exact ih U hU b
      _ = _ := by rw [← Finset.sum_mul, mean_row_sum, one_mul]
  change coordinateDistance (conditionalMean μ (0,c)) (marginalVector μc) ≤ _
  rw [coordinateDistance_rows]
  change coordinateDistance (fun b => conditionalMean μ (0,c) (0,b))
    (fun b => mean μc 0 b) +
    coordinateDistance (fun x : Fin d × Fin q => conditionalMean μ (0,c) (x.1.succ,x.2))
      (fun x : Fin d × Fin q => mean μc x.1.succ x.2) ≤ _
  simp_rw [htail_eq]
  exact add_le_add hhead htail

theorem conditional_distance_le (W : Fin (d + 1) → Fin q → ℝ) {t : ℝ}
    (hW : RowSurplus W t) (ht : 1 < t) (i : Fin (d + 1)) (c : Fin q) (hc : 0 < W i c)
    (ih : ∀ (U : Fin d → Fin q → ℝ) (hU : RowSurplus U t) (b : Fin q),
      coordinateDistance (marginalVector (law U hU.nonneg (partition_pos U hU)))
        (marginalVector (law (withoutColor U b) (hU.forbid U ht b).nonneg
          (partition_pos _ (hU.forbid U ht b)))) ≤ 2 * (d : ℝ) / t) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let hWc := hW.forbid W ht c
    let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
    coordinateDistance (conditionalMean μ (i,c)) (marginalVector μc) ≤
      2 + 2 * (d : ℝ) / t := by
  dsimp only
  let e := Equiv.swap (0 : Fin (d + 1)) i
  let W' := fun j => W (e j)
  have hW' : RowSurplus W' t :=
    ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
      fun j => hW.row_mass (e j)⟩
  have hei : e 0 = i := by simp [e]
  have hc' : 0 < W' 0 c := by simpa [W', hei] using hc
  have h := head_conditional_distance_le W' hW' ht c hc' ih
  dsimp only at h
  let μ := law W hW.nonneg (partition_pos W hW)
  let μ' := law W' hW'.nonneg (partition_pos W' hW')
  let hWc := hW.forbid W ht c
  let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
  let hWc' := hW'.forbid W' ht c
  let μc' := law (withoutColor W' c) hWc'.nonneg (partition_pos _ hWc')
  have hp (j : Fin (d + 1)) (b : Fin q) :
      conditionalMean μ' (0,c) (j,b) = conditionalMean μ (i,c) (e j,b) := by
    have h' := conditionalMean_reindex W hW e 0 j c b
    simpa [μ', μ, W', hei] using h'
  have hp' (j : Fin (d + 1)) (b : Fin q) : mean μc' j b = mean μc (e j) b :=
    marginal_reindex (withoutColor W c) hWc e j b
  have heq : coordinateDistance (conditionalMean μ' (0,c)) (marginalVector μc') =
      coordinateDistance (conditionalMean μ (i,c)) (marginalVector μc) := by
    unfold coordinateDistance marginalVector
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp_rw [hp, hp']
    exact Equiv.sum_comp e (fun j => ∑ b, |conditionalMean μ (i,c) (j,b) - mean μc j b|)
  change coordinateDistance (conditionalMean μ' (0,c)) (marginalVector μc') ≤ _ at h
  rw [heq] at h
  exact h

/-- The alternating-path estimate for all actual cell marginals.
This is the precise quantitative consequence of Lemma 4.3 needed in the covariance proof. -/
theorem color_deletion_distance (W : Fin d → Fin q → ℝ) {t : ℝ}
    (hW : RowSurplus W t) (ht : 1 < t) (c : Fin q) :
    coordinateDistance (marginalVector (law W hW.nonneg (partition_pos W hW)))
      (marginalVector (law (withoutColor W c) (hW.forbid W ht c).nonneg
        (partition_pos _ (hW.forbid W ht c)))) ≤ 2 * (d : ℝ) / t := by
  induction d generalizing c with
  | zero => simp [coordinateDistance]
  | succ d ih =>
    let μ := law W hW.nonneg (partition_pos W hW)
    let hWc := hW.forbid W ht c
    let μc := law (withoutColor W c) hWc.nonneg (partition_pos _ hWc)
    have hdecomp (y : Fin (d + 1) × Fin q) :
        marginalVector μ y = (1 - ∑ i, mean μ i c) * marginalVector μc y +
          ∑ i, mean μ i c * conditionalMean μ (i,c) y :=
      mean_color_mixture W hW ht c y
    have hstep := coordinateDistance.common_part (marginalVector μ) (marginalVector μc)
      (fun i => conditionalMean μ (i,c)) (fun i => mean μ i c)
      (fun i => mean_nonneg μ i c) hdecomp
    have htpos : 0 < t := by linarith
    have hK : 0 ≤ 2 + 2 * (d : ℝ) / t := by positivity
    have hsum : (∑ i, mean μ i c * coordinateDistance (conditionalMean μ (i,c))
        (marginalVector μc)) ≤ colorMean μ c * (2 + 2 * (d : ℝ) / t) := by
      rw [colorMean, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : mean μ i c = 0
      · simp [hi]
      · have hipos := lt_of_le_of_ne (mean_nonneg μ i c) (Ne.symm hi)
        have hiW := (marginal_pos_iff W hW i c).mp hipos
        apply mul_le_mul_of_nonneg_left _ (mean_nonneg μ i c)
        exact conditional_distance_le W hW ht i c hiW (fun U hU b => ih U hU b)
    apply (hstep.trans hsum).trans
    calc
      _ ≤ ((d + 1 : ℕ) : ℝ) / (((d + 1 : ℕ) : ℝ) + t) *
          (2 + 2 * (d : ℝ) / t) :=
        mul_le_mul_of_nonneg_right (colorMean_le W hW c) hK
      _ ≤ 2 * ((d + 1 : ℕ) : ℝ) / t := by
        have hden : 0 < ((d + 1 : ℕ) : ℝ) + t := by positivity
        apply (le_div_iff₀ htpos).mpr
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        apply (div_le_iff₀ hden).mpr
        field_simp
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- The conditional first-row influence on the remaining-row marginals. -/
theorem head_conditional_tail_distance (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) (hc : 0 < W 0 c) :
    let μ := law W hW.nonneg (partition_pos W hW)
    coordinateDistance
      (fun x : Fin d × Fin q => conditionalMean μ (0,c) (x.1.succ,x.2))
      (fun x : Fin d × Fin q => mean μ x.1.succ x.2) ≤ 4 * (d : ℝ) / (s + 1) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let U := fun i : Fin d => W i.succ
  have hU : RowSurplus U (s + 1) := hW.tail W
  have ht : 1 < s + 1 := by linarith [hW.positive]
  let ν := law U hU.nonneg (partition_pos U hU)
  let νb := fun b => law (withoutColor U b) (hU.forbid U ht b).nonneg
    (partition_pos _ (hU.forbid U ht b))
  let Q : Fin q → Fin d × Fin q → ℝ :=
    fun b x => conditionalMean μ (0,b) (x.1.succ,x.2)
  have hpost (b : Fin q) (hb : 0 < W 0 b) : Q b = marginalVector (νb b) := by
    funext x
    exact head_conditionalMean_tail W hW b hb x.1 x.2
  have hmix (x : Fin d × Fin q) : mean μ x.1.succ x.2 = ∑ b, mean μ 0 b * Q b x :=
    mean_row_mixture μ 0 (x.1.succ,x.2)
  change coordinateDistance (Q c) (fun x : Fin d × Fin q => mean μ x.1.succ x.2) ≤ _
  simp_rw [hmix]
  apply (coordinateDistance.mixture_right (Q c) Q (mean μ 0)
    (mean_nonneg μ 0) (mean_row_sum μ 0)).trans
  calc
    _ ≤ ∑ b, mean μ 0 b * (4 * (d : ℝ) / (s + 1)) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : mean μ 0 b = 0
      · simp [hb]
      · have hbpos := lt_of_le_of_ne (mean_nonneg μ 0 b) (Ne.symm hb)
        have hbW := (marginal_pos_iff W hW 0 b).mp hbpos
        apply mul_le_mul_of_nonneg_left _ (mean_nonneg μ 0 b)
        rw [hpost c hc, hpost b hbW]
        apply (coordinateDistance.triangle (marginalVector (νb c))
          (marginalVector ν) (marginalVector (νb b))).trans
        have h₁ := color_deletion_distance U hU ht c
        have h₂ := color_deletion_distance U hU ht b
        rw [coordinateDistance.symm] at h₁
        change coordinateDistance (marginalVector (νb c)) (marginalVector ν) ≤ _ at h₁
        change coordinateDistance (marginalVector ν) (marginalVector (νb b)) ≤ _ at h₂
        exact (add_le_add h₁ h₂).trans_eq (by ring)
    _ = _ := by rw [← Finset.sum_mul, mean_row_sum, one_mul]

/-- Cross-row absolute covariances for the first row, with the required surplus factor. -/
theorem head_crossRow_covariance_bound (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (c : Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    (∑ x : Fin d × Fin q, |covariance μ (0,c) (x.1.succ,x.2)|) ≤
      4 * (d : ℝ) * mean μ 0 c / (s + 1) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  by_cases hc : mean μ 0 c = 0
  · have hz (x : Fin d × Fin q) : covariance μ (0,c) (x.1.succ,x.2) = 0 := by
      rw [covariance, FiniteLaw.covariance_symm]
      exact covariance_eq_zero_of_mean_zero μ _ (0,c) hc
    change (∑ x : Fin d × Fin q, |covariance μ (0,c) (x.1.succ,x.2)|) ≤
      4 * (d : ℝ) * mean μ 0 c / (s + 1)
    simp [hz, hc]
  · have hcpos := lt_of_le_of_ne (mean_nonneg μ 0 c) (Ne.symm hc)
    have hcW := (marginal_pos_iff W hW 0 c).mp hcpos
    have heq (x : Fin d × Fin q) : covariance μ (0,c) (x.1.succ,x.2) =
        mean μ 0 c * (conditionalMean μ (0,c) (x.1.succ,x.2) - mean μ x.1.succ x.2) := by
      have h := mean_mul_conditionalMean μ (0,c) (x.1.succ,x.2)
      rw [covariance, FiniteLaw.covariance_symm] at h
      change _ = _ + covariance μ (0,c) (x.1.succ,x.2) at h
      linarith
    change (∑ x : Fin d × Fin q, |covariance μ (0,c) (x.1.succ,x.2)|) ≤
      4 * (d : ℝ) * mean μ 0 c / (s + 1)
    simp_rw [heq, abs_mul, abs_of_nonneg (mean_nonneg μ 0 c)]
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (head_conditional_tail_distance W hW c hcW)
      (mean_nonneg μ 0 c)
    change mean μ 0 c * coordinateDistance
      (fun x : Fin d × Fin q => conditionalMean μ (0,c) (x.1.succ,x.2))
      (fun x : Fin d × Fin q => mean μ x.1.succ x.2) ≤ _ at h
    exact h.trans_eq (by ring)

noncomputable def crossRowAbs (μ : FiniteLaw (Injection d q)) (i : Fin d) (c : Fin q) : ℝ :=
  ∑ j, if j = i then 0 else ∑ b, |covariance μ (i,c) (j,b)|

/-- The full quantitative cross-row influence bound for every actual cell. -/
theorem crossRow_covariance_bound (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin d) (c : Fin q) :
    let μ := law W hW.nonneg (partition_pos W hW)
    crossRowAbs μ i c ≤ 4 * ((d : ℝ) - 1) * mean μ i c / (s + 1) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    let e := Equiv.swap (0 : Fin (d + 1)) i
    let W' := fun j => W (e j)
    have hW' : RowSurplus W' s :=
      ⟨hW.positive, fun j b => hW.nonneg (e j) b, fun j b => hW.le_one (e j) b,
        fun j => hW.row_mass (e j)⟩
    let μ := law W hW.nonneg (partition_pos W hW)
    let μ' := law W' hW'.nonneg (partition_pos W' hW')
    have hei : e 0 = i := by simp [e]
    have hcov (j : Fin (d + 1)) (b : Fin q) :
        covariance μ' (0,c) (j,b) = covariance μ (i,c) (e j,b) := by
      have h := covariance_reindex W hW e 0 j c b
      simpa [μ', μ, W', hei] using h
    have heq : crossRowAbs μ' 0 c = crossRowAbs μ i c := by
      unfold crossRowAbs
      have hji (j : Fin (d + 1)) : j = 0 ↔ e j = i := by
        rw [← hei, e.injective.eq_iff]
      simp_rw [hji, hcov]
      exact Equiv.sum_comp e (fun j => if j = i then 0 else
        ∑ b, |covariance μ (i,c) (j,b)|)
    have h := head_crossRow_covariance_bound W' hW' c
    have hhead : crossRowAbs μ' 0 c =
        ∑ x : Fin d × Fin q, |covariance μ' (0,c) (x.1.succ,x.2)| := by
      simp [crossRowAbs, Fin.sum_univ_succ, Fintype.sum_prod_type]
    change (∑ x : Fin d × Fin q, |covariance μ' (0,c) (x.1.succ,x.2)|) ≤
      4 * (d : ℝ) * mean μ' 0 c / (s + 1) at h
    rw [← hhead, heq] at h
    have hmean : mean μ' 0 c = mean μ i c := by
      have hm := marginal_reindex W hW e 0 c
      simpa [μ', μ, W', hei] using hm
    rw [hmean] at h
    simpa using h

end EdgeColoringMixing.WeightedInjection
