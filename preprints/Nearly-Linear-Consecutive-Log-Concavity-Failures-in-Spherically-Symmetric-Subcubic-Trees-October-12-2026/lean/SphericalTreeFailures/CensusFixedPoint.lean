import SphericalTreeFailures.BroadcastBranching

/-! # Distributional fixed points of the census limit -/
namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable def rootMixtureLimit (p : unitInterval) (ω : BroadcastSpace) : ℝ :=
  if ω [] then censusLimit p true ω else censusLimit p false ω

noncomputable def censusMixtureLaw (p : unitInterval) : Measure ℝ :=
  ENNReal.ofReal (1 - (p : ℝ)) • censusLimitLaw p false +
    ENNReal.ofReal (p : ℝ) • censusLimitLaw p true

theorem measurable_censusLimit (p : unitInterval) (i : Bool) : Measurable (censusLimit p i) :=
  (Lp.stronglyMeasurable (censusLimitL2 p i)).measurable

theorem measurable_rootMixtureLimit (p : unitInterval) : Measurable (rootMixtureLimit p) :=
  Measurable.ite (show MeasurableSet {ω : BroadcastSpace | ω [] = true} from
    (measurable_pi_apply (X := fun _ : BinaryNode => Bool) []) (measurableSet_singleton true))
    (measurable_censusLimit p true) (measurable_censusLimit p false)

theorem input_root_false_probability (p : unitInterval) :
    broadcastMeasure p {ω : BroadcastSpace | ω [] = false} = ENNReal.ofReal (1 - (p : ℝ)) := by
  change broadcastMeasure p ((fun ω : BroadcastSpace => ω []) ⁻¹' {_}) = _
  have he := (broadcast_input_law p []).map_eq
  have hh := congrArg (fun μ : Measure Bool => μ {false}) he
  rw [Measure.map_apply (measurable_pi_apply (X := fun _ : BinaryNode => Bool) []) (measurableSet_singleton false)] at hh
  simpa [bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using hh

theorem input_root_true_probability (p : unitInterval) :
    broadcastMeasure p {ω : BroadcastSpace | ω [] = true} = ENNReal.ofReal (p : ℝ) := by
  change broadcastMeasure p ((fun ω : BroadcastSpace => ω []) ⁻¹' {_}) = _
  have he := (broadcast_input_law p []).map_eq
  have hh := congrArg (fun μ : Measure Bool => μ {true}) he
  rw [Measure.map_apply (measurable_pi_apply (X := fun _ : BinaryNode => Bool) []) (measurableSet_singleton true)] at hh
  simpa [bernoulliMeasure_apply, ENNReal.coe_nnreal_eq] using hh

theorem rootMixtureLimit_law (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    HasLaw (rootMixtureLimit p) (censusMixtureLaw p) (broadcastMeasure p) := by
  refine ⟨(measurable_rootMixtureLimit p).aemeasurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_rootMixtureLimit p) hs]
  have he : rootMixtureLimit p ⁻¹' s =
      ((fun ω : BroadcastSpace => ω []) ⁻¹' {false} ∩ censusLimit p false ⁻¹' s) ∪
      ((fun ω : BroadcastSpace => ω []) ⁻¹' {true} ∩ censusLimit p true ⁻¹' s) := by
    ext ω
    cases hh : ω [] <;> simp [rootMixtureLimit, hh]
  have hd : Disjoint
      ((fun ω : BroadcastSpace => ω []) ⁻¹' {false} ∩ censusLimit p false ⁻¹' s)
      ((fun ω : BroadcastSpace => ω []) ⁻¹' {true} ∩ censusLimit p true ⁻¹' s) := by
    rw [Set.disjoint_left]
    intro ω h0 h1
    have hh := h0.1.symm.trans h1.1
    cases hh
  have hm2 : MeasurableSet (((fun ω : BroadcastSpace => ω []) ⁻¹' {true}) ∩
      censusLimit p true ⁻¹' s) :=
    ((measurable_pi_apply (X := fun _ : BinaryNode => Bool) []) (measurableSet_singleton true)).inter ((measurable_censusLimit p true) hs)
  rw [he, measure_union hd hm2]
  rw [(rootInput_censusLimit_independent p hc false).measure_inter_preimage_eq_mul
    {false} s (measurableSet_singleton false) hs,
    (rootInput_censusLimit_independent p hc true).measure_inter_preimage_eq_mul
    {true} s (measurableSet_singleton true) hs]
  change broadcastMeasure p {ω | ω [] = false} * _ + broadcastMeasure p {ω | ω [] = true} * _ = _
  rw [input_root_false_probability, input_root_true_probability]
  simp only [censusMixtureLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    censusLimitLaw, Measure.map_apply (measurable_censusLimit p false) hs,
    Measure.map_apply (measurable_censusLimit p true) hs]

theorem sum_binaryLevel_append {A : Type*} [AddCommMonoid A] (f : BinaryNode → A) (h : ℕ) :
    ∑ v ∈ binaryLevel (h + 1), f v =
      ∑ v ∈ binaryLevel h, (f (v ++ [false]) + f (v ++ [true])) := by
  induction h generalizing f with
  | zero => rw [sum_binaryLevel_succ]; simp [binaryLevel]
  | succ h ih =>
    rw [sum_binaryLevel_succ, ih, sum_binaryLevel_succ]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [List.cons_append]
    abel

theorem census_subtree_sum (p : ℝ) (i : Bool) (h : ℕ) (ω : BroadcastSpace) :
    census p i (h + 1) ω =
      census p (broadcastState i ω [false]) h (subtreeInput false ω) +
      census p (broadcastState i ω [true]) h (subtreeInput true ω) := by
  unfold census
  rw [sum_binaryLevel_append, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [broadcastState_subtree, broadcastState_subtree]

theorem censusMartingale_subtree_sum (p : ℝ) (hp : 0 < p) (i : Bool) (h : ℕ) (ω : BroadcastSpace) :
    censusMartingale p i (h + 1) ω =
      -(censusMartingale p (broadcastState i ω [false]) h (subtreeInput false ω) +
        censusMartingale p (broadcastState i ω [true]) h (subtreeInput true ω)) / censusScale p := by
  unfold censusMartingale
  rw [census_subtree_sum, pow_succ]
  have hg : censusScale p ≠ 0 := by unfold censusScale; positivity
  field_simp

noncomputable def rootMixtureCensus (p : unitInterval) (h : ℕ) (ω : BroadcastSpace) : ℝ :=
  if ω [] then censusMartingale p true h ω else censusMartingale p false h ω

noncomputable def descendantCensus (p : unitInterval) (i : Bool) (h : ℕ) : BroadcastSpace → ℝ :=
  if i then censusMartingale p false h else rootMixtureCensus p h

noncomputable def descendantLimit (p : unitInterval) (i : Bool) : BroadcastSpace → ℝ :=
  if i then censusLimit p false else rootMixtureLimit p

noncomputable def descendantLaw (p : unitInterval) (i : Bool) : Measure ℝ :=
  if i then censusLimitLaw p false else censusMixtureLaw p

theorem measurable_censusMartingale (p : ℝ) (i : Bool) (h : ℕ) :
    Measurable (censusMartingale p i h) := by
  apply measurable_const.mul
  exact Finset.measurable_sum _ fun v _ => (measurable_occupation i v).sub measurable_const

theorem measurable_rootMixtureCensus (p : unitInterval) (h : ℕ) :
    Measurable (rootMixtureCensus p h) :=
  Measurable.ite (show MeasurableSet {ω : BroadcastSpace | ω [] = true} from
    (measurable_pi_apply (X := fun _ : BinaryNode => Bool) []) (measurableSet_singleton true))
    (measurable_censusMartingale p true h) (measurable_censusMartingale p false h)

theorem measurable_descendantCensus (p : unitInterval) (i : Bool) (h : ℕ) :
    Measurable (descendantCensus p i h) := by
  cases i
  · exact measurable_rootMixtureCensus p h
  · exact measurable_censusMartingale p false h

theorem measurable_descendantLimit (p : unitInterval) (i : Bool) :
    Measurable (descendantLimit p i) := by
  cases i
  · exact measurable_rootMixtureLimit p
  · exact measurable_censusLimit p false

theorem rootMixtureCensus_error_bound (p : unitInterval) (h : ℕ) :
    eLpNorm (rootMixtureCensus p h - rootMixtureLimit p) 2 (broadcastMeasure p) ≤
      eLpNorm (censusMartingale p false h - censusLimit p false) 2 (broadcastMeasure p) +
      eLpNorm (censusMartingale p true h - censusLimit p true) 2 (broadcastMeasure p) := by
  let s : Set BroadcastSpace := {ω | ω [] = true}
  have hs : MeasurableSet s := (measurable_pi_apply (X := fun _ : BinaryNode => Bool) []) (measurableSet_singleton true)
  have he : rootMixtureCensus p h - rootMixtureLimit p =
      sᶜ.indicator (censusMartingale p false h - censusLimit p false) +
      s.indicator (censusMartingale p true h - censusLimit p true) := by
    funext ω
    cases hh : ω [] <;> simp [rootMixtureCensus, rootMixtureLimit, s, hh]
  rw [he]
  exact (eLpNorm_add_le (by norm_num)).trans
    (add_le_add (eLpNorm_indicator_le _ hs.compl) (eLpNorm_indicator_le _ hs))

theorem rootMixtureCensus_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    Tendsto (fun h => eLpNorm (rootMixtureCensus p h - rootMixtureLimit p) 2 (broadcastMeasure p))
      atTop (𝓝 0) := by
  have ht := (census_tendsto_L2 p hc false).add (census_tendsto_L2 p hc true)
  simp only [add_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (rootMixtureCensus_error_bound p)

theorem descendantCensus_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    Tendsto (fun h => eLpNorm (descendantCensus p i h - descendantLimit p i) 2 (broadcastMeasure p))
      atTop (𝓝 0) := by
  cases i
  · exact rootMixtureCensus_tendsto_L2 p hc
  · exact census_tendsto_L2 p hc false

theorem branchCensus_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i b : Bool) :
    Tendsto (fun h => eLpNorm ((descendantCensus p i h - descendantLimit p i) ∘ subtreeInput b)
      2 (broadcastMeasure p)) atTop (𝓝 0) := by
  have he (h : ℕ) := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    ((measurable_descendantCensus p i h).sub (measurable_descendantLimit p i)).aestronglyMeasurable
    (broadcast_subtreeInput_preserving p b)
  simp_rw [he]
  exact descendantCensus_tendsto_L2 p hc i

theorem tendsto_L2_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf : Tendsto (fun h => eLpNorm (f h - F) 2 μ) atTop (𝓝 0))
    (hg : Tendsto (fun h => eLpNorm (g h - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun h => eLpNorm (f h + g h - (F + G)) 2 μ) atTop (𝓝 0) := by
  have ht := hf.add hg
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro h
  have he : f h + g h - (F + G) = (f h - F) + (g h - G) := by abel
  dsimp only
  rw [he]
  exact eLpNorm_add_le (by norm_num)

theorem tendsto_L2_const_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf : Tendsto (fun h => eLpNorm (f h - F) 2 μ) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun h => eLpNorm (c • f h - c • F) 2 μ) atTop (𝓝 0) := by
  simp only [← smul_sub, eLpNorm_const_smul]
  simpa using ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) hf (Or.inr enorm_ne_top)

theorem censusMartingale_descendant_sum (p : unitInterval) (hp : 0 < (p : ℝ)) (i : Bool) (h : ℕ) :
    censusMartingale p i (h + 1) = (-((censusScale p)⁻¹)) •
      (descendantCensus p i h ∘ subtreeInput false + descendantCensus p i h ∘ subtreeInput true) := by
  funext ω
  rw [censusMartingale_subtree_sum p hp i h ω]
  cases i <;> cases hf : ω [false] <;> cases ht : ω [true] <;>
    simp [descendantCensus, rootMixtureCensus, subtreeInput, div_eq_mul_inv, hf, ht] <;> ring

theorem censusLimit_branch_equation (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    censusLimit p i =ᵐ[broadcastMeasure p] (-((censusScale p)⁻¹)) •
      (descendantLimit p i ∘ subtreeInput false + descendantLimit p i ∘ subtreeInput true) := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have ht := tendsto_L2_const_mul (broadcastMeasure p)
    (tendsto_L2_add (broadcastMeasure p)
      (f := fun h => descendantCensus p i h ∘ subtreeInput false)
      (g := fun h => descendantCensus p i h ∘ subtreeInput true)
      (F := descendantLimit p i ∘ subtreeInput false)
      (G := descendantLimit p i ∘ subtreeInput true)
      (branchCensus_tendsto_L2 p hc i false) (branchCensus_tendsto_L2 p hc i true))
      (-((censusScale p)⁻¹))
  have he (h : ℕ) := censusMartingale_descendant_sum p hp i h
  simp_rw [← he] at ht
  have ht' := (census_tendsto_L2 p hc i).comp (tendsto_add_atTop_nat 1)
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ht')
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ht)

theorem descendantLimit_law (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    HasLaw (descendantLimit p i) (descendantLaw p i) (broadcastMeasure p) := by
  cases i
  · exact rootMixtureLimit_law p hc
  · exact ⟨(measurable_censusLimit p false).aemeasurable, rfl⟩

theorem branch_limits_independent (p : unitInterval) (i : Bool) :
    IndepFun (descendantLimit p i ∘ subtreeInput false)
      (descendantLimit p i ∘ subtreeInput true) (broadcastMeasure p) :=
  (broadcast_subtreeInput_independent p).comp
    (measurable_descendantLimit p i) (measurable_descendantLimit p i)

theorem branch_limit_law (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i b : Bool) :
    HasLaw (descendantLimit p i ∘ subtreeInput b) (descendantLaw p i) (broadcastMeasure p) :=
  (descendantLimit_law p hc i).comp
    ⟨(measurable_subtreeInput b).aemeasurable, (broadcast_subtreeInput_preserving p b).map_eq⟩

theorem branch_limits_joint_law (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    HasLaw (fun ω => (descendantLimit p i (subtreeInput false ω),
      descendantLimit p i (subtreeInput true ω)))
      ((descendantLaw p i).prod (descendantLaw p i)) (broadcastMeasure p) := by
  have hm (b : Bool) := (measurable_descendantLimit p i).comp (measurable_subtreeInput b)
  refine ⟨((hm false).prodMk (hm true)).aemeasurable, ?_⟩
  have he := (branch_limits_independent p i).map_prod_eq_prod_map_map
    (hm false).aemeasurable (hm true).aemeasurable
  rw [(branch_limit_law p hc i false).map_eq, (branch_limit_law p hc i true).map_eq] at he
  exact he

/-- The full distributional recursion, with actual independent child limits. -/
theorem censusLimitLaw_fixedPoint (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) (i : Bool) :
    censusLimitLaw p i =
      ((descendantLaw p i).prod (descendantLaw p i)).map
        (fun z : ℝ × ℝ => -(z.1 + z.2) / censusScale p) := by
  let pair : BroadcastSpace → ℝ × ℝ := fun ω =>
    (descendantLimit p i (subtreeInput false ω), descendantLimit p i (subtreeInput true ω))
  let f : ℝ × ℝ → ℝ := fun z => -(z.1 + z.2) / censusScale p
  have hm : Measurable pair :=
    ((measurable_descendantLimit p i).comp (measurable_subtreeInput false)).prodMk
      ((measurable_descendantLimit p i).comp (measurable_subtreeInput true))
  have hf : Measurable f := (measurable_fst.add measurable_snd).neg.div_const _
  have he : censusLimit p i =ᵐ[broadcastMeasure p] f ∘ pair := by
    filter_upwards [censusLimit_branch_equation p hc i] with ω hω
    change censusLimit p i ω = -(censusScale p)⁻¹ *
      (descendantLimit p i (subtreeInput false ω) + descendantLimit p i (subtreeInput true ω)) at hω
    dsimp [f, pair]
    rw [hω]
    ring
  calc
    censusLimitLaw p i = (broadcastMeasure p).map (f ∘ pair) := Measure.map_congr he
    _ = ((broadcastMeasure p).map pair).map f := (Measure.map_map hf hm).symm
    _ = _ := by rw [(branch_limits_joint_law p hc i).map_eq]

/-- Conditional on an occupied root, both child limits are independent copies of W₀. -/
theorem censusLimitLaw_fixedPoint_one (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    censusLimitLaw p true = ((censusLimitLaw p false).prod (censusLimitLaw p false)).map
      (fun z : ℝ × ℝ => -(z.1 + z.2) / censusScale p) :=
  censusLimitLaw_fixedPoint p hc true

/-- Conditional on a vacant root, both child limits are independent copies of
`(1-p) W₀ + p W₁`. -/
theorem censusLimitLaw_fixedPoint_zero (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2) :
    censusLimitLaw p false = ((censusMixtureLaw p).prod (censusMixtureLaw p)).map
      (fun z : ℝ × ℝ => -(z.1 + z.2) / censusScale p) :=
  censusLimitLaw_fixedPoint p hc false

end SphericalTreeFailures
