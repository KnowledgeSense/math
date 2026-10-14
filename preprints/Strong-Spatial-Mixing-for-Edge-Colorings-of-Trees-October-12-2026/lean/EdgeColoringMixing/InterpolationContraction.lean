import EdgeColoringMixing.RootedInterpolation
import EdgeColoringMixing.JacobianContraction
import EdgeColoringMixing.ColumnCovariance
import EdgeColoringMixing.ObservedMarginal
import EdgeColoringMixing.RootMessageDecay

set_option autoImplicit false

/-! Analytic control of the actual depth-cut interpolation on genuine finite trees. -/
namespace EdgeColoringMixing
open Finset WeightedInjection

/-- Polynomial continuity of the actual weighted-injection partition. -/
theorem continuousOn_partition_path {d q : ℕ} {S : Set ℝ}
    (W : ℝ → Fin d → Fin q → ℝ)
    (hW : ∀ i c, ContinuousOn (fun t => W t i c) S) :
    ContinuousOn (fun t => partition (W t)) S := by
  unfold partition weight
  apply continuousOn_finsetSum
  intro σ _
  exact continuousOn_finsetProd univ (fun i _ => hW i (σ i))

/-- Continuity of the exact recursion up to both endpoints of an interpolation. -/
theorem continuousOn_availabilityStep {d q : ℕ} {S : Set ℝ}
    (F : Finset (Fin q)) (A : ℝ → Fin d → Fin q → ℝ)
    (hA : ∀ i c, ContinuousOn (fun t => A t i c) S)
    (hZ : ∀ t ∈ S, partition (maskedWeights F (A t)) ≠ 0) (c : Fin q) :
    ContinuousOn (fun t => availabilityStep F (A t) c) S := by
  classical
  have hW : ∀ i b, ContinuousOn (fun t => maskedWeights F (A t) i b) S := by
    intro i b
    by_cases hb : b ∈ F <;> simp only [maskedWeights, hb, ite_true, ite_false]
    · exact continuousOn_const
    · exact hA i b
  have hWc : ∀ i b, ContinuousOn (fun t => withoutColor (maskedWeights F (A t)) c i b) S := by
    intro i b
    by_cases hb : b = c <;> simp only [withoutColor, hb, ite_true, ite_false]
    · exact continuousOn_const
    · exact hW i b
  by_cases hc : c ∈ F
  · simpa only [availabilityStep, hc, ite_true] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) S)
  · apply ((continuousOn_partition_path _ hWc).div (continuousOn_partition_path _ hW) hZ).congr
    intro t _
    simp only [availabilityStep, hc, ite_false, Pi.div_apply]

/-- The exact original retained-column factor at the palette and degree in use. -/
noncomputable def releaseColumnMultiplier (Δ q : ℕ) : ℝ :=
  let s := (q : ℝ) - 2 * Δ + 2
  let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
  1 + (columnError L (s + 1) Δ + 1 / (s + 1)) * ((Δ : ℝ) + s) / s

/-- Only the explicit scalar conditions from the original release are collected
here. The weighted-injection covariance bound is proved from them below. -/
structure ContractionBudget (Δ q : ℕ) (κ : ℝ) : Prop where
  degree : 2 ≤ Δ
  surplus : 0 < (q : ℝ) - 2 * Δ + 2
  rate : 0 ≤ κ
  first : 8 * harmonicHeight Δ ≤ ((q : ℝ) - 2 * Δ + 2) + 1
  second : let s := (q : ℝ) - 2 * Δ + 2
    4 * (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)) *
      (Δ : ℝ) * (harmonicHeight Δ)^2 ≤ (s + 1)^2
  third : let s := (q : ℝ) - 2 * Δ + 2
    columnError (22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2))
      (s + 1) Δ + 1 / (s + 1) ≤ 1 / 5
  gain : let s := (q : ℝ) - 2 * Δ + 2
    (releaseColumnMultiplier Δ q)^2 * (((Δ : ℝ) - 1) * Δ / (((Δ : ℝ) + s) * (s + 1))) ≤ κ^2

namespace ContractionBudget
variable {Δ q : ℕ} {κ : ℝ}

theorem multiplier_nonneg (P : ContractionBudget Δ q κ) : 0 ≤ releaseColumnMultiplier Δ q := by
  let s := (q : ℝ) - 2 * Δ + 2
  let L := 22 + 8 * ((q : ℝ) * ((Δ : ℝ) + s) / (s + 1)^2)
  have hs : 0 < s := P.surplus
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hb := columnError_nonneg (t := s + 1) hL (by have h := P.degree; omega : 1 ≤ Δ)
  change 0 ≤ 1 + (columnError L (s + 1) Δ + 1 / (s + 1)) * ((Δ : ℝ) + s) / s
  positivity

theorem covariance {d : ℕ} (P : ContractionBudget Δ q κ)
    (W : Fin d → Fin q → ℝ)
    (hW : RowSurplus W ((q : ℝ) - 2 * Δ + 2)) (hd : d ≤ Δ) :
    ((releaseColumnMultiplier Δ q) • columnBlock (law W hW.nonneg (partition_pos W hW)) -
      WeightedInjection.covariance (law W hW.nonneg (partition_pos W hW))).PosSemidef := by
  have h := column_covariance_bound W hW Δ (by have h := P.degree; omega) hd P.first P.second P.third
  simpa only [releaseColumnMultiplier, mul_div_assoc] using h

theorem gain_for_children {d : ℕ} (P : ContractionBudget Δ q κ) (hd : d + 1 ≤ Δ) :
    let s := (q : ℝ) - 2 * Δ + 2
    (releaseColumnMultiplier Δ q)^2 * ((d : ℝ) * Δ / (((Δ : ℝ) + s) * (s + 1))) ≤ κ^2 := by
  let s := (q : ℝ) - 2 * Δ + 2
  have hs : 0 < s := P.surplus
  have hd' : (d : ℝ) ≤ (Δ : ℝ) - 1 := by
    have h : (d : ℝ) + 1 ≤ Δ := by exact_mod_cast hd
    linarith
  apply le_trans _ P.gain
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg Δ)) (by positivity)

end ContractionBudget

namespace RootedCounting
universe u
variable {V : Type u} [Fintype V]

/-- The hypotheses all concern the actual tree and its two genuine coloring sets. -/
structure InterpolationData (Δ q : ℕ) (G : SimpleGraph V) (r : V)
    (F F' : V → Finset (Fin q)) : Prop where
  isTree : G.IsTree
  feasible : Nonempty (Coloring G q F)
  feasible' : Nonempty (Coloring G q F')
  budget : VertexBudget Δ q G F
  budget' : VertexBudget Δ q G F'
  rootBudget : RootBudget Δ q G r F
  rootBudget' : RootBudget Δ q G r F'
  surplus : 0 < (q : ℝ) - 2 * Δ + 2

namespace InterpolationData
variable {Δ q : ℕ} {G : SimpleGraph V} {r : V} {F F' : V → Finset (Fin q)}

theorem child (D : InterpolationData Δ q G r F F') (i : G.neighborSet r) :
    InterpolationData Δ q (childGraph r i) (childRoot r i)
      (fun v => F ((childEmbedding r i) v)) (fun v => F' ((childEmbedding r i) v)) :=
  ⟨childGraph_isTree D.isTree r i,
    child_coloring_nonempty D.isTree r q F D.feasible i,
    child_coloring_nonempty D.isTree r q F' D.feasible' i,
    D.budget.child r i, D.budget'.child r i,
    D.budget.child_root r i, D.budget'.child_root r i, D.surplus⟩

theorem domain (D : InterpolationData Δ q G r F F') (n : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : MessageDomain Δ q (interpolate n G r q F F' θ) :=
  interpolate_mem_domain n G D.isTree r q Δ F F' D.feasible D.feasible'
    D.budget D.budget' D.rootBudget D.rootBudget' D.surplus θ hθ

end InterpolationData

/-- The derivative is taken of the actual recursively defined coordinate function. -/
noncomputable def interpolateVelocity (n : ℕ) (G : SimpleGraph V) (r : V)
    (q : ℕ) (F F' : V → Finset (Fin q)) (θ : ℝ) (c : Fin q) : ℝ :=
  deriv (fun t => interpolate n G r q F F' t c) θ

/-- Continuity of every actual interpolation coordinate on the closed interval. -/
theorem interpolate_continuousOn (n : ℕ) :
    ∀ {V : Type u} [Fintype V] {Δ q : ℕ} {G : SimpleGraph V} {r : V}
      {F F' : V → Finset (Fin q)}, InterpolationData Δ q G r F F' →
      ∀ c, ContinuousOn (fun t => interpolate n G r q F F' t c) (Set.Icc (0 : ℝ) 1) := by
  induction n with
  | zero =>
    intro V _ Δ q G r F F' D c
    exact (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
      (continuousOn_id.mul continuousOn_const))
  | succ n ih =>
    intro V _ Δ q G r F F' D c
    apply continuousOn_availabilityStep
    · intro j b
      exact ih (D.child _) b
    · intro t ht
      exact (partition_pos _ (maskedWeights_rowSurplus _ _
        (fun j => (D.child _).domain n t ht) D.rootBudget D.surplus)).ne'

/-- Interior differentiability is inherited through the same exact recursion. -/
theorem interpolate_differentiableAt (n : ℕ) :
    ∀ {V : Type u} [Fintype V] {Δ q : ℕ} {G : SimpleGraph V} {r : V}
      {F F' : V → Finset (Fin q)}, InterpolationData Δ q G r F F' →
      ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∀ c,
      DifferentiableAt ℝ (fun t => interpolate n G r q F F' t c) θ := by
  induction n with
  | zero =>
    intro V _ Δ q G r F F' D θ hθ c
    exact (affine_cut_speed
      (rootAvailability_mem_domain D.isTree r q Δ F D.feasible D.rootBudget)
      (rootAvailability_mem_domain D.isTree r q Δ F' D.feasible' D.rootBudget') θ c).1.differentiableAt
  | succ n ih =>
    intro V _ Δ q G r F F' D θ hθ c
    let i := fun j : Fin (Fintype.card (G.neighborSet r)) =>
      (Fintype.equivFin (G.neighborSet r)).symm j
    let A := fun t j => interpolate n (childGraph r (i j)) (childRoot r (i j)) q
      (fun v => F ((childEmbedding r (i j)) v)) (fun v => F' ((childEmbedding r (i j)) v)) t
    let ξ := fun j c => deriv (fun t => A t j c) θ
    have hd : ∀ j c, HasDerivAt (fun t => A t j c) (ξ j c) θ :=
      fun j c => (ih (D.child (i j)) θ hθ c).hasDerivAt
    have hnear : ∀ j c, ∀ᶠ t in nhds θ, 0 ≤ A t j c := by
      intro j c
      filter_upwards [Icc_mem_nhds hθ.1 hθ.2] with t ht
      exact ((D.child (i j)).domain n t ht).nonneg c
    have hz : ∀ j c, A θ j c = 0 → ξ j c = 0 :=
      fun j c h => derivative_zero_at_zero (hd j c) (hnear j c) h
    let hW := maskedWeights_rowSurplus (F r) (A θ)
      (fun j => (D.child (i j)).domain n θ ⟨hθ.1.le, hθ.2.le⟩) D.rootBudget D.surplus
    exact (hasDerivAt_availabilityStep (F r) A ξ θ hW hd hz c).differentiableAt

theorem interpolate_hasDerivAt {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (c : Fin q) :
    HasDerivAt (fun t => interpolate n G r q F F' t c)
      (interpolateVelocity n G r q F F' θ c) θ :=
  (interpolate_differentiableAt n D θ hθ c).hasDerivAt

/-- Canonical finite indexing of the genuine children used by the recursion. -/
noncomputable def indexedChild (G : SimpleGraph V) (r : V)
    (j : Fin (Fintype.card (G.neighborSet r))) : G.neighborSet r :=
  (Fintype.equivFin (G.neighborSet r)).symm j

noncomputable def interpolateChildren (n : ℕ) (G : SimpleGraph V) (r : V) (q : ℕ)
    (F F' : V → Finset (Fin q)) (θ : ℝ) (j : Fin (Fintype.card (G.neighborSet r))) : Fin q → ℝ :=
  let i := indexedChild G r j
  interpolate n (childGraph r i) (childRoot r i) q
    (fun v => F ((childEmbedding r i) v)) (fun v => F' ((childEmbedding r i) v)) θ

noncomputable def interpolateChildrenVelocity (n : ℕ) (G : SimpleGraph V) (r : V) (q : ℕ)
    (F F' : V → Finset (Fin q)) (θ : ℝ) (j : Fin (Fintype.card (G.neighborSet r))) : Fin q → ℝ :=
  let i := indexedChild G r j
  interpolateVelocity n (childGraph r i) (childRoot r i) q
    (fun v => F ((childEmbedding r i) v)) (fun v => F' ((childEmbedding r i) v)) θ

theorem InterpolationData.children_domain {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin (Fintype.card (G.neighborSet r))) :
    MessageDomain Δ q (interpolateChildren n G r q F F' θ j) :=
  (D.child (indexedChild G r j)).domain n θ hθ

theorem InterpolationData.weights {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    RowSurplus (maskedWeights (F r) (interpolateChildren n G r q F F' θ))
      ((q : ℝ) - 2 * Δ + 2) :=
  maskedWeights_rowSurplus _ _ (D.children_domain n θ hθ) D.rootBudget D.surplus

/-- Exact derivative recursion for the actual interpolation velocity. -/
theorem interpolateVelocity_succ {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    interpolateVelocity (n + 1) G r q F F' θ =
      availabilityTangent (F r) (interpolateChildren n G r q F F' θ)
        (interpolateChildrenVelocity n G r q F F' θ)
        (D.weights n θ ⟨hθ.1.le, hθ.2.le⟩) := by
  have hd : ∀ j c, HasDerivAt (fun t => interpolateChildren n G r q F F' t j c)
      (interpolateChildrenVelocity n G r q F F' θ j c) θ := by
    intro j c
    exact interpolate_hasDerivAt (D.child (indexedChild G r j)) n θ hθ c
  have hz : ∀ j c, interpolateChildren n G r q F F' θ j c = 0 →
      interpolateChildrenVelocity n G r q F F' θ j c = 0 := by
    intro j c hzero
    apply derivative_zero_at_zero (hd j c) _ hzero
    filter_upwards [Icc_mem_nhds hθ.1 hθ.2] with t ht
    exact (D.children_domain n t ht j).nonneg c
  funext c
  exact (hasDerivAt_availabilityStep (F r) (interpolateChildren n G r q F F')
    (interpolateChildrenVelocity n G r q F F' θ) θ
    (D.weights n θ ⟨hθ.1.le, hθ.2.le⟩) hd hz c).deriv

/-- Every interior path derivative is tangent at both endpoints of the cube. -/
theorem interpolate_endpoint_tangent {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    EndpointTangent (interpolate n G r q F F' θ) (interpolateVelocity n G r q F F' θ) := by
  intro c hc
  have hd := interpolate_hasDerivAt D n θ hθ c
  rcases hc with hc | hc
  · apply derivative_zero_at_zero hd _ hc
    filter_upwards [Icc_mem_nhds hθ.1 hθ.2] with t ht
    exact (D.domain n t ht).nonneg c
  · have hneg := (hasDerivAt_const θ (1 : ℝ)).sub hd
    have hz : 1 - interpolate n G r q F F' θ c = 0 := by rw [hc]; ring
    have hn : ∀ᶠ t in nhds θ, 0 ≤ 1 - interpolate n G r q F F' t c := by
      filter_upwards [Icc_mem_nhds hθ.1 hθ.2] with t ht
      linarith [(D.domain n t ht).le_one c]
    have h := derivative_zero_at_zero hneg hn hz
    linarith

/-- Before contraction is used, each exact recursion costs at most the original K. -/
theorem interpolate_coordinate_speed (n : ℕ) :
    ∀ {V : Type u} [Fintype V] {Δ q : ℕ} {G : SimpleGraph V} {r : V}
      {F F' : V → Finset (Fin q)}, InterpolationData Δ q G r F F' → 2 ≤ Δ →
      ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∀ c,
      |interpolateVelocity n G r q F F' θ c| ≤
        (bufferSpeedConstant Δ q ((q : ℝ) - 2 * Δ + 2))^n := by
  induction n with
  | zero =>
    intro V _ Δ q G r F F' D hΔ θ hθ c
    have h := affine_cut_speed
      (rootAvailability_mem_domain D.isTree r q Δ F D.feasible D.rootBudget)
      (rootAvailability_mem_domain D.isTree r q Δ F' D.feasible' D.rootBudget') θ c
    change |deriv _ θ| ≤ _
    simp only [interpolate]
    rw [h.1.deriv, pow_zero]
    exact h.2
  | succ n ih =>
    intro V _ Δ q G r F F' D hΔ θ hθ c
    let s : ℝ := (q : ℝ) - 2 * Δ + 2
    let K := bufferSpeedConstant Δ q s
    have hΔ' : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    have hq : s + 1 ≤ q := by dsimp [s]; linarith
    have hd : Fintype.card (G.neighborSet r) ≤ Δ := by have h := D.rootBudget; unfold RootBudget at h; omega
    have hK : 0 ≤ K := by
      have hs : 0 < s := D.surplus
      unfold K bufferSpeedConstant
      positivity
    rw [interpolateVelocity_succ D n θ hθ]
    have h := availabilityTangent_speed_bound (F r) (interpolateChildren n G r q F F' θ)
      (interpolateChildrenVelocity n G r q F F' θ) (D.weights n θ ⟨hθ.1.le,hθ.2.le⟩)
      (fun j c => (D.children_domain n θ ⟨hθ.1.le,hθ.2.le⟩ j).nonneg c) (pow_nonneg hK n)
      (fun j c => ih (D.child (indexedChild G r j)) hΔ θ hθ c) c
    apply h.trans
    calc
      _ ≤ K * K^n := mul_le_mul_of_nonneg_right
        (speed_coefficient_le_bufferConstant (by omega : 1 ≤ Δ) hd D.surplus hq) (pow_nonneg hK n)
      _ = _ := by rw [pow_succ]; ring

/-- Every exactly generated interpolation message has the same pinned support
and the uniform positive lower bound on its unpinned coordinates. -/
theorem interpolate_generated_support {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (c : Fin q) :
    (c ∈ F r → interpolate (n + 1) G r q F F' θ c = 0) ∧
    (c ∉ F r → ((q : ℝ) - 2 * Δ + 2) / ((Δ : ℝ) + ((q : ℝ) - 2 * Δ + 2)) ≤
      interpolate (n + 1) G r q F F' θ c) := by
  classical
  have hd : Fintype.card (G.neighborSet r) ≤ Δ := by
    have h := D.rootBudget
    unfold RootBudget at h
    omega
  exact ⟨fun hc => by simp [interpolate, availabilityStep, hc],
    fun hc => availabilityStep_uniform_lower (F r) (interpolateChildren n G r q F F' θ)
      (D.weights n θ hθ) hd c hc⟩

/-- The original two-level energy bound for the actual finite-tree interpolation. -/
theorem interpolate_two_level_bound {Δ q : ℕ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (D : InterpolationData Δ q G r F F')
    (hΔ : 2 ≤ Δ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    arcsineNorm (interpolate 2 G r q F F' θ) (interpolateVelocity 2 G r q F F' θ) ≤
      bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2) := by
  classical
  let s : ℝ := (q : ℝ) - 2 * Δ + 2
  let a := s / ((Δ : ℝ) + s)
  let b := s * (s + 1) / ((q : ℝ) * ((Δ : ℝ) + s)^2)
  let K := bufferSpeedConstant Δ q s
  let Fc := fun j : Fin (Fintype.card (G.neighborSet r)) => F (indexedChild G r j).1
  let I : Finset (Fin q) := univ.filter (fun c => c ∉ F r ∧ ∃ j, c ∉ Fc j)
  have ht : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 < s := D.surplus
  have hΔ' : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hq : 0 < (q : ℝ) := by dsimp [s] at hs; linarith
  have ha : 0 < a := div_pos hs (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hs)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hd : Fintype.card (G.neighborSet r) ≤ Δ := by
    have h := D.rootBudget
    unfold RootBudget at h
    omega
  have hsupport (j : Fin (Fintype.card (G.neighborSet r))) (c : Fin q) :=
    interpolate_generated_support (D.child (indexedChild G r j)) 0 θ ht c
  have hbuf (c : Fin q) := availabilityStep_buffer (F r) Fc
    (interpolateChildren 1 G r q F F' θ) (D.weights 1 θ ht) hd
      (fun j c hc => (hsupport j c).1 hc) (fun j c hc => (hsupport j c).2 hc) c
  have hlo : ∀ c ∈ I, a ≤ interpolate 2 G r q F F' θ c := by
    intro c hc
    have hc' : c ∉ F r ∧ ∃ j, c ∉ Fc j := by simpa [I] using hc
    exact ((hbuf c).2.2 hc'.1 hc'.2).1
  have hhi : ∀ c ∈ I, interpolate 2 G r q F F' θ c ≤ 1 - b := by
    intro c hc
    have hc' : c ∉ F r ∧ ∃ j, c ∉ Fc j := by simpa [I] using hc
    exact ((hbuf c).2.2 hc'.1 hc'.2).2
  have hzero : ∀ c ∉ I, interpolateVelocity 2 G r q F F' θ c = 0 := by
    intro c hc
    apply interpolate_endpoint_tangent D 2 θ hθ c
    by_cases hcF : c ∈ F r
    · exact Or.inl ((hbuf c).1 hcF)
    · apply Or.inr
      apply (hbuf c).2.1 hcF
      intro j
      by_contra hj
      exact hc (by simp [I, hcF, show ∃ j, c ∉ Fc j from ⟨j,hj⟩])
  exact arcsineNorm.buffer_bound ha hb (sq_nonneg K) hlo hhi hzero
    (interpolate_coordinate_speed 2 D hΔ θ hθ)

/-- Above the two exact buffer levels, every additional genuine recursion
level contracts by the original rate. -/
theorem interpolate_arcsine_decay (m : ℕ) :
    ∀ {V : Type u} [Fintype V] {Δ q : ℕ} {κ : ℝ} {G : SimpleGraph V} {r : V}
      {F F' : V → Finset (Fin q)}, ContractionBudget Δ q κ →
      InterpolationData Δ q G r F F' → ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      arcsineNorm (interpolate (m + 2) G r q F F' θ)
        (interpolateVelocity (m + 2) G r q F F' θ) ≤
      κ^m * bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2) := by
  induction m with
  | zero =>
    intro V _ Δ q κ G r F F' P D θ hθ
    simpa only [zero_add, pow_zero, one_mul] using interpolate_two_level_bound D P.degree θ hθ
  | succ m ih =>
    intro V _ Δ q κ G r F F' P D θ hθ
    let s := (q : ℝ) - 2 * Δ + 2
    let E := bufferEnergyConstant Δ q s
    let A := interpolateChildren (m + 2) G r q F F' θ
    let ξ := interpolateChildrenVelocity (m + 2) G r q F F' θ
    let hW := D.weights (m + 2) θ ⟨hθ.1.le,hθ.2.le⟩
    have hd : Fintype.card (G.neighborSet r) + 1 ≤ Δ := by
      have h := D.rootBudget
      unfold RootBudget at h
      omega
    have hA (j : Fin (Fintype.card (G.neighborSet r))) :=
      D.children_domain (m + 2) θ ⟨hθ.1.le,hθ.2.le⟩ j
    have hplus : ∀ j c, A j c = 0 ∨ s / ((Δ : ℝ) + s) ≤ A j c := by
      intro j c
      by_cases hc : c ∈ F (indexedChild G r j).1
      · exact Or.inl ((interpolate_generated_support (D.child (indexedChild G r j))
          (m + 1) θ ⟨hθ.1.le,hθ.2.le⟩ c).1 hc)
      · exact Or.inr ((interpolate_generated_support (D.child (indexedChild G r j))
          (m + 1) θ ⟨hθ.1.le,hθ.2.le⟩ c).2 hc)
    have htan : ∀ j, EndpointTangent (A j) (ξ j) :=
      fun j => interpolate_endpoint_tangent (D.child (indexedChild G r j)) (m + 2) θ hθ
    have hE : 0 ≤ E := by unfold E bufferEnergyConstant; positivity
    have hM : 0 ≤ κ^m * E := mul_nonneg (pow_nonneg P.rate m) hE
    have hc := availabilityTangent_contraction (F r) A ξ hW
      (fun j c => (hA j).nonneg c) (fun j c => (hA j).le_one c) hplus htan
      P.multiplier_nonneg (P.covariance _ hW (by omega)) P.rate hM
      (P.gain_for_children hd)
      (fun j => ih P (D.child (indexedChild G r j)) θ hθ)
    rw [interpolateVelocity_succ D (m + 2) θ hθ]
    apply hc.trans_eq
    rw [pow_succ]
    ring

/-- Endpoint control for the two actual counting messages at an arbitrary cut depth. -/
theorem rootAvailability_decay {Δ q : ℕ} {κ : ℝ} {G : SimpleGraph V} {r : V}
    {F F' : V → Finset (Fin q)} (P : ContractionBudget Δ q κ)
    (D : InterpolationData Δ q G r F F') (n : ℕ) (hn : 2 ≤ n)
    (hagree : AgreeToDepth n G r q F F') :
    (∑ c, |rootAvailability (G := G) r q F c - rootAvailability (G := G) r q F' c|) ≤
      Real.sqrt q / 2 * (κ^(n - 2) * bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2)) := by
  have hspeed : ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      arcsineNorm (interpolate n G r q F F' θ) (interpolateVelocity n G r q F F' θ) ≤
        κ^(n - 2) * bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2) := by
    intro θ hθ
    have h := interpolate_arcsine_decay (n - 2) P D θ hθ
    simpa only [Nat.sub_add_cancel hn] using h
  have h := arcsine_path_endpoint_bound (interpolate n G r q F F')
    (interpolateVelocity n G r q F F') (D.domain n) (interpolate_continuousOn n D)
    (fun θ hθ c => interpolate_hasDerivAt D n θ hθ c)
    (fun θ hθ => interpolate_endpoint_tangent D n θ hθ) hspeed
  rw [interpolate_zero n G D.isTree r q F F' D.feasible,
    interpolate_one n G D.isTree r q F F' D.feasible' hagree] at h
  simpa only [abs_sub_comm] using h

end RootedCounting

universe u

/-- The actual-tree endpoint estimate is now derived from the release's scalar
conditions, with the weighted-injection covariance theorem fully discharged. -/
theorem rootMessageDecay_of_budget {Δ q : ℕ} {κ : ℝ} (P : ContractionBudget Δ q κ) :
    RootMessageDecay.{u} Δ q κ (bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2)) := by
  intro V _ G hG r F F' hf hf' hb hb' hr hr' n hn hagree
  exact RootedCounting.rootAvailability_decay P ⟨hG,hf,hf',hb,hb',hr,hr',P.surplus⟩ n hn hagree

end EdgeColoringMixing
