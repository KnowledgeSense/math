import EdgeColoringMixing.ConditionalInjections
import EdgeColoringMixing.MatrixTrickleDown
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

/-! Exact local walks of the finite weighted-injection measures. -/
namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- The off-diagonal joint occupancy; its diagonal is zero. -/
noncomputable def offDiagonalJoint (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) : ℝ :=
  if x = y then 0 else μ.expectation (fun σ => cell x.1 x.2 σ * cell y.1 y.2 σ)

/-- Joint occupancy and covariance differ by the diagonal and the exact rank-one term. -/
theorem offDiagonalJoint_eq_covariance (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) :
    offDiagonalJoint μ x y = covariance μ x y + mean μ x.1 x.2 * mean μ y.1 y.2 -
      if x = y then mean μ x.1 x.2 else 0 := by
  by_cases hxy : x = y
  · subst y
    rcases x with ⟨i,c⟩
    simp only [offDiagonalJoint, ite_true, covariance_diagonal]
    ring
  · simp only [offDiagonalJoint, hxy, ite_false, sub_zero, covariance,
      FiniteLaw.covariance_eq_mixed_moment, mean]
    ring

theorem offDiagonalJoint_nonneg (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) : 0 ≤ offDiagonalJoint μ x y := by
  unfold offDiagonalJoint
  split_ifs
  · rfl
  · exact μ.expectation_nonneg (fun σ => mul_nonneg (cell_nonneg _ _ σ) (cell_nonneg _ _ σ))

theorem offDiagonalJoint_symm (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) : offDiagonalJoint μ x y = offDiagonalJoint μ y x := by
  unfold offDiagonalJoint
  simp only [eq_comm, mul_comm]

theorem offDiagonalJoint_row_sum (μ : FiniteLaw (Injection d q)) (x : Fin d × Fin q) :
    ∑ y, offDiagonalJoint μ x y = ((d : ℝ) - 1) * mean μ x.1 x.2 := by
  simp_rw [offDiagonalJoint_eq_covariance]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, covariance_total,
    ← Finset.mul_sum, mean_total, Finset.sum_ite_eq, Finset.mem_univ, ite_true, zero_add]
  ring

theorem offDiagonalJoint_zero_of_inactive (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hy : y ∉ active μ) : offDiagonalJoint μ x y = 0 := by
  have hp := mean_eq_zero_of_not_active μ hy
  rw [offDiagonalJoint_eq_covariance, covariance_eq_zero_of_mean_zero μ x y hp, hp]
  by_cases hxy : x = y
  · subst x
    simp [hp]
  · simp [hxy]

/-- The local walk's state space is exactly its active cells. -/
abbrev ActiveCell (μ : FiniteLaw (Injection d q)) := {x : Fin d × Fin q // x ∈ active μ}

noncomputable instance activeCellFintype (μ : FiniteLaw (Injection d q)) : Fintype (ActiveCell μ) :=
  (active μ).fintypeCoeSort

noncomputable def localPi (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) : ℝ :=
  mean μ x.val.1 x.val.2 / d

noncomputable def localConductance (μ : FiniteLaw (Injection d q)) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  fun x y => offDiagonalJoint μ x.val y.val / ((d : ℝ) * ((d : ℝ) - 1))

noncomputable def localWalk (μ : FiniteLaw (Injection d q)) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  fun x y => offDiagonalJoint μ x.val y.val / (mean μ x.val.1 x.val.2 * ((d : ℝ) - 1))

theorem localPi_pos (μ : FiniteLaw (Injection d q)) (hd : 0 < d) (x : ActiveCell μ) :
    0 < localPi μ x := div_pos ((mem_active μ x.val).mp x.property) (by exact_mod_cast hd)

theorem localPi_sum (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    ∑ x, localPi μ x = 1 := by
  unfold localPi
  rw [← Finset.sum_div]
  have h : ∑ x : ActiveCell μ, mean μ x.val.1 x.val.2 = d := by
    calc
      _ = ∑ x ∈ active μ, mean μ x.1 x.2 :=
        (Finset.sum_subtype (active μ) (fun _ => Iff.rfl)
          (fun x => mean μ x.1 x.2)).symm
      _ = d := active_mean_total μ
  rw [h]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hd))

theorem localConductance_nonneg (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d)
    (x y : ActiveCell μ) : 0 ≤ localConductance μ x y := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (offDiagonalJoint_nonneg μ x.val y.val)
    (mul_nonneg (by linarith) (by linarith))

theorem localConductance_hermitian (μ : FiniteLaw (Injection d q)) :
    (localConductance μ).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, star_trivial, localConductance, offDiagonalJoint_symm μ y.val x.val]

theorem localConductance_row_sum (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d)
    (x : ActiveCell μ) : ∑ y, localConductance μ x y = localPi μ x := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsum : ∑ y : ActiveCell μ, offDiagonalJoint μ x.val y.val =
      ((d : ℝ) - 1) * mean μ x.val.1 x.val.2 := by
    rw [← Finset.sum_subtype (active μ) (fun _ => Iff.rfl)]
    rw [← offDiagonalJoint_row_sum μ x.val]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    exact offDiagonalJoint_zero_of_inactive μ x.val y hy
  simp only [localConductance, ← Finset.sum_div, hsum, localPi]
  field_simp [show (d : ℝ) - 1 ≠ 0 by linarith]

theorem localWalk_stochastic (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d)
    (x : ActiveCell μ) : ∑ y, localWalk μ x y = 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : mean μ x.val.1 x.val.2 ≠ 0 := ((mem_active μ x.val).mp x.property).ne'
  have hc := localConductance_row_sum μ hd x
  simp only [localConductance, ← Finset.sum_div, localPi] at hc
  simp only [localWalk, ← Finset.sum_div]
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hd0, hd1] at hc
  field_simp [hp, hd1]
  nlinarith

theorem localConductance_eq_diagonal_mul_walk (μ : FiniteLaw (Injection d q))
    (hd : 2 ≤ d) : localConductance μ = diagonal (localPi μ) * localWalk μ := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  ext x y
  have hp : mean μ x.val.1 x.val.2 ≠ 0 := ((mem_active μ x.val).mp x.property).ne'
  simp only [Matrix.diagonal_mul, localConductance, localPi, localWalk]
  field_simp

/-- Exact recovery of the full covariance from the local walk, including its diagonal. -/
theorem covariance_localWalk_identity (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    (covariance μ).submatrix Subtype.val Subtype.val =
      diagonal (fun x : ActiveCell μ => mean μ x.val.1 x.val.2) +
      ((d : ℝ) * ((d : ℝ) - 1)) •
        (localConductance μ - ((d : ℝ) / ((d : ℝ) - 1)) •
          vecMulVec (localPi μ) (localPi μ)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, vecMulVec_apply, localPi, localConductance,
    offDiagonalJoint_eq_covariance, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true]
    field_simp
    ring
  · have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    simp only [hxy, hv, ite_false]
    field_simp
    ring


/-- Positive compatible cells have positive joint probability, obtained from the
exact conditioned smaller injection law and its preserved row surplus. -/
theorem offDiagonalJoint_pos_of_compatible (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i j : Fin d) (c b : Fin q)
    (hic : 0 < W i c) (hjb : 0 < W j b) (hij : i ≠ j) (hcb : c ≠ b) :
    0 < offDiagonalJoint (law W hW.nonneg (partition_pos W hW)) (i,c) (j,b) := by
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
    have hkc : 0 < W' 0 c := by simpa [W', hei] using hic
    have hcond := head_conditionalMean_tail W' hW' c hkc k b
    rw [conditionalMean_reindex W hW e 0 k.succ c b] at hcond
    have hkj : e k.succ = j := by rw [hk]; simp [e]
    rw [hei, hkj] at hcond
    have htail : 0 < withoutColor (fun l : Fin d => W' l.succ) c k b := by
      simp only [withoutColor, Ne.symm hcb, ite_false, W', hkj]
      exact hjb
    have hm := (marginal_pos_iff _ (hW'.tail_withoutColor W' c) k b).mpr htail
    rw [← hcond] at hm
    have hp := (marginal_pos_iff W hW i c).mpr hic
    rw [conditionalMean_eq_mixed_div _ _ _ hp] at hm
    have hmoment : 0 < (law W hW.nonneg (partition_pos W hW)).expectation
        (fun σ => cell i c σ * cell j b σ) :=
      (div_pos_iff.mp hm).resolve_right (fun h => (not_lt_of_ge hp.le) h.2) |>.1
    have hne : (i,c) ≠ (j,b) := by intro h; exact hij (Prod.mk.inj h).1
    simpa only [offDiagonalJoint, hne, ite_false] using hmoment

/-- Surplus gives a positive cell avoiding any two specified colors. -/
theorem exists_positive_color_away_two (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d) (i : Fin d) (a b : Fin q) :
    ∃ c, 0 < W i c ∧ c ≠ a ∧ c ≠ b := by
  by_contra! h
  have hbound c : W i c ≤ (if c = a then (1 : ℝ) else 0) +
      (if c = b then (1 : ℝ) else 0) := by
    by_cases hca : c = a
    · subst c
      simp only [ite_true]
      split_ifs <;> linarith [hW.le_one i a]
    · by_cases hcb : c = b
      · subst c
        simp only [hca, ite_false, ite_true, zero_add]
        exact hW.le_one i b
      · simp only [hca, hcb, ite_false, zero_add]
        exact le_of_not_gt (fun hc => hcb (h c hc hca))
  have hm := (hW.row_mass i).trans (Finset.sum_le_sum (fun c _ => hbound c))
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hm
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith [hW.positive]

/-- Irreducibility of every injection local walk is proved by explicit paths
of length at most three in the positive-conductance graph. -/
theorem localConductance_connected (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d) :
    let μ := law W hW.nonneg (partition_pos W hW)
    ∀ x y : ActiveCell μ,
      Relation.ReflTransGen (fun a b => 0 < localConductance μ a b) x y := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hweight (x : ActiveCell μ) : 0 < W x.val.1 x.val.2 :=
    (marginal_pos_iff W hW _ _).mp ((mem_active μ _).mp x.property)
  have hedge (x y : ActiveCell μ) (hi : x.val.1 ≠ y.val.1) (hc : x.val.2 ≠ y.val.2) :
      0 < localConductance μ x y := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_pos (offDiagonalJoint_pos_of_compatible W hW _ _ _ _ (hweight x) (hweight y) hi hc)
    exact mul_pos (by linarith) (by linarith)
  have active_of_weight (i : Fin d) (c : Fin q) (hc : 0 < W i c) : (i,c) ∈ active μ :=
    (mem_active μ _).mpr ((marginal_pos_iff W hW i c).mpr hc)
  intro x y
  by_cases hxy : x = y
  · subst y
    exact Relation.ReflTransGen.refl
  by_cases hrow : x.val.1 = y.val.1
  · obtain ⟨j,hj⟩ : ∃ j : Fin d, j ≠ x.val.1 := by
      have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
      exact exists_ne x.val.1
    obtain ⟨b,hb,hbx,hby⟩ := exists_positive_color_away_two W hW hd j x.val.2 y.val.2
    let z : ActiveCell μ := ⟨(j,b), active_of_weight j b hb⟩
    have hxz := hedge x z (Ne.symm hj) (Ne.symm hbx)
    have hzy := hedge z y (by simpa [z, ← hrow] using hj) hby
    exact (Relation.ReflTransGen.single (r := fun a b => 0 < localConductance μ a b) hxz).trans (Relation.ReflTransGen.single (r := fun a b => 0 < localConductance μ a b) hzy)
  · by_cases hcolor : x.val.2 = y.val.2
    · obtain ⟨c,hc,hcx,-⟩ := exists_positive_color_away_two W hW hd x.val.1 x.val.2 x.val.2
      obtain ⟨b,hb,hbx,hbc⟩ := exists_positive_color_away_two W hW hd y.val.1 x.val.2 c
      let z : ActiveCell μ := ⟨(y.val.1,b), active_of_weight _ _ hb⟩
      let t : ActiveCell μ := ⟨(x.val.1,c), active_of_weight _ _ hc⟩
      have hxz := hedge x z hrow (Ne.symm hbx)
      have hzt := hedge z t (Ne.symm hrow) hbc
      have hty := hedge t y hrow (by simpa [hcolor] using hcx)
      exact (Relation.ReflTransGen.single (r := fun a b => 0 < localConductance μ a b) hxz).trans
        ((Relation.ReflTransGen.single (r := fun a b => 0 < localConductance μ a b) hzt).trans (Relation.ReflTransGen.single (r := fun a b => 0 < localConductance μ a b) hty))
    · exact Relation.ReflTransGen.single (hedge x y hrow hcolor)


/-- Positive diagonal square roots of the stationary distribution. -/
noncomputable def localStationary (μ : FiniteLaw (Injection d q)) : ActiveCell μ → ℝ :=
  fun x => Real.sqrt (localPi μ x)

noncomputable def localInverseRoot (μ : FiniteLaw (Injection d q)) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  diagonal (fun x => (localStationary μ x)⁻¹)

/-- The symmetric normalized walk on the actual active-cell state space. -/
noncomputable def normalizedWalk (μ : FiniteLaw (Injection d q)) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  localInverseRoot μ * localConductance μ * localInverseRoot μ

theorem localStationary_pos (μ : FiniteLaw (Injection d q)) (hd : 0 < d) (x : ActiveCell μ) :
    0 < localStationary μ x := Real.sqrt_pos.mpr (localPi_pos μ hd x)

theorem localStationary_sq (μ : FiniteLaw (Injection d q)) (hd : 0 < d) (x : ActiveCell μ) :
    localStationary μ x * localStationary μ x = localPi μ x :=
  Real.mul_self_sqrt (localPi_pos μ hd x).le

theorem localStationary_unit (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    localStationary μ ⬝ᵥ localStationary μ = 1 := by
  unfold dotProduct
  simp_rw [localStationary_sq μ hd]
  exact localPi_sum μ hd

theorem normalizedWalk_hermitian (μ : FiniteLaw (Injection d q)) :
    (normalizedWalk μ).IsHermitian := by
  simpa only [normalizedWalk, localInverseRoot, conjTranspose_eq_transpose_of_trivial,
    diagonal_transpose] using
    Matrix.isHermitian_mul_mul_conjTranspose (localInverseRoot μ) (localConductance_hermitian μ)

theorem localInverseRoot_stationary (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    localInverseRoot μ *ᵥ localStationary μ = (fun _ => 1) := by
  ext x
  simp only [localInverseRoot, mulVec_diagonal]
  exact inv_mul_cancel₀ (localStationary_pos μ hd x).ne'

theorem localInverseRoot_pi (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    localInverseRoot μ *ᵥ localPi μ = localStationary μ := by
  ext x
  simp only [localInverseRoot, mulVec_diagonal]
  rw [← localStationary_sq μ hd]
  field_simp

theorem normalizedWalk_stationary (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    normalizedWalk μ *ᵥ localStationary μ = localStationary μ := by
  have hd0 : 0 < d := by omega
  have hrow : localConductance μ *ᵥ (fun _ => 1) = localPi μ := by
    ext x
    simpa [mulVec, dotProduct] using localConductance_row_sum μ hd x
  simp only [normalizedWalk, ← mulVec_mulVec, localInverseRoot_stationary μ hd0,
    hrow, localInverseRoot_pi μ hd0]

theorem localInverseRoot_diagonal_pi (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    localInverseRoot μ * diagonal (localPi μ) * localInverseRoot μ = 1 := by
  ext x y
  simp only [localInverseRoot, diagonal_mul_diagonal, diagonal_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true]
    rw [← localStationary_sq μ hd]
    field_simp [(localStationary_pos μ hd x).ne']
  · simp only [hxy, ite_false]

theorem normalizedWalk_contractive (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    ((1 : Matrix (ActiveCell μ) (ActiveCell μ) ℝ) - normalizedWalk μ).PosSemidef := by
  have h := MatrixTrickleDown.conductance_laplacian_posSemidef
    (localConductance_hermitian μ) (localConductance_nonneg μ hd)
  simp_rw [localConductance_row_sum μ hd] at h
  have hh := h.mul_mul_conjTranspose_same (localInverseRoot μ)
  simpa only [conjTranspose_eq_transpose_of_trivial, localInverseRoot, diagonal_transpose,
    Matrix.mul_sub, Matrix.sub_mul,
    show diagonal (fun x => (localStationary μ x)⁻¹) * diagonal (localPi μ) *
      diagonal (fun x => (localStationary μ x)⁻¹) = 1 from
      localInverseRoot_diagonal_pi μ (by omega), normalizedWalk, localInverseRoot] using hh

/-- The simple stationary eigenspace follows from the explicit injection connectivity proof. -/
theorem normalizedWalk_connected (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d) :
    let μ := law W hW.nonneg (partition_pos W hW)
    ∀ v : ActiveCell μ → ℝ, localStationary μ ⬝ᵥ v = 0 →
      normalizedWalk μ *ᵥ v = v → v = 0 := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hd0 : 0 < d := by omega
  intro v huv hSv
  let z : ActiveCell μ → ℝ := localInverseRoot μ *ᵥ v
  have henergy : z ⬝ᵥ (diagonal (localPi μ) - localConductance μ) *ᵥ z = 0 := by
    have hK : (localInverseRoot μ)ᵀ = localInverseRoot μ := by simp [localInverseRoot]
    calc
      _ = v ⬝ᵥ (localInverseRoot μ * (diagonal (localPi μ) - localConductance μ) *
          localInverseRoot μ) *ᵥ v := by
        simp only [← mulVec_mulVec, z, dotProduct_mulVec]
        rw [← vecMul_transpose (localInverseRoot μ) v, hK]
      _ = v ⬝ᵥ ((1 : Matrix (ActiveCell μ) (ActiveCell μ) ℝ) - normalizedWalk μ) *ᵥ v := by
        rw [Matrix.mul_sub, Matrix.sub_mul, localInverseRoot_diagonal_pi μ hd0]
        rfl
      _ = 0 := by rw [sub_mulVec, one_mulVec, hSv, sub_self, dotProduct_zero]
  have hpz : localPi μ ⬝ᵥ z = 0 := by
    have hid : localPi μ ⬝ᵥ z = localStationary μ ⬝ᵥ v := by
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro x _
      simp only [z, localInverseRoot, mulVec_diagonal]
      rw [← localStationary_sq μ hd0]
      field_simp
    exact hid.trans huv
  have hz : z = 0 := by
    apply MatrixTrickleDown.conductance_energy_zero_of_orthogonal
      (localConductance_hermitian μ) (localConductance_nonneg μ hd)
      (localConductance_connected W hW hd) (localPi_sum μ hd0) hpz
    simpa only [localConductance_row_sum μ hd] using henergy
  ext x
  have hzx := congrFun hz x
  simp only [z, localInverseRoot, mulVec_diagonal, Pi.zero_apply] at hzx
  exact (mul_eq_zero.mp hzx).resolve_left (inv_ne_zero (localStationary_pos μ hd0 x).ne')


/-- The joint occupancy of three distinct cells, extended by zero when cells coincide. -/
noncomputable def offDiagonalTriple (μ : FiniteLaw (Injection d q))
    (x y z : Fin d × Fin q) : ℝ :=
  if x = y ∨ x = z ∨ y = z then 0 else
    μ.expectation (fun σ => cell x.1 x.2 σ * cell y.1 y.2 σ * cell z.1 z.2 σ)

theorem offDiagonalTriple_nonneg (μ : FiniteLaw (Injection d q)) (x y z : Fin d × Fin q) :
    0 ≤ offDiagonalTriple μ x y z := by
  unfold offDiagonalTriple
  split_ifs
  · rfl
  · exact μ.expectation_nonneg (fun σ => mul_nonneg
      (mul_nonneg (cell_nonneg _ _ σ) (cell_nonneg _ _ σ)) (cell_nonneg _ _ σ))

theorem offDiagonalTriple_cycle (μ : FiniteLaw (Injection d q)) (x y z : Fin d × Fin q) :
    offDiagonalTriple μ x y z = offDiagonalTriple μ y z x := by
  unfold offDiagonalTriple
  have hprop : (x = y ∨ x = z ∨ y = z) ↔ (y = z ∨ y = x ∨ z = x) := by aesop
  simp only [hprop]
  congr 1
  congr 1
  ext σ
  ring

theorem offDiagonalTriple_swap (μ : FiniteLaw (Injection d q)) (x y z : Fin d × Fin q) :
    offDiagonalTriple μ x y z = offDiagonalTriple μ x z y := by
  unfold offDiagonalTriple
  have hprop : (x = y ∨ x = z ∨ y = z) ↔ (x = z ∨ x = y ∨ z = y) := by aesop
  simp only [hprop]
  congr 1
  congr 1
  ext σ
  ring

private theorem triple_correction (μ : FiniteLaw (Injection d q))
    (x y z : Fin d × Fin q) (hxy : x ≠ y) :
    offDiagonalTriple μ x y z =
      μ.expectation (fun σ => cell x.1 x.2 σ * cell y.1 y.2 σ * cell z.1 z.2 σ) -
      (if z = x then offDiagonalJoint μ x y else 0) -
      (if z = y then offDiagonalJoint μ x y else 0) := by
  by_cases hzx : z = x
  · subst z
    have hid (σ : Injection d q) : cell x.1 x.2 σ * cell y.1 y.2 σ * cell x.1 x.2 σ =
        cell x.1 x.2 σ * cell y.1 y.2 σ := by
      calc
        _ = (cell x.1 x.2 σ) ^ 2 * cell y.1 y.2 σ := by ring
        _ = _ := by rw [cell_sq]
    simp only [offDiagonalTriple, offDiagonalJoint, hxy, hid,
      true_or, or_true, ite_true, ite_false, sub_self]
  · by_cases hzy : z = y
    · subst z
      have hid (σ : Injection d q) : cell x.1 x.2 σ * cell y.1 y.2 σ * cell y.1 y.2 σ =
          cell x.1 x.2 σ * cell y.1 y.2 σ := by
        rw [mul_assoc, ← pow_two, cell_sq]
      simp [offDiagonalTriple, offDiagonalJoint, hxy, hzx, hid]
    · simp [offDiagonalTriple, hxy, Ne.symm hzx, Ne.symm hzy, hzx, hzy]

theorem offDiagonalTriple_row_sum (μ : FiniteLaw (Injection d q)) (x y : Fin d × Fin q) :
    ∑ z, offDiagonalTriple μ x y z = ((d : ℝ) - 2) * offDiagonalJoint μ x y := by
  by_cases hxy : x = y
  · subst y
    simp [offDiagonalTriple, offDiagonalJoint]
  · simp_rw [triple_correction μ x y _ hxy]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← FiniteLaw.expectation_sum]
    have hsum (σ : Injection d q) :
        (∑ z : Fin d × Fin q, cell x.1 x.2 σ * cell y.1 y.2 σ * cell z.1 z.2 σ) =
        (d : ℝ) * (cell x.1 x.2 σ * cell y.1 y.2 σ) := by
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      simp only [row_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      ring
    simp only [hsum, FiniteLaw.expectation_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, offDiagonalJoint, hxy, ite_false]
    ring

theorem offDiagonalTriple_le_joint (μ : FiniteLaw (Injection d q)) (x y z : Fin d × Fin q) :
    offDiagonalTriple μ x y z ≤ offDiagonalJoint μ x y := by
  unfold offDiagonalTriple
  split_ifs with heq
  · exact offDiagonalJoint_nonneg μ x y
  · have hxy : x ≠ y := fun h => heq (Or.inl h)
    simp only [offDiagonalJoint, hxy, ite_false]
    apply μ.expectation_mono
    intro σ
    exact mul_le_of_le_one_right (mul_nonneg (cell_nonneg _ _ σ) (cell_nonneg _ _ σ))
      (cell_le_one _ _ σ)

theorem offDiagonalTriple_zero_of_inactive (μ : FiniteLaw (Injection d q))
    (x y z : Fin d × Fin q) (hz : z ∉ active μ) : offDiagonalTriple μ x y z = 0 := by
  apply le_antisymm _ (offDiagonalTriple_nonneg μ x y z)
  rw [offDiagonalTriple_swap μ x y z]
  exact (offDiagonalTriple_le_joint μ x z y).trans_eq (offDiagonalJoint_zero_of_inactive μ x z hz)

theorem active_offDiagonalTriple_row_sum (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) :
    ∑ z : ActiveCell μ, offDiagonalTriple μ x y z.val =
      ((d : ℝ) - 2) * offDiagonalJoint μ x y := by
  rw [← Finset.sum_subtype (active μ) (fun _ => Iff.rfl)]
  rw [← offDiagonalTriple_row_sum μ x y]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z _ hz
  exact offDiagonalTriple_zero_of_inactive μ x y z hz

/-- The embedded stationary distribution of the link obtained by occupying `x`. -/
noncomputable def linkPi (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) : ActiveCell μ → ℝ :=
  fun y => localWalk μ x y

/-- The embedded conductance matrix of the link obtained by occupying `x`. -/
noncomputable def linkConductance (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  fun y z => offDiagonalTriple μ x.val y.val z.val /
    (mean μ x.val.1 x.val.2 * ((d : ℝ) - 1) * ((d : ℝ) - 2))

theorem linkPi_nonneg (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) (x y : ActiveCell μ) :
    0 ≤ linkPi μ x y := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (offDiagonalJoint_nonneg μ x.val y.val)
    (mul_nonneg ((mem_active μ _).mp x.property).le (by linarith))

theorem linkPi_sum (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) (x : ActiveCell μ) :
    ∑ y, linkPi μ x y = 1 := localWalk_stochastic μ hd x

theorem linkConductance_hermitian (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) :
    (linkConductance μ x).IsHermitian := by
  ext y z
  simp only [conjTranspose_apply, star_trivial, linkConductance,
    offDiagonalTriple_swap μ x.val z.val y.val]

theorem linkConductance_row_sum (μ : FiniteLaw (Injection d q)) (hd : 3 ≤ d)
    (x y : ActiveCell μ) : ∑ z, linkConductance μ x y z = linkPi μ x y := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [linkConductance, ← Finset.sum_div, active_offDiagonalTriple_row_sum,
    linkPi, localWalk]
  field_simp [show (d : ℝ) - 2 ≠ 0 by linarith]

theorem localPi_mul_linkPi (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d)
    (x y : ActiveCell μ) : localPi μ x * linkPi μ x y = localConductance μ x y := by
  have h := congrFun (congrFun (localConductance_eq_diagonal_mul_walk μ hd) x) y
  simpa only [Matrix.diagonal_mul, linkPi] using h.symm

/-- First local-link identity, with zeros retained outside the link. -/
theorem average_linkPi (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) (y : ActiveCell μ) :
    ∑ x, localPi μ x * linkPi μ x y = localPi μ y := by
  simp_rw [localPi_mul_linkPi μ hd]
  have hs x : localConductance μ x y = localConductance μ y x := by
    exact congrFun (congrFun (localConductance_hermitian μ).eq y) x
  simp_rw [hs]
  exact localConductance_row_sum μ hd y

/-- Garland's exact average-conductance identity. -/
theorem average_linkConductance (μ : FiniteLaw (Injection d q)) (hd : 3 ≤ d) :
    (∑ x, localPi μ x • linkConductance μ x) = localConductance μ := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  ext y z
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have heach x : localPi μ x * linkConductance μ x y z =
      offDiagonalTriple μ y.val z.val x.val /
        ((d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) - 2)) := by
    have hp : mean μ x.val.1 x.val.2 ≠ 0 := ((mem_active μ _).mp x.property).ne'
    rw [localPi, linkConductance, offDiagonalTriple_cycle μ x.val y.val z.val]
    field_simp
  simp_rw [heach]
  rw [← Finset.sum_div, active_offDiagonalTriple_row_sum]
  unfold localConductance
  field_simp [show (d : ℝ) - 2 ≠ 0 by linarith]

/-- Garland's exact posterior second-moment identity, valid for every pair of colors. -/
theorem average_linkPi_rank_one (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    (∑ x, localPi μ x • vecMulVec (linkPi μ x) (linkPi μ x)) =
      localConductance μ * diagonal (fun x => (localPi μ x)⁻¹) * localConductance μ := by
  ext y z
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro x _
  have hp : localPi μ x ≠ 0 := (localPi_pos μ (by omega) x).ne'
  have hy := localPi_mul_linkPi μ hd x y
  have hz := localPi_mul_linkPi μ hd x z
  have hsym : localConductance μ y x = localConductance μ x y := by
    exact congrFun (congrFun (localConductance_hermitian μ).eq x) y
  rw [hsym, ← hy, ← hz]
  field_simp


noncomputable def normalizedLinkDiagonal (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  localInverseRoot μ * diagonal (linkPi μ x) * localInverseRoot μ

noncomputable def normalizedLinkConductance (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) :
    Matrix (ActiveCell μ) (ActiveCell μ) ℝ :=
  localInverseRoot μ * linkConductance μ x * localInverseRoot μ

noncomputable def normalizedLinkPi (μ : FiniteLaw (Injection d q)) (x : ActiveCell μ) :
    ActiveCell μ → ℝ := localInverseRoot μ *ᵥ linkPi μ x

private theorem root_congruence_rank_one (μ : FiniteLaw (Injection d q)) (v : ActiveCell μ → ℝ) :
    localInverseRoot μ * vecMulVec v v * localInverseRoot μ =
      vecMulVec (localInverseRoot μ *ᵥ v) (localInverseRoot μ *ᵥ v) := by
  rw [mul_vecMulVec, vecMulVec_mul]
  have hv : v ᵥ* localInverseRoot μ = localInverseRoot μ *ᵥ v := by
    rw [← mulVec_transpose, show (localInverseRoot μ)ᵀ = localInverseRoot μ by simp [localInverseRoot]]
  rw [hv]

private theorem average_root_congruence (μ : FiniteLaw (Injection d q))
    (F : ActiveCell μ → Matrix (ActiveCell μ) (ActiveCell μ) ℝ) :
    (∑ x, localPi μ x • (localInverseRoot μ * F x * localInverseRoot μ)) =
      localInverseRoot μ * (∑ x, localPi μ x • F x) * localInverseRoot μ := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Normalized first link identity, exactly on the positive-marginal state space. -/
theorem average_normalizedLinkDiagonal (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    (∑ x, localPi μ x • normalizedLinkDiagonal μ x) = 1 := by
  simp only [normalizedLinkDiagonal]
  rw [average_root_congruence]
  have hdiag : (∑ x, localPi μ x • diagonal (linkPi μ x)) = diagonal (localPi μ) := by
    ext y z
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, diagonal_apply]
    by_cases hyz : y = z
    · subst z
      simp only [ite_true]
      exact average_linkPi μ hd y
    · simp [hyz]
  rw [hdiag]
  exact localInverseRoot_diagonal_pi μ (by omega)

/-- Normalized Garland conductance identity. -/
theorem average_normalizedLinkConductance (μ : FiniteLaw (Injection d q)) (hd : 3 ≤ d) :
    (∑ x, localPi μ x • normalizedLinkConductance μ x) = normalizedWalk μ := by
  simp only [normalizedLinkConductance]
  rw [average_root_congruence, average_linkConductance μ hd]
  rfl

theorem localInverseRoot_sq (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    localInverseRoot μ * localInverseRoot μ = diagonal (fun x => (localPi μ x)⁻¹) := by
  simp only [localInverseRoot, diagonal_mul_diagonal]
  congr 1
  ext x
  rw [← localStationary_sq μ hd, _root_.mul_inv_rev]

/-- Normalized Garland second-moment identity. -/
theorem average_normalizedLinkPi_rank_one (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d) :
    (∑ x, localPi μ x • vecMulVec (normalizedLinkPi μ x) (normalizedLinkPi μ x)) =
      normalizedWalk μ * normalizedWalk μ := by
  simp only [normalizedLinkPi, ← root_congruence_rank_one, average_root_congruence,
    average_linkPi_rank_one μ hd, normalizedWalk]
  rw [← localInverseRoot_sq μ (by omega)]
  simp only [Matrix.mul_assoc]

theorem normalizedLinkDiagonal_stationary (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d)
    (x : ActiveCell μ) :
    normalizedLinkDiagonal μ x *ᵥ localStationary μ = normalizedLinkPi μ x := by
  have hid : diagonal (linkPi μ x) *ᵥ (fun _ => 1) = linkPi μ x := by ext y; simp only [mulVec_diagonal, mul_one]
  simp only [normalizedLinkDiagonal, normalizedLinkPi, ← mulVec_mulVec,
    localInverseRoot_stationary μ (by omega), hid]

theorem normalizedLinkConductance_stationary (μ : FiniteLaw (Injection d q)) (hd : 3 ≤ d)
    (x : ActiveCell μ) :
    normalizedLinkConductance μ x *ᵥ localStationary μ = normalizedLinkPi μ x := by
  have hid : linkConductance μ x *ᵥ (fun _ => 1) = linkPi μ x := by
    ext y
    simpa [mulVec, dotProduct] using linkConductance_row_sum μ hd x y
  simp only [normalizedLinkConductance, normalizedLinkPi, ← mulVec_mulVec,
    localInverseRoot_stationary μ (by omega), hid]

theorem normalizedLinkPi_dot_stationary (μ : FiniteLaw (Injection d q)) (hd : 2 ≤ d)
    (x : ActiveCell μ) : normalizedLinkPi μ x ⬝ᵥ localStationary μ = 1 := by
  rw [normalizedLinkPi, dotProduct_comm, ← dotProduct_transpose_mulVec,
    show (localInverseRoot μ)ᵀ = localInverseRoot μ by simp [localInverseRoot],
    localInverseRoot_stationary μ (by omega)]
  simpa [dotProduct] using linkPi_sum μ hd x


private theorem root_inverseRoot (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    diagonal (localStationary μ) * localInverseRoot μ = 1 := by
  simp only [localInverseRoot, diagonal_mul_diagonal]
  have hid : (fun x => localStationary μ x * (localStationary μ x)⁻¹) = fun _ => 1 := by
    ext x
    exact mul_inv_cancel₀ (localStationary_pos μ hd x).ne'
  rw [hid, diagonal_one]

private theorem inverseRoot_root (μ : FiniteLaw (Injection d q)) (hd : 0 < d) :
    localInverseRoot μ * diagonal (localStationary μ) = 1 := by
  simp only [localInverseRoot, diagonal_mul_diagonal]
  have hid : (fun x => (localStationary μ x)⁻¹ * localStationary μ x) = fun _ => 1 := by
    ext x
    exact inv_mul_cancel₀ (localStationary_pos μ hd x).ne'
  rw [hid, diagonal_one]

private theorem unnormalize_root_congruence (μ : FiniteLaw (Injection d q)) (hd : 0 < d)
    (A : Matrix (ActiveCell μ) (ActiveCell μ) ℝ) :
    diagonal (localStationary μ) * (localInverseRoot μ * A * localInverseRoot μ) *
      diagonal (localStationary μ) = A := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, root_inverseRoot μ hd, Matrix.one_mul,
    Matrix.mul_assoc, inverseRoot_root μ hd, Matrix.mul_one]

/-- The actual injection version of the one-step matrix trickle-down theorem.
Only the recursive matrix estimates remain as hypotheses: all local-walk, link,
normalization, and irreducibility facts are proved for the supplied `W`. -/
theorem injection_matrix_trickle_down_step (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hd : 3 ≤ d)
    (M : Matrix (ActiveCell (law W hW.nonneg (partition_pos W hW)))
      (ActiveCell (law W hW.nonneg (partition_pos W hW))) ℝ)
    (N : ActiveCell (law W hW.nonneg (partition_pos W hW)) →
      Matrix (ActiveCell (law W hW.nonneg (partition_pos W hW)))
        (ActiveCell (law W hW.nonneg (partition_pos W hW))) ℝ)
    (hM : M.IsHermitian) {α : ℝ} (hα : 1 ≤ α)
    (hlower : ∀ x, (N x -
      (linkConductance (law W hW.nonneg (partition_pos W hW)) x -
        α • vecMulVec (linkPi (law W hW.nonneg (partition_pos W hW)) x)
          (linkPi (law W hW.nonneg (partition_pos W hW)) x))).PosSemidef)
    (hupper : ∀ x, ((1 / (2 * α + 1)) •
      diagonal (linkPi (law W hW.nonneg (partition_pos W hW)) x) - N x).PosSemidef)
    (hrecursive : (M - α • (M *
      diagonal (fun x => (localPi (law W hW.nonneg (partition_pos W hW)) x)⁻¹) * M) -
      ∑ x, localPi (law W hW.nonneg (partition_pos W hW)) x • N x).PosSemidef) :
    (M - (localConductance (law W hW.nonneg (partition_pos W hW)) -
      (2 - 1 / α) • vecMulVec (localPi (law W hW.nonneg (partition_pos W hW)))
        (localPi (law W hW.nonneg (partition_pos W hW))))).PosSemidef := by
  let μ := law W hW.nonneg (partition_pos W hW)
  let K := localInverseRoot μ
  have hd2 : 2 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hKt : Kᵀ = K := by simp [K, localInverseRoot]
  have hnormalizedM : (K * M * K).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hKt] using
      Matrix.isHermitian_mul_mul_conjTranspose K hM
  have hnormalizedD x : (normalizedLinkDiagonal μ x).IsHermitian := by
    simpa only [normalizedLinkDiagonal, conjTranspose_eq_transpose_of_trivial, K,
      localInverseRoot, diagonal_transpose] using
      Matrix.isHermitian_mul_mul_conjTranspose K (Matrix.isHermitian_diagonal (linkPi μ x))
  have hnormalizedL x : (normalizedLinkConductance μ x).IsHermitian := by
    simpa only [normalizedLinkConductance, conjTranspose_eq_transpose_of_trivial, K,
      localInverseRoot, diagonal_transpose] using
      Matrix.isHermitian_mul_mul_conjTranspose K (linkConductance_hermitian μ x)
  have hlower' x : (K * N x * K - (normalizedLinkConductance μ x -
      α • vecMulVec (normalizedLinkPi μ x) (normalizedLinkPi μ x))).PosSemidef := by
    have h := (hlower x).mul_mul_conjTranspose_same K
    simpa only [conjTranspose_eq_transpose_of_trivial, hKt, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, K, root_congruence_rank_one,
      normalizedLinkConductance, normalizedLinkPi] using h
  have hupper' x : ((1 / (2 * α + 1)) • normalizedLinkDiagonal μ x - K * N x * K).PosSemidef := by
    have h := (hupper x).mul_mul_conjTranspose_same K
    simpa only [conjTranspose_eq_transpose_of_trivial, hKt, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, normalizedLinkDiagonal] using h
  have hsq : (K * M * K) * (K * M * K) =
      K * (M * diagonal (fun x => (localPi μ x)⁻¹) * M) * K := by
    rw [← localInverseRoot_sq μ hd0]
    simp only [K, Matrix.mul_assoc]
  have hrec' : (K * M * K - α • ((K * M * K) * (K * M * K)) -
      ∑ x, localPi μ x • (K * N x * K)).PosSemidef := by
    have h := hrecursive.mul_mul_conjTranspose_same K
    rw [hsq]
    simpa only [conjTranspose_eq_transpose_of_trivial, hKt, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, K] using h
  have hresult := MatrixTrickleDown.matrix_trickle_down_step
    (normalizedWalk_hermitian μ) hnormalizedM (normalizedWalk_stationary μ hd2)
    (localStationary_unit μ hd0) (normalizedWalk_contractive μ hd2)
    (normalizedWalk_connected W hW hd2) (localPi μ) (fun x => (localPi_pos μ hd0 x).le)
    (normalizedLinkDiagonal μ) (normalizedLinkConductance μ) (fun x => K * N x * K)
    (normalizedLinkPi μ) hnormalizedD hnormalizedL
    (normalizedLinkDiagonal_stationary μ hd2) (normalizedLinkConductance_stationary μ hd)
    (normalizedLinkPi_dot_stationary μ hd2) (average_normalizedLinkDiagonal μ hd2)
    (average_normalizedLinkConductance μ hd) (average_normalizedLinkPi_rank_one μ hd2)
    hα hlower' hupper' hrec'
  have hfinal := MatrixTrickleDown.unnormalize_conclusion (diagonal (localStationary μ)) hresult
  have hpi : diagonal (localStationary μ) *ᵥ localStationary μ = localPi μ := by
    ext x
    simp only [mulVec_diagonal, localStationary_sq μ hd0]
  simpa only [diagonal_transpose, K, normalizedWalk, unnormalize_root_congruence μ hd0, hpi] using hfinal

end EdgeColoringMixing.WeightedInjection





