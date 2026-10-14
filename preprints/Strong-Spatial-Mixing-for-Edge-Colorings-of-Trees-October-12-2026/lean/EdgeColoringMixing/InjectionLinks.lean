import EdgeColoringMixing.InjectionWalks

set_option autoImplicit false

/-! Exact identification of intrinsic local links with smaller weighted injections. -/
namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- Reindexing a weighted injection preserves every observable, not only marginals. -/
theorem expectation_reindex (W : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (e : Fin d ≃ Fin d) (f : Injection d q → ℝ) :
    let hW' : RowSurplus (fun i => W (e i)) s :=
      ⟨hW.positive, fun i c => hW.nonneg (e i) c, fun i c => hW.le_one (e i) c,
        fun i => hW.row_mass (e i)⟩
    (law (fun i => W (e i)) hW'.nonneg (partition_pos _ hW')).expectation f =
      (law W hW.nonneg (partition_pos W hW)).expectation
        (fun σ => f ((e.symm.embeddingCongr (Equiv.refl (Fin q))) σ)) := by
  dsimp only
  unfold FiniteLaw.expectation law
  simp only [partition_reindex]
  symm
  apply Fintype.sum_equiv (e.symm.embeddingCongr (Equiv.refl (Fin q)))
  intro σ
  rw [weight_reindex]

/-- The arbitrary-cell deletion used in the induction. The palette is preserved,
with the occupied color set to zero in every remaining row. -/
noncomputable def deleteRowColor (W : Fin (d + 1) → Fin q → ℝ)
    (i : Fin (d + 1)) (c : Fin q) : Fin d → Fin q → ℝ :=
  withoutColor (fun j => W ((Equiv.swap 0 i) j.succ)) c

/-- The embedding of a remaining cell into the original rows and colors. -/
def liftRemainingCell (i : Fin (d + 1)) (y : Fin d × Fin q) : Fin (d + 1) × Fin q :=
  ((Equiv.swap 0 i) y.1.succ, y.2)

theorem liftRemainingCell_injective (i : Fin (d + 1)) :
    Function.Injective (liftRemainingCell (q := q) i) := by
  intro y z h
  obtain ⟨hr,hc⟩ := Prod.mk.inj h
  have hrow := (Equiv.swap 0 i).injective hr
  exact Prod.ext (Fin.succ_injective _ hrow) hc

theorem liftRemainingCell_row_ne (i : Fin (d + 1)) (y : Fin d × Fin q) :
    (liftRemainingCell i y).1 ≠ i := by
  intro h
  have h' := congrArg (Equiv.swap 0 i) h
  simp only [liftRemainingCell, Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
  exact Fin.succ_ne_zero _ h'

theorem RowSurplus.deleteRowColor (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin (d + 1)) (c : Fin q) :
    RowSurplus (deleteRowColor W i c) s := by
  let W' := fun j => W ((Equiv.swap 0 i) j)
  have hW' : RowSurplus W' s :=
    ⟨hW.positive, fun j b => hW.nonneg _ b, fun j b => hW.le_one _ b,
      fun j => hW.row_mass _⟩
  exact hW'.tail_withoutColor W' c

/-- The posterior mean is exactly the marginal of the deleted weighted injection. -/
theorem deleteRowColor_mean (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin (d + 1)) (c : Fin q) (hic : 0 < W i c)
    (y : Fin d × Fin q) :
    mean (law (deleteRowColor W i c) (hW.deleteRowColor W i c).nonneg
      (partition_pos _ (hW.deleteRowColor W i c))) y.1 y.2 =
    posteriorMean (law W hW.nonneg (partition_pos W hW)) (i,c) (liftRemainingCell i y) := by
  let e := Equiv.swap (0 : Fin (d + 1)) i
  let W' := fun j => W (e j)
  have hW' : RowSurplus W' s :=
    ⟨hW.positive, fun j b => hW.nonneg _ b, fun j b => hW.le_one _ b,
      fun j => hW.row_mass _⟩
  have hc : 0 < W' 0 c := by simpa [W', e] using hic
  have h := head_conditionalMean_tail W' hW' c hc y.1 y.2
  rw [conditionalMean_reindex W hW e 0 y.1.succ c y.2] at h
  have hi : e 0 = i := by simp [e]
  rw [hi] at h
  have hne : (i,c) ≠ liftRemainingCell i y := by
    intro h
    exact liftRemainingCell_row_ne i y (congrArg Prod.fst h).symm
  rw [posteriorMean_eq _ _ _ ((mem_active _ _).mpr ((marginal_pos_iff W hW i c).mpr hic))]
  simp only [hne, ite_false, sub_zero]
  exact h.symm

/-- The intrinsic triple moment is the ordinary two-cell joint probability in the link. -/
theorem deleteRowColor_offDiagonalJoint (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (i : Fin (d + 1)) (c : Fin q) (hic : 0 < W i c)
    (y z : Fin d × Fin q) :
    offDiagonalJoint (law (deleteRowColor W i c) (hW.deleteRowColor W i c).nonneg
      (partition_pos _ (hW.deleteRowColor W i c))) y z =
      offDiagonalTriple (law W hW.nonneg (partition_pos W hW)) (i,c)
        (liftRemainingCell i y) (liftRemainingCell i z) /
          mean (law W hW.nonneg (partition_pos W hW)) i c := by
  by_cases hyz : y = z
  · subst z
    simp [offDiagonalJoint, offDiagonalTriple]
  let e := Equiv.swap (0 : Fin (d + 1)) i
  let W' := fun j => W (e j)
  have hW' : RowSurplus W' s :=
    ⟨hW.positive, fun j b => hW.nonneg _ b, fun j b => hW.le_one _ b,
      fun j => hW.row_mass _⟩
  have hc : 0 < W' 0 c := by simpa [W', e] using hic
  have h := head_condition_expectation W' hW' c hc (fun σ => cell y.1 y.2 σ * cell z.1 z.2 σ)
  rw [weightedExpectation_eq W' hW'.nonneg (partition_pos W' hW'),
    weightedExpectation_eq _ (hW'.tail_withoutColor W' c).nonneg
      (partition_pos _ (hW'.tail_withoutColor W' c))] at h
  rw [expectation_reindex W hW e, marginal_reindex W hW e 0 c] at h
  have hi : e 0 = i := by simp [e]
  rw [hi] at h
  have hxy : (i,c) ≠ liftRemainingCell i y := by
    intro h
    exact liftRemainingCell_row_ne i y (congrArg Prod.fst h).symm
  have hxz : (i,c) ≠ liftRemainingCell i z := by
    intro h
    exact liftRemainingCell_row_ne i z (congrArg Prod.fst h).symm
  have hlift : liftRemainingCell i y ≠ liftRemainingCell i z :=
    fun h => hyz (liftRemainingCell_injective i h)
  simp only [offDiagonalJoint, hyz, ite_false, offDiagonalTriple, hxy, hxz, hlift,
    false_or] 
  have hid (σ : Injection (d + 1) q) :
      cell 0 c ((e.symm.embeddingCongr (Equiv.refl (Fin q))) σ) *
        (cell y.1 y.2 (tailInjection ((e.symm.embeddingCongr (Equiv.refl (Fin q))) σ)) *
          cell z.1 z.2 (tailInjection ((e.symm.embeddingCongr (Equiv.refl (Fin q))) σ))) =
      cell i c σ * cell (liftRemainingCell i y).1 (liftRemainingCell i y).2 σ *
        cell (liftRemainingCell i z).1 (liftRemainingCell i z).2 σ := by
    change cell (e 0) c σ * (cell (e y.1.succ) y.2 σ * cell (e z.1.succ) z.2 σ) =
      cell i c σ * cell (e y.1.succ) y.2 σ * cell (e z.1.succ) z.2 σ
    rw [hi]
    ring
  simp_rw [hid] at h
  exact h.symm


/-- The posterior occupancy has the off-diagonal joint numerator. -/
theorem posteriorMean_eq_offDiagonalJoint (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hx : x ∈ active μ) :
    posteriorMean μ x y = offDiagonalJoint μ x y / mean μ x.1 x.2 := by
  have hp : mean μ x.1 x.2 ≠ 0 := ((mem_active μ _).mp hx).ne'
  rw [posteriorMean_eq μ x y hx, offDiagonalJoint_eq_covariance]
  rw [show covariance μ x y = covariance μ y x from FiniteLaw.covariance_symm μ _ _]
  split_ifs <;> field_simp <;> ring

theorem linkPi_eq_posteriorMean (μ : FiniteLaw (Injection d q)) (x y : ActiveCell μ) :
    linkPi μ x y = posteriorMean μ x.val y.val / ((d : ℝ) - 1) := by
  rw [posteriorMean_eq_offDiagonalJoint μ x.val y.val x.property]
  simp only [linkPi, localWalk, div_div]

theorem offDiagonalJoint_same_row (μ : FiniteLaw (Injection d q))
    (i : Fin d) (c b : Fin q) : offDiagonalJoint μ (i,c) (i,b) = 0 := by
  by_cases hcb : c = b
  · subst b
    simp [offDiagonalJoint]
  · simp [offDiagonalJoint, hcb, cell_mul_same_row i hcb]

theorem posteriorMean_same_row (μ : FiniteLaw (Injection d q))
    (x y : Fin d × Fin q) (hx : x ∈ active μ) (hrow : x.1 = y.1) :
    posteriorMean μ x y = 0 := by
  rw [posteriorMean_eq_offDiagonalJoint μ x y hx]
  obtain ⟨i,c⟩ := x
  obtain ⟨j,b⟩ := y
  dsimp at hrow
  subst j
  rw [offDiagonalJoint_same_row, zero_div]

theorem offDiagonalTriple_same_row (μ : FiniteLaw (Injection d q))
    (x y z : Fin d × Fin q) (hrow : x.1 = y.1) : offDiagonalTriple μ x y z = 0 := by
  apply le_antisymm _ (offDiagonalTriple_nonneg μ x y z)
  apply (offDiagonalTriple_le_joint μ x y z).trans_eq
  obtain ⟨i,c⟩ := x
  obtain ⟨j,b⟩ := y
  dsimp at hrow
  subst j
  exact offDiagonalJoint_same_row μ i c b

/-- Every cell outside the removed row has a unique remaining-cell representative. -/
theorem exists_liftRemainingCell (i : Fin (d + 1)) (y : Fin (d + 1) × Fin q)
    (hy : y.1 ≠ i) : ∃ z, liftRemainingCell i z = y := by
  let e := Equiv.swap (0 : Fin (d + 1)) i
  have he : e y.1 ≠ 0 := by
    intro h
    have h' := congrArg e h
    simp [e] at h'
    exact hy h'
  obtain ⟨j,hj⟩ := Fin.exists_succ_eq.mpr he
  refine ⟨(j,y.2), ?_⟩
  apply Prod.ext
  · change e j.succ = y.1
    rw [hj]
    simp [e]
  · rfl

/-- Zero-extension from the remaining full cell set to the parent's active state space. -/
noncomputable def remainingEmbedding (μ : FiniteLaw (Injection (d + 1) q))
    (i : Fin (d + 1)) : Matrix (ActiveCell μ) (Fin d × Fin q) ℝ :=
  fun y z => if y.val = liftRemainingCell i z then 1 else 0

theorem remainingEmbedding_congruence_apply (μ : FiniteLaw (Injection (d + 1) q))
    (i : Fin (d + 1)) (A : Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ)
    (y z : ActiveCell μ) (a b : Fin d × Fin q)
    (hy : y.val = liftRemainingCell i a) (hz : z.val = liftRemainingCell i b) :
    (remainingEmbedding μ i * A * (remainingEmbedding μ i)ᵀ) y z = A a b := by
  simp [Matrix.mul_apply, Matrix.transpose_apply, remainingEmbedding, hy, hz,
    (liftRemainingCell_injective i).eq_iff]

theorem remainingEmbedding_row_zero (μ : FiniteLaw (Injection (d + 1) q))
    (i : Fin (d + 1)) (y : ActiveCell μ) (hy : y.val.1 = i) (a : Fin d × Fin q) :
    remainingEmbedding μ i y a = 0 := by
  have hne : y.val ≠ liftRemainingCell i a := by
    intro h
    have he := congrArg Prod.fst h
    rw [hy] at he
    exact liftRemainingCell_row_ne i a he.symm
  simp [remainingEmbedding, hne]

/-- Entrywise identification gives a genuine PSD-preserving zero-extension. -/
theorem remainingEmbedding_congruence_eq (μ : FiniteLaw (Injection (d + 1) q))
    (i : Fin (d + 1)) (A : Matrix (Fin d × Fin q) (Fin d × Fin q) ℝ)
    (G : Matrix (ActiveCell μ) (ActiveCell μ) ℝ)
    (hleft : ∀ y z, y.val.1 = i → G y z = 0)
    (hright : ∀ y z, z.val.1 = i → G y z = 0)
    (hlift : ∀ y z a b, y.val = liftRemainingCell i a → z.val = liftRemainingCell i b →
      G y z = A a b) :
    remainingEmbedding μ i * A * (remainingEmbedding μ i)ᵀ = G := by
  ext y z
  by_cases hy : y.val.1 = i
  · rw [hleft y z hy]
    simp [Matrix.mul_apply, remainingEmbedding_row_zero μ i y hy]
  by_cases hz : z.val.1 = i
  · rw [hright y z hz]
    simp [Matrix.mul_apply, Matrix.transpose_apply, remainingEmbedding_row_zero μ i z hz]
  obtain ⟨a,ha⟩ := exists_liftRemainingCell i y.val hy
  obtain ⟨b,hb⟩ := exists_liftRemainingCell i z.val hz
  rw [remainingEmbedding_congruence_apply μ i A y z a b ha.symm hb.symm,
    hlift y z a b ha.symm hb.symm]


theorem deleted_linkPi (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x y : ActiveCell (law W hW.nonneg (partition_pos W hW))) (a : Fin d × Fin q)
    (hy : y.val = liftRemainingCell x.val.1 a) :
    linkPi (law W hW.nonneg (partition_pos W hW)) x y =
      mean (law (deleteRowColor W x.val.1 x.val.2)
        (hW.deleteRowColor W x.val.1 x.val.2).nonneg
        (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))) a.1 a.2 / d := by
  have hx := (marginal_pos_iff W hW _ _).mp ((mem_active _ _).mp x.property)
  rw [linkPi_eq_posteriorMean, hy, ← deleteRowColor_mean W hW _ _ hx]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

theorem deleted_linkConductance (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x y z : ActiveCell (law W hW.nonneg (partition_pos W hW))) (a b : Fin d × Fin q)
    (hy : y.val = liftRemainingCell x.val.1 a) (hz : z.val = liftRemainingCell x.val.1 b) :
    linkConductance (law W hW.nonneg (partition_pos W hW)) x y z =
      offDiagonalJoint (law (deleteRowColor W x.val.1 x.val.2)
        (hW.deleteRowColor W x.val.1 x.val.2).nonneg
        (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))) a b /
          ((d : ℝ) * ((d : ℝ) - 1)) := by
  have hx := (marginal_pos_iff W hW _ _).mp ((mem_active _ _).mp x.property)
  rw [deleteRowColor_offDiagonalJoint W hW _ _ hx]
  simp only [linkConductance, hy, hz, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, div_div]
  congr 1
  ring

/-- The smaller injection's centered covariance is exactly the intrinsic parent
link target after zero-extension, including all null cells. -/
theorem deleted_covarianceTarget_transfer (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s) (hd : 2 ≤ d)
    (x : ActiveCell (law W hW.nonneg (partition_pos W hW))) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
    remainingEmbedding μ x.val.1 *
      ((1 / ((d : ℝ) * ((d : ℝ) - 1))) •
        (covariance ν - diagonal (fun a => mean ν a.1 a.2))) *
      (remainingEmbedding μ x.val.1)ᵀ =
      linkConductance μ x - ((d : ℝ) / ((d : ℝ) - 1)) • vecMulVec (linkPi μ x) (linkPi μ x) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hzero (y : ActiveCell μ) (hy : y.val.1 = x.val.1) : linkPi μ x y = 0 := by
    rw [linkPi_eq_posteriorMean, posteriorMean_same_row μ _ _ x.property hy.symm, zero_div]
  apply remainingEmbedding_congruence_eq μ x.val.1
  · intro y z hy
    change linkConductance μ x y z - ((d : ℝ) / ((d : ℝ) - 1)) *
      (linkPi μ x y * linkPi μ x z) = 0
    simp only [hzero y hy, zero_mul, mul_zero, sub_zero, linkConductance,
      offDiagonalTriple_same_row μ _ _ _ hy.symm, zero_div]
  · intro y z hz
    change linkConductance μ x y z - ((d : ℝ) / ((d : ℝ) - 1)) *
      (linkPi μ x y * linkPi μ x z) = 0
    simp only [hzero z hz, mul_zero, sub_zero, linkConductance,
      offDiagonalTriple_swap μ x.val y.val z.val,
      offDiagonalTriple_same_row μ _ _ _ hz.symm, zero_div]
  · intro y z a b hy hz
    have hpya := deleted_linkPi W hW x y a hy
    have hpzb := deleted_linkPi W hW x z b hz
    have hcyz := deleted_linkConductance W hW x y z a b hy hz
    change linkConductance μ x y z - ((d : ℝ) / ((d : ℝ) - 1)) *
      (linkPi μ x y * linkPi μ x z) =
      (1 / ((d : ℝ) * ((d : ℝ) - 1))) *
        (covariance ν a b - diagonal (fun a => mean ν a.1 a.2) a b)
    rw [hpya, hpzb, hcyz, offDiagonalJoint_eq_covariance]
    simp only [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst b
      simp only [ite_true]
      field_simp
      ring
    · simp only [hab, ite_false, sub_zero]
      field_simp
      ring

/-- Posterior diagonal mass is the zero-extension of the actual smaller-law diagonal. -/
theorem deleted_diagonal_transfer (W : Fin (d + 1) → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus W s)
    (x : ActiveCell (law W hW.nonneg (partition_pos W hW))) :
    let μ := law W hW.nonneg (partition_pos W hW)
    let ν := law (deleteRowColor W x.val.1 x.val.2)
      (hW.deleteRowColor W x.val.1 x.val.2).nonneg
      (partition_pos _ (hW.deleteRowColor W x.val.1 x.val.2))
    remainingEmbedding μ x.val.1 * diagonal (fun a => mean ν a.1 a.2) *
      (remainingEmbedding μ x.val.1)ᵀ = diagonal (fun y => posteriorMean μ x.val y.val) := by
  dsimp only
  let μ := law W hW.nonneg (partition_pos W hW)
  have hx := (marginal_pos_iff W hW _ _).mp ((mem_active _ _).mp x.property)
  apply remainingEmbedding_congruence_eq μ x.val.1
  · intro y z hy
    by_cases hyz : y = z
    · subst z
      rw [diagonal_apply_eq, posteriorMean_same_row μ _ _ x.property hy.symm]
    · exact diagonal_apply_ne _ hyz
  · intro y z hz
    by_cases hyz : y = z
    · subst z
      rw [diagonal_apply_eq, posteriorMean_same_row μ _ _ x.property hz.symm]
    · exact diagonal_apply_ne _ hyz
  · intro y z a b hy hz
    have hyz : y = z ↔ a = b := by
      rw [Subtype.ext_iff, hy, hz]
      exact (liftRemainingCell_injective x.val.1).eq_iff
    simp only [Matrix.diagonal_apply, hyz]
    split_ifs
    · rw [hy, deleteRowColor_mean W hW _ _ hx]
    · rfl

end EdgeColoringMixing.WeightedInjection


