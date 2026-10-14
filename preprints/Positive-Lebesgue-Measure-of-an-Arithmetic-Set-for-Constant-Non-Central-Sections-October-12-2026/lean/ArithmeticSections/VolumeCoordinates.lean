import ArithmeticSections.SeedFiniteCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace ArithmeticSections
open MeasureTheory

noncomputable def omegaThree : ℝ := 4 * Real.pi / 3
noncomputable def volumeCoordinate (γ : ℝ) : ℝ := omegaThree * Real.tan (Real.pi * γ) ^ 3
noncomputable def doubledVolumeCoordinate (θ : ℝ) : ℝ := volumeCoordinate (θ / 2)

/-- The paper's original A↦γ_A, including the real cube root. -/
noncomputable def rotationOfVolume (A : ℝ) : ℝ :=
  Real.arctan ((A / omegaThree) ^ (1 / 3 : ℝ)) / Real.pi

/-- The actual Haddad–Ryabogin arithmetic set from Definition 2.2. -/
def arithmeticSet : Set ℝ := {A | 8 * omegaThree < A ∧ Irrational (rotationOfVolume A) ∧
  ∀ k : ℕ, 2 ≤ k → 0 < conditionGap (rotationOfVolume A) k}

noncomputable def seedVolume : ℝ := omegaThree * Real.tan (Real.pi * (4 + Real.sqrt 2) / 14) ^ 3

theorem omegaThree_pos : 0 < omegaThree := by unfold omegaThree; positivity

theorem seedVolume_eq : seedVolume = volumeCoordinate seedRotation := by
  unfold seedVolume volumeCoordinate seedRotation
  congr 2
  ring

theorem rotationOfVolume_volumeCoordinate {γ : ℝ} (hlo : 0 < γ) (hhi : γ < 1 / 2) :
    rotationOfVolume (volumeCoordinate γ) = γ := by
  have ha : 0 < Real.pi * γ := mul_pos Real.pi_pos hlo
  have ha' : Real.pi * γ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have htan : 0 ≤ Real.tan (Real.pi * γ) := (Real.tan_pos_of_pos_of_lt_pi_div_two ha ha').le
  unfold rotationOfVolume volumeCoordinate
  rw [mul_div_cancel_left₀ _ (ne_of_gt omegaThree_pos)]
  have hp : (Real.tan (Real.pi * γ) ^ 3) ^ (1 / 3 : ℝ) = Real.tan (Real.pi * γ) := by
    simpa only [Nat.cast_ofNat, one_div] using Real.pow_rpow_inv_natCast htan (by norm_num : (3 : ℕ) ≠ 0)
  rw [hp, Real.arctan_tan (by linarith [Real.pi_pos]) ha', mul_div_cancel_left₀ _ Real.pi_ne_zero]

theorem volumeCoordinate_pos {γ : ℝ} (hlo : 0 < γ) (hhi : γ < 1 / 2) :
    0 < volumeCoordinate γ := by
  have ha : 0 < Real.pi * γ := mul_pos Real.pi_pos hlo
  have ha' : Real.pi * γ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  unfold volumeCoordinate
  exact mul_pos omegaThree_pos (pow_pos (Real.tan_pos_of_pos_of_lt_pi_div_two ha ha') 3)

theorem volumeCoordinate_rotationOfVolume {A : ℝ} (hA : 0 < A) :
    volumeCoordinate (rotationOfVolume A) = A := by
  have hpos : 0 ≤ A / omegaThree := (div_pos hA omegaThree_pos).le
  unfold volumeCoordinate rotationOfVolume
  rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.tan_arctan]
  have hp : ((A / omegaThree) ^ (1 / 3 : ℝ)) ^ 3 = A / omegaThree := by
    simpa only [Nat.cast_ofNat, one_div] using Real.rpow_inv_natCast_pow hpos (by norm_num : (3 : ℕ) ≠ 0)
  rw [hp, mul_div_cancel₀ _ (ne_of_gt omegaThree_pos)]

/-- The original volume restriction implies the full rotation domain used by the proof. -/
theorem rotationOfVolume_bounds {A : ℝ} (hA : 8 * omegaThree < A) :
    1 / 3 < rotationOfVolume A ∧ rotationOfVolume A < 1 / 2 := by
  have hApos : 0 < A := by nlinarith [omegaThree_pos]
  have hp : 0 < A / omegaThree := div_pos hApos omegaThree_pos
  have hr : 0 ≤ (A / omegaThree) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hp.le _
  have hcub : ((A / omegaThree) ^ (1 / 3 : ℝ)) ^ 3 = A / omegaThree := by
    simpa only [Nat.cast_ofNat, one_div] using Real.rpow_inv_natCast_pow hp.le (by norm_num : (3 : ℕ) ≠ 0)
  have h8 : (8 : ℝ) < A / omegaThree := (lt_div_iff₀ omegaThree_pos).mpr hA
  have h2 : 2 < (A / omegaThree) ^ (1 / 3 : ℝ) := by
    by_contra hn
    have hh := pow_le_pow_left₀ hr (le_of_not_gt hn) 3
    norm_num [hcub] at hh
    linarith
  have hs : Real.sqrt 3 < (2 : ℝ) := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have harc := Real.arctan_strictMono (hs.trans h2)
  rw [Real.arctan_sqrt_three] at harc
  unfold rotationOfVolume
  constructor
  · apply (lt_div_iff₀ Real.pi_pos).mpr
    linarith
  · apply (div_lt_iff₀ Real.pi_pos).mpr
    linarith [Real.arctan_lt_pi_div_two ((A / omegaThree) ^ (1 / 3 : ℝ))]

theorem continuousAt_volumeCoordinate {γ : ℝ} (hlo : 0 < γ) (hhi : γ < 1 / 2) :
    ContinuousAt volumeCoordinate γ := by
  have ha' : Real.pi * γ < Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hc : Real.cos (Real.pi * γ) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], ha'⟩)
  unfold volumeCoordinate
  exact continuous_const.continuousAt.mul
    (((Real.continuousAt_tan.mpr hc).comp (continuous_const.continuousAt.mul continuous_id.continuousAt)).pow 3)

theorem continuousAt_doubledVolumeCoordinate {θ : ℝ} (hlo : 0 < θ) (hhi : θ < 1) :
    ContinuousAt doubledVolumeCoordinate θ := by
  have hq : ContinuousAt (fun x : ℝ => x / 2) θ := continuous_id.continuousAt.div_const 2
  have hv : ContinuousAt volumeCoordinate (θ / 2) :=
    continuousAt_volumeCoordinate (by linarith) (by linarith)
  exact ContinuousAt.comp (f := fun x : ℝ => x / 2) hv hq

theorem doubledVolumeCoordinate_injOn : Set.InjOn doubledVolumeCoordinate (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy he
  have hx' := rotationOfVolume_volumeCoordinate (by linarith [hx.1] : 0 < x / 2) (by linarith [hx.2] : x / 2 < 1 / 2)
  have hy' := rotationOfVolume_volumeCoordinate (by linarith [hy.1] : 0 < y / 2) (by linarith [hy.2] : y / 2 < 1 / 2)
  have hh := congrArg rotationOfVolume he
  change rotationOfVolume (volumeCoordinate (x / 2)) = rotationOfVolume (volumeCoordinate (y / 2)) at hh
  rw [hx', hy'] at hh
  linarith

theorem differentiableAt_rotationOfVolume {A : ℝ} (hA : 0 < A) :
    DifferentiableAt ℝ rotationOfVolume A := by
  have hdiv : DifferentiableAt ℝ (fun x : ℝ => x / omegaThree) A := differentiableAt_id.div_const _
  have hp : DifferentiableAt ℝ (fun x : ℝ => (x / omegaThree) ^ (1 / 3 : ℝ)) A :=
    hdiv.rpow_const (Or.inl (ne_of_gt (div_pos hA omegaThree_pos)))
  exact ((Real.differentiableAt_arctan _).comp A hp).div_const Real.pi

/-- Smooth injective volume coordinates preserve Borel sets and positivity of measure. -/
theorem volume_image_positive {E : Set ℝ} (hE : MeasurableSet E)
    (hdom : E ⊆ Set.Ioo (0 : ℝ) 1) (hpos : 0 < volume E) :
    MeasurableSet (doubledVolumeCoordinate '' E) ∧ 0 < volume (doubledVolumeCoordinate '' E) := by
  have hcont : ContinuousOn doubledVolumeCoordinate E := by
    intro θ hθ
    exact (continuousAt_doubledVolumeCoordinate (hdom hθ).1 (hdom hθ).2).continuousWithinAt
  refine ⟨hE.image_of_continuousOn_injOn hcont (doubledVolumeCoordinate_injOn.mono hdom), ?_⟩
  by_contra hn
  have hz : volume (doubledVolumeCoordinate '' E) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hdiff : DifferentiableOn ℝ (fun A => 2 * rotationOfVolume A) (doubledVolumeCoordinate '' E) := by
    rintro A ⟨θ, hθ, rfl⟩
    have hp : 0 < doubledVolumeCoordinate θ :=
      volumeCoordinate_pos (by linarith [(hdom hθ).1]) (by linarith [(hdom hθ).2])
    exact ((differentiableAt_rotationOfVolume hp).const_mul 2).differentiableWithinAt
  have hnull := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hz
  have he : (fun A => 2 * rotationOfVolume A) '' (doubledVolumeCoordinate '' E) = E := by
    ext θ
    constructor
    · rintro ⟨A, ⟨x, hx, rfl⟩, rfl⟩
      have hinv : 2 * rotationOfVolume (doubledVolumeCoordinate x) = x := by
        unfold doubledVolumeCoordinate
        rw [rotationOfVolume_volumeCoordinate (by linarith [(hdom hx).1]) (by linarith [(hdom hx).2])]
        ring
      change 2 * rotationOfVolume (doubledVolumeCoordinate x) ∈ E
      rwa [hinv]
    · intro hθ
      refine ⟨doubledVolumeCoordinate θ, ⟨θ, hθ, rfl⟩, ?_⟩
      change 2 * rotationOfVolume (volumeCoordinate (θ / 2)) = θ
      rw [rotationOfVolume_volumeCoordinate (by linarith [(hdom hθ).1] : 0 < θ / 2) (by linarith [(hdom hθ).2] : θ / 2 < 1 / 2)]
      ring
  rw [he] at hnull
  exact (ne_of_gt hpos) hnull

theorem seedVolume_threshold : 8 * omegaThree < seedVolume := by
  rw [seedVolume_eq]
  unfold volumeCoordinate
  have h := seed_tan_gt_two
  have hp : (2 : ℝ) ^ 3 < Real.tan (Real.pi * seedRotation) ^ 3 := by
    gcongr
  norm_num at hp
  nlinarith [omegaThree_pos]

theorem seedVolume_mem_arithmeticSet : seedVolume ∈ arithmeticSet := by
  have hi := rotationOfVolume_volumeCoordinate (by linarith [seedRotation_bounds.1] : 0 < seedRotation)
    seedRotation_bounds.2
  rw [← seedVolume_eq] at hi
  exact ⟨seedVolume_threshold, hi ▸ seedRotation_irrational, by simpa only [hi] using seed_all_conditions⟩

theorem measurable_conditionGap (k : ℕ) : Measurable (fun γ => conditionGap γ k) := by
  have hs := (continuous_firstDistance k).measurable
  have ht := (continuous_secondDistance k).measurable
  have hd := (continuous_oddDistance (k + 1)).measurable
  have hr : Measurable rotationRadius := by unfold rotationRadius; fun_prop
  unfold conditionGap minusDeviation plusDeviation sectionG
  exact hd.sub (((Real.measurable_arccos.comp ((hr.mul (Real.measurable_cos.comp hs)).inv)).sub
    (measurable_const.mul measurable_id)).neg.max
      ((Real.measurable_arccos.comp ((hr.mul
        ((Real.measurable_sin.comp (ht.sub hs)).div
          ((Real.measurable_sin.comp ht).sub (Real.measurable_sin.comp hs)))).inv)).sub
        (measurable_const.mul measurable_id)))

theorem measurable_rotationOfVolume : Measurable rotationOfVolume := by
  unfold rotationOfVolume
  fun_prop

/-- The original arithmetic set is itself Borel. -/
theorem measurableSet_arithmeticSet : MeasurableSet arithmeticSet := by
  have hi : MeasurableSet {γ : ℝ | Irrational γ} :=
    (Set.countable_range (fun q : ℚ => (q : ℝ))).measurableSet.compl
  have hpre : MeasurableSet {A : ℝ | Irrational (rotationOfVolume A)} :=
    measurable_rotationOfVolume hi
  have hc : MeasurableSet {A : ℝ | ∀ k : ℕ, 2 ≤ k → 0 < conditionGap (rotationOfVolume A) k} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt measurable_const ((measurable_conditionGap k).comp measurable_rotationOfVolume)
  exact measurableSet_Ioi.inter (hpre.inter hc)

end ArithmeticSections
