import R34.ReducedTensorCore
import R34.ReducedBoundary

noncomputable section

namespace R34.ReducedCharge

open MvPolynomial ChargeSites
open scoped BigOperators

theorem allEqual_cons_nonempty (n : ℕ) (b : Bool) (χ : Fin (n+1) → Bool) :
    allEqual (Fin.cons b χ) ↔ b=χ 0 ∧ allEqual χ := by
  rw [allEqual_cons]
  constructor
  · intro h
    subst χ
    simp [allEqual]
  · rintro ⟨h, hh⟩
    funext i
    exact (hh i).trans h.symm

theorem prod_localEqualZ_group (a : ℕ) (χ : Fin (a+1) → Bool) :
    (∏ e : Fin a, localEqualZ (.group a) χ e) = if allEqual χ then 1 else 0 := by
  change (∏ e : Fin a, if χ e.castSucc=χ e.succ then (1 : ℝ) else 0) = _
  induction a with
  | zero =>
    have h : allEqual χ := by intro i; fin_cases i; rfl
    simp [h]
  | succ a ih =>
    rw [← Fin.cons_self_tail χ]
    simp only [Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
      Fin.castSucc_succ]
    rw [ih]
    simp only [allEqual_cons_nonempty]
    by_cases h : χ 0=(Fin.tail χ) 0 <;> by_cases hh : allEqual (Fin.tail χ) <;>
      simp [h, hh]

-- Each charged site has a scalar option and a color option.
theorem weightedSiteTensor_eq_options (c : ChargedSite) (χ : Fin c.size → Bool) :
    weightedSiteTensor c χ = ∑ o : Bool,
      siteAmplitude c χ o • realUnitEntry (siteLeftState c χ o) (siteRightState c χ o) := by
  classical
  cases c with
  | point =>
    simp [weightedSiteTensor, siteExtraWeight, ChargedSite.tensor, siteAmplitude,
      siteCoefficient, internalAffine, ChargedSite.size, siteLeftState, siteRightState]
  | group a =>
    by_cases ha : a=1
    · subst a
      apply Matrix.ext
      intro i j
      by_cases h : χ 0=χ (Fin.last 1)
      all_goals simp [weightedSiteTensor, siteExtraWeight, ChargedSite.tensor, goodTensor,
        siteAmplitude, siteCoefficient, internalAffine, ChargedSite.size, siteLeftState,
        siteRightState, localEqualZ, internalChargeEndpoints, Matrix.smul_apply,
        Matrix.add_apply, realUnitEntry, Fin.last, h]
      all_goals split_ifs <;> simp_all [Fin.last] <;> ring
    · have hp := prod_localEqualZ_group a χ
      apply Matrix.ext
      intro i j
      by_cases hall : allEqual χ
      all_goals simp [weightedSiteTensor, siteExtraWeight, ChargedSite.tensor, groupTensor,
        siteAmplitude, siteCoefficient, internalAffine, ChargedSite.size, siteLeftState,
        siteRightState, Matrix.smul_apply, Matrix.add_apply, realUnitEntry, ha, hp, hall]
      all_goals ring

theorem kernel_entry_eq_ite (K : Kernel) :
    K.entry = fun i j => if i=0 then (if j=0 then K.d else K.p)
      else if j=0 then K.q else if i=j then K.a else K.b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem junction_eq_entry (c d : ChargedSite) (K : Kernel)
    (χ : Fin c.size → Bool) (ψ : Fin d.size → Bool) (o p : Bool) :
    (junctionAffine c d K o p).1 + (junctionAffine c d K o p).2 *
        (if χ ⟨c.size-1, by have hc := c.size_pos; omega⟩=ψ ⟨0, d.size_pos⟩ then 1 else 0) =
      K.entry (siteRightState c χ o) (siteLeftState d ψ p) := by
  rw [kernel_entry_eq_ite]
  cases c with
  | point =>
    cases d with
    | point =>
      cases hχ : χ 0 <;> cases hψ : ψ 0 <;> cases o <;> cases p
      all_goals simp [junctionAffine, sameKind, siteLeftState, siteRightState,
        Transfer.colorState, Kernel.g, ChargedSite.size, hχ, hψ]
    | group b =>
      cases hχ : χ 0 <;> cases hψ : ψ 0 <;> cases o <;> cases p
      all_goals simp [junctionAffine, sameKind, siteLeftState, siteRightState,
        Transfer.colorState, Kernel.g, ChargedSite.size, hχ, hψ]
  | group a =>
    cases d with
    | point =>
      cases hχ : χ (Fin.last a) <;> cases hψ : ψ 0 <;> cases o <;> cases p
      all_goals simp only [Fin.last] at hχ
      all_goals simp [junctionAffine, sameKind, siteLeftState, siteRightState,
        Transfer.colorState, Kernel.g, Fin.last, ChargedSite.size, hχ, hψ]
    | group b =>
      cases hχ : χ (Fin.last a) <;> cases hψ : ψ 0 <;> cases o <;> cases p
      all_goals simp only [Fin.last] at hχ
      all_goals simp [junctionAffine, sameKind, siteLeftState, siteRightState,
        Transfer.colorState, Kernel.g, Fin.last, ChargedSite.size, hχ, hψ]

theorem realUnitEntry_kernel (a b c d : Fin 3) (A : RealMat) :
    realUnitEntry a b * A * realUnitEntry c d = A b c • realUnitEntry a d := by
  classical
  funext i j
  by_cases hi : i=a <;> by_cases hj : j=d <;>
    simp [Matrix.mul_apply, realUnitEntry, Matrix.smul_apply, smul_eq_mul, ite_mul, mul_ite,
      hi, hj]

theorem optionAmplitude_last (c : ChargedSite) (χ : ChargeColorings (Chain.last c).sizes)
    (o : Bool) : optionAmplitude (.last c) χ o = siteAmplitude c χ.1 o := by
  rfl

theorem firstZ_equalZ (c : ChargedSite) (K : Kernel) (tail : Chain)
    (χ : ChargeColorings (Chain.cons c K tail).sizes) :
    firstZ (.cons c K tail) (equalZ (.cons c K tail) χ) = localEqualZ c χ.1 := by
  cases tail <;> rfl

theorem tailZ_equalZ (c : ChargedSite) (K : Kernel) (tail : Chain)
    (χ : ChargeColorings (Chain.cons c K tail).sizes) :
    tailZ c tail (equalZ (.cons c K tail) χ) = equalZ tail χ.2 := by
  cases tail <;> rfl

theorem junction_actual (c : ChargedSite) (K : Kernel) (tail : Chain)
    (χ : ChargeColorings (Chain.cons c K tail).sizes) (o : Options (.cons c K tail)) :
    (junctionAffine c tail.first K o.1 (firstOption tail o.2)).1 +
      (junctionAffine c tail.first K o.1 (firstOption tail o.2)).2 *
        junctionZ c tail (equalZ (.cons c K tail) χ) =
      K.entry (siteRightState c χ.1 o.1) (optionFirstState tail χ.2 o.2) := by
  cases tail with
  | last d => exact junction_eq_entry c d K χ.1 χ.2.1 o.1 o.2
  | cons d L rest => exact junction_eq_entry c d K χ.1 χ.2.1 o.1 o.2.1

theorem optionAmplitude_cons (c : ChargedSite) (K : Kernel) (tail : Chain)
    (χ : ChargeColorings (Chain.cons c K tail).sizes) (o : Options (.cons c K tail)) :
    optionAmplitude (.cons c K tail) χ o = siteAmplitude c χ.1 o.1 *
      K.entry (siteRightState c χ.1 o.1) (optionFirstState tail χ.2 o.2) *
        optionAmplitude tail χ.2 o.2 := by
  unfold optionAmplitude
  rw [affineEdgeProduct_cons, firstZ_equalZ, tailZ_equalZ, junction_actual,
    ← internal_product]
  simp only [siteCoefficients, siteAmplitude]
  ring

theorem options_sum_cons {R : Type} [AddCommMonoid R] (c : ChargedSite) (K : Kernel)
    (tail : Chain) (f : Options (.cons c K tail) → R) :
    (∑ o, f o) = ∑ o : Bool, ∑ p : Options tail, f (o,p) := by
  change (∑ o : Bool × Options tail, f o) = _
  exact Fintype.sum_prod_type _

-- Matrix multiplication joins neighboring options through their endpoint states.
theorem realTensor_eq_options (ch : Chain) (χ : ChargeColorings ch.sizes) :
    realTensor ch χ = ∑ o : Options ch, optionAmplitude ch χ o •
      realUnitEntry (optionFirstState ch χ o) (optionLastState ch χ o) := by
  induction ch with
  | last c =>
    simpa only [realTensor, optionAmplitude_last, optionFirstState, optionLastState]
      using weightedSiteTensor_eq_options c χ.1
  | cons c K tail ih =>
    rw [realTensor, weightedSiteTensor_eq_options, ih, options_sum_cons]
    simp only [Matrix.sum_mul, Matrix.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o ho
    apply Finset.sum_congr rfl
    intro p hp
    rw [optionAmplitude_cons]
    simp only [optionFirstState, optionLastState, Matrix.smul_mul, Matrix.mul_smul,
      realUnitEntry_kernel, smul_smul]
    congr 1
    ring

theorem realValue_eq_affineModel (ch : Chain) (χ : ChargeColorings ch.sizes)
    (L R : ℝ × ℝ) : realValue ch L R χ = affineModel ch L R (equalZ ch χ) :=
  realValue_eq_affineModel_of_tensor_options ch χ L R (realTensor_eq_options ch χ)

end R34.ReducedCharge

