import R34.Transfer
import Mathlib.Data.Matrix.Basic
import R34.SchurChainEquiv

noncomputable section

namespace R34.ChargeSites

open MvPolynomial
open scoped BigOperators

abbrev RealMat := Matrix (Fin 3) (Fin 3) ℝ

def realUnitEntry (a b : Fin 3) : RealMat := fun i j => if i=a ∧ j=b then 1 else 0

def liftRealMatrix (A : RealMat) : Transfer.Mat := fun i j => C (A i j)

def allEqual {n : ℕ} (χ : Fin (n+1) → Bool) : Prop := ∀ i, χ i=χ 0

instance {n : ℕ} (χ : Fin (n+1) → Bool) : Decidable (allEqual χ) := inferInstanceAs (Decidable (∀ i, χ i=χ 0))

@[simp] theorem colorState_ne_zero (b : Bool) : Transfer.colorState b ≠ 0 := by
  cases b <;> decide

theorem matrix_ite_apply (p : Prop) [Decidable p] (A B : Transfer.Mat) (i j : Fin 3) :
    (if p then A else B) i j=if p then A i j else B i j := by
  by_cases hp : p <;> simp [hp]

def groupTensor (a : ℕ) (χ : Fin (a+1) → Bool) : RealMat :=
  ((a+2 : ℕ) : ℝ) • realUnitEntry 0 0+
    if allEqual χ then realUnitEntry (Transfer.colorState (!χ 0))
      (Transfer.colorState (!χ (Fin.last a))) else 0

def chargeWeight {n : ℕ} (χ : Fin n → Bool) : Poly := ∏ i, color (χ i)

theorem sum_chargeWeight (n : ℕ) : (∑ χ : Fin n → Bool, chargeWeight χ)=U^n := by
  unfold chargeWeight
  rw [← Fintype.prod_sum]
  simp [color, U]

theorem allEqual_cons (n : ℕ) (b : Bool) (χ : Fin n → Bool) :
    allEqual (Fin.cons b χ) ↔ χ=(fun _ => b) := by
  constructor
  · intro hχ
    apply funext
    intro i
    exact hχ i.succ
  · rintro rfl
    intro i
    refine Fin.cases ?_ ?_ i <;> simp

theorem sum_allEqual (n : ℕ) (F : (Fin (n+1) → Bool) → Poly) :
    (∑ χ, if allEqual χ then F χ else 0)=∑ b : Bool, F (fun _ => b) := by
  rw [sum_colors_succ]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [allEqual_cons]
  have hcons : (Fin.cons b (fun _ : Fin n => b) : Fin (n+1) → Bool)=(fun _ => b) := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  simp [hcons]

theorem lift_groupTensor (a : ℕ) (χ : Fin (a+1) → Bool) :
    liftRealMatrix (groupTensor a χ) =
      (C ((a+2 : ℕ) : ℝ) : Poly) • Transfer.unitEntry 0 0+
      if allEqual χ then Transfer.unitEntry (Transfer.colorState (!χ 0))
        (Transfer.colorState (!χ (Fin.last a))) else 0 := by
  apply Matrix.ext
  intro i j
  by_cases hall : allEqual χ <;>
    by_cases h00 : i=0 ∧ j=0 <;>
    by_cases hoc : i=Transfer.colorState (!χ 0) ∧ j=Transfer.colorState (!χ (Fin.last a)) <;>
    simp [liftRealMatrix, groupTensor, realUnitEntry, Transfer.unitEntry, hall, h00, hoc,
      Matrix.smul_apply, smul_eq_mul, map_add]

 theorem group_colored_sum (a : ℕ) :
    (∑ χ : Fin (a+1) → Bool, chargeWeight χ • liftRealMatrix (groupTensor a χ))=
      Transfer.normalizedMatrix (a+2) := by
  simp only [lift_groupTensor, smul_add, Finset.sum_add_distrib]
  have hv : (∑ χ : Fin (a+1) → Bool,
      chargeWeight χ • ((C ((a+2 : ℕ) : ℝ) : Poly) • Transfer.unitEntry 0 0))=
      (C ((a+2 : ℕ) : ℝ)*U^(a+1)) • Transfer.unitEntry 0 0 := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, sum_chargeWeight]
    ring
  have ho : (∑ χ : Fin (a+1) → Bool,
      chargeWeight χ • (if allEqual χ then Transfer.unitEntry (Transfer.colorState (!χ 0))
        (Transfer.colorState (!χ (Fin.last a))) else 0))=
      T^(a+1) • Transfer.unitEntry 1 1+S^(a+1) • Transfer.unitEntry 2 2 := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      matrix_ite_apply, Matrix.zero_apply, mul_ite, mul_zero]
    rw [sum_allEqual]
    simp [chargeWeight, color, Transfer.colorState]
    ring
  rw [hv, ho]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Transfer.normalizedMatrix, Transfer.normalizedWeight, Transfer.unitEntry,
      Matrix.smul_apply, smul_eq_mul, Transfer.U, Transfer.S, Transfer.T, U, S, T]

inductive ChargedSite
  | point
  | group (a : ℕ)

abbrev ChargedSite.size : ChargedSite → ℕ
  | .point => 1
  | .group a => a+1

theorem ChargedSite.size_pos (c : ChargedSite) : 0<c.size := by cases c <;> simp [ChargedSite.size]

def goodTensor (a : ℕ) (χ : Fin (a+1) → Bool) : RealMat :=
  (3 : ℝ) • realUnitEntry 0 0+
    realUnitEntry (Transfer.colorState (!χ 0)) (Transfer.colorState (!χ (Fin.last a)))

def ChargedSite.tensor (c : ChargedSite) (χ : Fin c.size → Bool) : RealMat :=
  match c with
  | .point => realUnitEntry (Transfer.colorState (χ 0)) (Transfer.colorState (χ 0))
  | .group a => if a=1 then goodTensor a χ else groupTensor a χ

def ChargedSite.colorWeight (c : ChargedSite) (χ : Fin c.size → Bool) : Poly :=
  match c with
  | .point => chargeWeight χ
  | .group a => chargeWeight χ *
      if a=1 then C (if χ 0=χ (Fin.last a) then (2 : ℝ) else 1) else 1

def ChargedSite.matrix : ChargedSite → Transfer.Mat
  | .point => Transfer.normalizedMatrix 0
  | .group a => if a=1 then Transfer.goodThree else Transfer.normalizedMatrix (a+2)

@[simp] theorem lift_realUnitEntry (a b : Fin 3) :
    liftRealMatrix (realUnitEntry a b)=Transfer.unitEntry a b := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=a ∧ j=b <;> simp [liftRealMatrix, realUnitEntry, Transfer.unitEntry, hij]

@[simp] theorem lift_add (A B : RealMat) :
    liftRealMatrix (A+B)=liftRealMatrix A+liftRealMatrix B := by
  apply Matrix.ext
  intro i j
  simp [liftRealMatrix]

@[simp] theorem lift_smul (r : ℝ) (A : RealMat) :
    liftRealMatrix (r • A)=(C r : Poly) • liftRealMatrix A := by
  apply Matrix.ext
  intro i j
  simp [liftRealMatrix, Matrix.smul_apply, smul_eq_mul, map_mul]

@[simp] theorem lift_goodTensor (a : ℕ) (χ : Fin (a+1) → Bool) :
    liftRealMatrix (goodTensor a χ) =
      (3 : Poly) • Transfer.unitEntry 0 0+
      Transfer.unitEntry (Transfer.colorState (!χ 0)) (Transfer.colorState (!χ (Fin.last a))) := by
  simp [goodTensor, map_ofNat]

theorem point_colored_sum :
    (∑ χ : Fin 1 → Bool, chargeWeight χ •
      liftRealMatrix (realUnitEntry (Transfer.colorState (χ 0)) (Transfer.colorState (χ 0))))=
      Transfer.normalizedMatrix 0 := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Equiv.funUnique, Matrix.sum_apply, chargeWeight, color,
      Transfer.normalizedMatrix, Transfer.normalizedWeight, Transfer.unitEntry, Transfer.colorState,
      Matrix.smul_apply, smul_eq_mul, Transfer.S, Transfer.T, S, T]

theorem goodThree_colored_sum :
    (∑ χ : Fin 2 → Bool,
      (chargeWeight χ*C (if χ 0=χ (Fin.last 1) then (2 : ℝ) else 1)) •
        liftRealMatrix (goodTensor 1 χ))=Transfer.goodThree := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
  unfold Transfer.goodThree
  apply Finset.sum_congr rfl
  intro c hc
  rcases c with ⟨b,d⟩
  cases b <;> cases d <;>
    simp [finTwoArrowEquiv, chargeWeight, Fin.prod_univ_succ, Transfer.pairSite,
    Transfer.color, color, Transfer.S, Transfer.T, S, T]

theorem ChargedSite.matrix_colored_sum (c : ChargedSite) :
    c.matrix=(∑ χ : Fin c.size → Bool, c.colorWeight χ • liftRealMatrix (c.tensor χ)) := by
  cases c with
  | point => exact point_colored_sum.symm
  | group a =>
    by_cases ha : a=1
    · subst a
      simpa [ChargedSite.matrix, ChargedSite.colorWeight, ChargedSite.tensor] using goodThree_colored_sum.symm
    · simpa [ChargedSite.matrix, ChargedSite.colorWeight, ChargedSite.tensor, ha] using (group_colored_sum a).symm

end R34.ChargeSites









