import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

def radialPrincipalMinor (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => A i.succ j.succ

def principalExtension (v : Fin 3 → ℝ) : Fin 4 → ℝ := ![0, v 0, v 1, v 2]

theorem radialPrincipalMinor_kernel {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ i j, A i j = A j i) (b : Fin 4 → ℝ) (hb0 : b 0 ≠ 0)
    (hb : A.mulVec b = 0)
    (hkernel : ∀ e, A.mulVec e = 0 → ∃ r : ℝ, e = r • b)
    (v : Fin 3 → ℝ) (hv : (radialPrincipalMinor A).mulVec v = 0) : v = 0 := by
  let e := principalExtension v
  have htail (i : Fin 3) : A.mulVec e i.succ = 0 := by
    have hi := congrFun hv i
    simpa [radialPrincipalMinor, e, principalExtension, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] using hi
  have hdot : dotProduct b (A.mulVec e) = 0 := by
    calc
      dotProduct b (A.mulVec e) = dotProduct (A.mulVec b) e := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hA j i]
        ring
      _ = 0 := by simp [hb]
  have hfirst : A.mulVec e 0 = 0 := by
    have h1 := htail 0
    have h2 := htail 1
    have h3 := htail 2
    change A.mulVec e 1 = 0 at h1
    change A.mulVec e 2 = 0 at h2
    change A.mulVec e 3 = 0 at h3
    simp only [dotProduct, Fin.sum_univ_four, h1, h2, h3, mul_zero, add_zero] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left hb0
  have he : A.mulVec e = 0 := by
    ext i
    fin_cases i
    · exact hfirst
    · exact htail 0
    · exact htail 1
    · exact htail 2
  obtain ⟨r, hr⟩ := hkernel e he
  have hr0 : r = 0 := by
    have h := congrFun hr 0
    change 0 = r * b 0 at h
    exact (mul_eq_zero.mp h.symm).resolve_right hb0
  rw [hr0, zero_smul] at hr
  ext i
  have h := congrFun hr i.succ
  fin_cases i <;> simpa [e, principalExtension] using h

theorem radialPrincipalMinor_det_ne_zero {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : ∀ i j, A i j = A j i) (b : Fin 4 → ℝ) (hb0 : b 0 ≠ 0)
    (hb : A.mulVec b = 0)
    (hkernel : ∀ e, A.mulVec e = 0 → ∃ r : ℝ, e = r • b) :
    (radialPrincipalMinor A).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  have hv : (radialPrincipalMinor A).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hz := radialPrincipalMinor_kernel hA b hb0 hb hkernel (v - w) hv
  exact sub_eq_zero.mp hz

end

end ResearchMain.DiagonalSchatten
