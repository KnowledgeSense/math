import MainTheorems.Chollet.RankCoefficients.EdgeColumn
import MainTheorems.Chollet.Comparison
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace ResearchMain.Chollet

open Matrix RankCoefficients

variable {I : Type*} [Fintype I] [LinearOrder I]

abbrev DDEdge (I : Type*) [LinearOrder I] := {e : I × I // e.1 < e.2}

def ddRemainder (B : Matrix I I ℂ) (i : I) : ℝ :=
  (B i i).re - ∑ j ∈ Finset.univ.erase i, ‖B i j‖

def ddEdge (B : Matrix I I ℂ) (e : DDEdge I) : UnitEdge I :=
  entryEdge e.1.1 e.1.2 (ne_of_lt e.2) (B e.1.1 e.1.2)

def ddGram (B : Matrix I I ℂ) : Matrix I (I ⊕ DDEdge I) ℂ :=
  fromCols (diagonal (fun i => (Real.sqrt (ddRemainder B i) : ℂ)))
    (fun i e => (Real.sqrt ‖B e.1.1 e.1.2‖ : ℂ) * (ddEdge B e).column i)

theorem ordered_incident_sum (w : I → I → ℝ) (hw : ∀ i j, w i j = w j i) (i : I) :
    (∑ e : DDEdge I, if i = e.1.1 ∨ i = e.1.2 then w e.1.1 e.1.2 else 0) =
      ∑ j ∈ Finset.univ.erase i, w i j := by
  classical
  let f : I × I → ℝ := fun e => if i = e.1 ∨ i = e.2 then w e.1 e.2 else 0
  change (∑ e : DDEdge I, f e.1) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun e : I × I => e.1 < e.2))
    (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]
  have he : ∀ u v,
      (if u < v then f (u, v) else 0) =
        (if i = u then if i < v then w i v else 0 else 0) +
        (if i = v then if u < i then w u i else 0 else 0) := by
    intro u v
    by_cases hu : i = u <;> by_cases hv : i = v
    · subst u; subst v; simp [f]
    · subst u; simp [f, hv]
    · subst v; simp [f, hu]
    · simp [f, hu, hv]
  simp only [he, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j, if j = i then 0 else w i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hw j i]
      rcases lt_trichotomy i j with h | h | h
      · simp [h, not_lt_of_gt h, h.ne']
      · subst j; simp
      · simp [h, not_lt_of_gt h, h.ne]
    _ = ∑ j ∈ Finset.univ.erase i, if j = i then 0 else w i j := by
      symm
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro j hj hj'
      have hji : j = i := by
        by_contra hne
        exact hj' (Finset.mem_erase.mpr ⟨hne, hj⟩)
      simp [hji]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]

omit [Fintype I] in
theorem ddEdge_diagonal (B : Matrix I I ℂ) (e : DDEdge I) (i : I) :
    (‖B e.1.1 e.1.2‖ : ℂ) * (ddEdge B e).column i *
      star ((ddEdge B e).column i) =
        ((if i = e.1.1 ∨ i = e.1.2 then ‖B e.1.1 e.1.2‖ else 0 : ℝ) : ℂ) := by
  by_cases hl : i = e.1.1
  · subst i
    rw [show (ddEdge B e).column e.1.1 = 1 from UnitEdge.column_left _]
    simp
  · by_cases hr : i = e.1.2
    · subst i
      rw [show (ddEdge B e).column e.1.2 = unitPhase (B e.1.1 e.1.2) by
        exact UnitEdge.column_right _]
      have hu : unitPhase (B e.1.1 e.1.2) * star (unitPhase (B e.1.1 e.1.2)) = 1 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, unitPhase_norm]
        norm_num
      rw [mul_assoc, hu]
      simp
    · rw [UnitEdge.column_zero _ i hl hr]
      simp [hl, hr]

theorem ddEdge_sum_diagonal (B : Matrix I I ℂ) (hB : B.IsHermitian) (i : I) :
    (∑ e : DDEdge I, (‖B e.1.1 e.1.2‖ : ℂ) * (ddEdge B e).column i *
      star ((ddEdge B e).column i)) =
        ((∑ j ∈ Finset.univ.erase i, ‖B i j‖ : ℝ) : ℂ) := by
  simp only [ddEdge_diagonal, ← Complex.ofReal_sum]
  congr 1
  exact ordered_incident_sum (fun u v => ‖B u v‖) (by
    intro u v
    rw [← hB.apply u v, norm_star]) i

theorem ddEdge_sum_upper (B : Matrix I I ℂ) (i j : I) (hij : i < j) :
    (∑ e : DDEdge I, (‖B e.1.1 e.1.2‖ : ℂ) * (ddEdge B e).column i *
      star ((ddEdge B e).column j)) = B i j := by
  let e₀ : DDEdge I := ⟨(i, j), hij⟩
  rw [Finset.sum_eq_single e₀]
  · exact entryEdge_outer i j (ne_of_lt hij) (B i j)
  · intro e _ he
    by_cases hi : i = e.1.1
    · by_cases hj : j = e.1.2
      · exfalso
        apply he
        apply Subtype.ext
        exact Prod.ext hi.symm hj.symm
      · have hji : j ≠ e.1.1 := by rw [← hi]; exact hij.ne'
        rw [UnitEdge.column_zero _ j hji hj]
        simp
    · by_cases hj : i = e.1.2
      · have hji : j ≠ e.1.1 := by
          intro h
          have := e.2
          rw [← hj, ← h] at this
          exact lt_asymm hij this
        have hjj : j ≠ e.1.2 := by rw [← hj]; exact hij.ne'
        rw [UnitEdge.column_zero _ j hji hjj]
        simp
      · rw [UnitEdge.column_zero _ i hi hj]
        simp
  · simp

theorem sqrt_column_outer (w : ℝ) (hw : 0 ≤ w) (a b : ℂ) :
    ((Real.sqrt w : ℂ) * a) * star ((Real.sqrt w : ℂ) * b) =
      (w : ℂ) * a * star b := by
  have hs : (Real.sqrt w : ℂ) ^ 2 = (w : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hw
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt w : ℂ) ^ 2 * a * (starRingEnd ℂ) b := by ring
    _ = _ := by rw [hs]

theorem ddGram_entry (B : Matrix I I ℂ) (hd : ∀ i, 0 ≤ ddRemainder B i) (i j : I) :
    (ddGram B * (ddGram B).conjTranspose) i j =
      (diagonal (fun u => (ddRemainder B u : ℂ))) i j +
        ∑ e : DDEdge I, (‖B e.1.1 e.1.2‖ : ℂ) * (ddEdge B e).column i *
          star ((ddEdge B e).column j) := by
  let D := diagonal (fun u => (Real.sqrt (ddRemainder B u) : ℂ))
  let E : Matrix I (DDEdge I) ℂ := fun u e =>
    (Real.sqrt ‖B e.1.1 e.1.2‖ : ℂ) * (ddEdge B e).column u
  have hD : D * D.conjTranspose = diagonal (fun u => (ddRemainder B u : ℂ)) := by
    dsimp only [D]
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    apply congrArg diagonal
    funext u
    simp only [Pi.star_apply]
    simpa using sqrt_column_outer (ddRemainder B u) (hd u) 1 1
  change (fromCols D E * (fromCols D E).conjTranspose) i j = _
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
  change (D * D.conjTranspose) i j + (E * E.conjTranspose) i j = _
  rw [hD]
  apply congrArg (fun c : ℂ => diagonal (fun u => (ddRemainder B u : ℂ)) i j + c)
  simp only [E]
  apply Finset.sum_congr rfl
  intro e _
  exact sqrt_column_outer _ (norm_nonneg _) _ _

theorem ddGram_reconstruct (B : Matrix I I ℂ) (hB : B.IsHermitian)
    (hd : ∀ i, 0 ≤ ddRemainder B i) :
    ddGram B * (ddGram B).conjTranspose = B := by
  have hQ : (ddGram B * (ddGram B).conjTranspose).IsHermitian :=
    isHermitian_mul_conjTranspose_self (ddGram B)
  have hup : ∀ i j, i ≤ j → (ddGram B * (ddGram B).conjTranspose) i j = B i j := by
    intro i j hij
    rw [ddGram_entry B hd]
    rcases hij.eq_or_lt with h | h
    · subst j
      rw [ddEdge_sum_diagonal B hB, diagonal_apply_eq]
      have hi : B i i = ((B i i).re : ℂ) := by
        apply Complex.ext
        · rfl
        · have h := congrArg Complex.im (hB.apply i i)
          simp only [Complex.star_def, Complex.conj_im] at h
          simpa using (show (B i i).im = 0 by linarith)
      rw [hi]
      simp only [ddRemainder, Complex.ofReal_sub, sub_add_cancel]
    · rw [ddEdge_sum_upper B i j h, diagonal_apply_ne _ h.ne, zero_add]
  ext i j
  rcases le_total i j with h | h
  · exact hup i j h
  · rw [← hQ.apply i j, hup j i h, hB.apply i j]

end ResearchMain.Chollet
