import MainTheorems.Chollet.RankCoefficients.EdgeNormalForm
import MainTheorems.Chollet.RankCoefficients.LinearAction

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

def unitPhase (b : ℂ) : ℂ := if b = 0 then 1 else star b / (‖b‖ : ℂ)

theorem unitPhase_norm (b : ℂ) : ‖unitPhase b‖ = 1 := by
  by_cases hb : b = 0
  · simp [unitPhase, hb]
  · have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    simp [unitPhase, hb, Complex.norm_real, hn]

theorem unitPhase_entry (b : ℂ) : (‖b‖ : ℂ) * star (unitPhase b) = b := by
  by_cases hb : b = 0
  · simp [unitPhase, hb]
  · have hn : (‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
    simp only [unitPhase, ite_eq_right hb]
    rw [star_div₀, star_star]
    have hr : star (‖b‖ : ℂ) = (‖b‖ : ℂ) := by simp
    rw [hr]
    field_simp

def entryEdge (i j : I) (hij : i ≠ j) (b : ℂ) : UnitEdge I where
  left := i
  right := j
  distinct := hij
  first := 1
  second := unitPhase b
  first_unit := by simp
  second_unit := unitPhase_norm b

def UnitEdge.column (e : UnitEdge I) : I → ℂ :=
  fun i => (if i = e.left then e.first else 0) + (if i = e.right then e.second else 0)

theorem UnitEdge.linearForm_column (e : UnitEdge I) :
    linearForm e.column = e.polynomial := by
  have hs : ∀ (i j : I) (c : ℂ),
      scalar (I := I) (if i = j then c else 0) = if i = j then scalar (I := I) c else 0 := by
    intro i j c
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
    · simp only [ite_eq_right hij, scalar_zero]
  simp only [linearForm, UnitEdge.column, UnitEdge.polynomial, scalar_add,
    hs, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [Fintype I] in
theorem UnitEdge.column_left (e : UnitEdge I) : e.column e.left = e.first := by
  simp [UnitEdge.column, e.distinct]

omit [Fintype I] in
theorem UnitEdge.column_right (e : UnitEdge I) : e.column e.right = e.second := by
  simp [UnitEdge.column, Ne.symm e.distinct]

omit [Fintype I] in
theorem UnitEdge.column_zero (e : UnitEdge I) (i : I)
    (hi : i ≠ e.left) (hj : i ≠ e.right) : e.column i = 0 := by
  simp [UnitEdge.column, hi, hj]

omit [Fintype I] in
theorem entryEdge_outer (i j : I) (hij : i ≠ j) (b : ℂ) :
    (‖b‖ : ℂ) * (entryEdge i j hij b).column i *
      star ((entryEdge i j hij b).column j) = b := by
  have hl : (entryEdge i j hij b).column i = 1 := UnitEdge.column_left _
  have hr : (entryEdge i j hij b).column j = unitPhase b := UnitEdge.column_right _
  rw [hl, hr, mul_one]
  exact unitPhase_entry b

end ResearchMain.Chollet.RankCoefficients
