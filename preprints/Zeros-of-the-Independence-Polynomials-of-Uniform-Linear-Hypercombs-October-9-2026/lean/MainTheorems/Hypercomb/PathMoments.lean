import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace ResearchMain.Hypercomb

open scoped BigOperators ComplexConjugate

noncomputable def pathMass (v : ℕ → ℂ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ‖v i‖ ^ 2

noncomputable def pathEndpoint (v : ℕ → ℂ) (m : ℕ) : ℝ := ‖v 0‖ ^ 2 + ‖v (m + 1)‖ ^ 2

def pathEdges (v : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), conj (v i) * v (i + 1)

theorem pathMass_split (v : ℕ → ℂ) (m : ℕ) :
    pathMass v (m + 2) = ‖v 0‖ ^ 2 +
      (∑ i ∈ Finset.range m, ‖v (i + 1)‖ ^ 2) + ‖v (m + 1)‖ ^ 2 := by
  rw [pathMass, Finset.sum_range_succ, Finset.sum_range_succ']
  ring

theorem pathEndpoint_le_mass (v : ℕ → ℂ) (m : ℕ) :
    0 ≤ pathEndpoint v m ∧ pathEndpoint v m ≤ pathMass v (m + 2) := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range m, ‖v (i + 1)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [pathMass_split, pathEndpoint]
  constructor
  · positivity
  · linarith

theorem adjacent_real_bound (u v : ℂ) :
    |2 * (conj u * v).re| ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have hu : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm u
  have hv : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm v
  rw [hu, hv, abs_le]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  constructor
  · nlinarith [sq_nonneg (u.re + v.re), sq_nonneg (u.im + v.im)]
  · nlinarith [sq_nonneg (u.re - v.re), sq_nonneg (u.im - v.im)]

theorem pathEdges_bound (v : ℕ → ℂ) (m : ℕ) :
    |2 * (pathEdges v m).re| ≤ 2 * pathMass v (m + 2) := by
  have hsum := Finset.sum_le_sum (s := Finset.range (m + 1))
    (fun i _ => adjacent_real_bound (v i) (v (i + 1)))
  have habs : |∑ i ∈ Finset.range (m + 1), 2 * (conj (v i) * v (i + 1)).re| ≤
      ∑ i ∈ Finset.range (m + 1), |2 * (conj (v i) * v (i + 1)).re| :=
    Finset.abs_sum_le_sum_abs _ _
  have hright : (∑ i ∈ Finset.range (m + 1), (‖v i‖ ^ 2 + ‖v (i + 1)‖ ^ 2)) ≤
      2 * pathMass v (m + 2) := by
    rw [Finset.sum_add_distrib]
    have hleft := Finset.sum_range_succ (fun i => ‖v i‖ ^ 2) (m + 1)
    have hnext := Finset.sum_range_succ' (fun i => ‖v i‖ ^ 2) (m + 1)
    change _ ≤ 2 * ∑ i ∈ Finset.range (m + 2), ‖v i‖ ^ 2
    nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v (m + 1)‖]
  have hre : 2 * (pathEdges v m).re =
      ∑ i ∈ Finset.range (m + 1), 2 * (conj (v i) * v (i + 1)).re := by
    simp only [pathEdges, Complex.re_sum, Finset.mul_sum]
  rw [hre]
  exact habs.trans (hsum.trans hright)

theorem path_moment_equation (A z c : ℂ) (v : ℕ → ℂ) (m : ℕ)
    (hfirst : (A + z) * v 0 + c * v 1 = 0)
    (hmiddle : ∀ i < m, c * v i + A * v (i + 1) + c * v (i + 2) = 0)
    (hlast : c * v m + (A + z) * v (m + 1) = 0) :
    A * (pathMass v (m + 2) : ℂ) + z * (pathEndpoint v m : ℂ) +
      c * ((2 * (pathEdges v m).re : ℝ) : ℂ) = 0 := by
  have hmid : (∑ i ∈ Finset.range m,
      conj (v (i + 1)) * (c * v i + A * v (i + 1) + c * v (i + 2))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hmiddle i (Finset.mem_range.mp hi), mul_zero]
  have h₀ : conj (v 0) * ((A + z) * v 0 + c * v 1) = 0 := by rw [hfirst, mul_zero]
  have h₁ : conj (v (m + 1)) * (c * v m + (A + z) * v (m + 1)) = 0 := by rw [hlast, mul_zero]
  have hdiag : (pathMass v (m + 2) : ℂ) = conj (v 0) * v 0 +
      (∑ i ∈ Finset.range m, conj (v (i + 1)) * v (i + 1)) + conj (v (m + 1)) * v (m + 1) := by
    rw [pathMass_split]
    push_cast
    simp only [Complex.conj_mul']
  have hend : (pathEndpoint v m : ℂ) = conj (v 0) * v 0 + conj (v (m + 1)) * v (m + 1) := by
    simp only [pathEndpoint, Complex.ofReal_add, Complex.conj_mul', Complex.ofReal_pow]
  have hedge : ((2 * (pathEdges v m).re : ℝ) : ℂ) = pathEdges v m + conj (pathEdges v m) := by
    apply Complex.ext <;> simp
    ring
  have hforward : pathEdges v m = conj (v 0) * v 1 +
      ∑ i ∈ Finset.range m, conj (v (i + 1)) * v (i + 2) := by
    rw [pathEdges, Finset.sum_range_succ']
    ring
  have hbackward : conj (pathEdges v m) =
      (∑ i ∈ Finset.range m, conj (v (i + 1)) * v i) + conj (v (m + 1)) * v m := by
    rw [pathEdges, map_sum]
    simp only [map_mul, Complex.conj_conj]
    rw [Finset.sum_range_succ]
    simp only [mul_comm]
  rw [hdiag, hend, hedge, hbackward, hforward]
  have hmid' : c * (∑ i ∈ Finset.range m, conj (v (i + 1)) * v i) +
      A * (∑ i ∈ Finset.range m, conj (v (i + 1)) * v (i + 1)) +
      c * (∑ i ∈ Finset.range m, conj (v (i + 1)) * v (i + 2)) = 0 := by
    convert hmid using 1
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linear_combination h₀ + h₁ + hmid'

theorem path_normalized_equation (A z c : ℂ) (v : ℕ → ℂ) (m : ℕ)
    (hv : v 0 ≠ 0)
    (hfirst : (A + z) * v 0 + c * v 1 = 0)
    (hmiddle : ∀ i < m, c * v i + A * v (i + 1) + c * v (i + 2) = 0)
    (hlast : c * v m + (A + z) * v (m + 1) = 0) :
    ∃ σ t : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ |t| ≤ 2 ∧ A + (σ : ℂ) * z + c * (t : ℂ) = 0 := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range m, ‖v (i + 1)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : 0 < pathMass v (m + 2) := by
    rw [pathMass_split]
    have hzero : 0 < ‖v 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    nlinarith [sq_nonneg ‖v (m + 1)‖]
  obtain ⟨hend0, hendle⟩ := pathEndpoint_le_mass v m
  have hedge := pathEdges_bound v m
  let σ := pathEndpoint v m / pathMass v (m + 2)
  let t := 2 * (pathEdges v m).re / pathMass v (m + 2)
  refine ⟨σ, t, div_nonneg hend0 hmass.le, ?_, ?_, ?_⟩
  · exact (div_le_one hmass).mpr hendle
  · dsimp only [t]
    rw [abs_div, abs_of_pos hmass]
    exact (div_le_iff₀ hmass).mpr hedge
  · have heq := path_moment_equation A z c v m hfirst hmiddle hlast
    push_cast at heq
    have hmassC : (pathMass v (m + 2) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hmass
    dsimp only [σ, t]
    push_cast
    field_simp
    linear_combination heq

end ResearchMain.Hypercomb
