import Fan.DelannoyContiguous
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open Polynomial Filter
open scoped Topology
namespace Fan

private theorem rootSum_hasDerivAt (m : Multiset ℝ) (z : ℝ)
    (hz : ∀ r ∈ m, z-r ≠ 0) :
    HasDerivAt (fun x => (m.map (fun r => 1/(x-r))).sum)
      (m.map (fun r => -(1/(z-r)^2))).sum z := by
  induction m using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const z (0:ℝ)
  | @cons r m ih =>
    have hr : z-r ≠ 0 := hz r (by simp)
    have h1 := ((hasDerivAt_id z).sub_const r).inv hr
    have h2 := ih (fun q hq => hz q (by simp [hq]))
    convert h1.add h2 using 1 <;> simp [one_div, neg_div]
    rfl

private theorem rootSum_identity (m : Multiset ℝ) (z : ℝ)
    (hz : ∀ r ∈ m, z-r ≠ 0) :
    (m.map (fun r => 1/(z-r))).sum -
      (1-z)*(m.map (fun r => -(1/(z-r)^2))).sum =
      (m.map (fun r => (1-r)/(z-r)^2)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons r m ih =>
    have hr := hz r (by simp)
    have hm := ih (fun q hq => hz q (by simp [hq]))
    simp only [Multiset.map_cons,Multiset.sum_cons]
    have he : 1/(z-r) - (1-z)*(-(1/(z-r)^2)) = (1-r)/(z-r)^2 := by
      field_simp
      ring
    linarith

/-- The signed logarithmic-derivative expression forced by negative roots is positive. -/
theorem negative_roots_log_positive {p : Polynomial ℝ} (hp : p.Splits)
    (hn : p.natDegree ≠ 0) (hr : ∀ r ∈ p.roots, r < 0) {z : ℝ} (hz : 0 < z) :
    0 < p.derivative.eval z / p.eval z - (1-z)*
      ((p.derivative.derivative.eval z * p.eval z - (p.derivative.eval z)^2)/(p.eval z)^2) := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hn
  have he (x : ℝ) (hx : 0 < x) : p.eval x ≠ 0 := by
    intro h
    have hm := (mem_roots hp0).mpr h
    have := hr x hm
    linarith
  have hnr : ∀ r ∈ p.roots, z-r ≠ 0 := by
    intro r h
    have := hr r h
    linarith
  have hD := (p.derivative.hasDerivAt z).div (p.hasDerivAt z) (he z hz)
  have hR := rootSum_hasDerivAt p.roots z hnr
  have hEq : (fun x => p.derivative.eval x / p.eval x) =ᶠ[𝓝 z]
      (fun x => (p.roots.map (fun r => 1/(x-r))).sum) := by
    filter_upwards [Ioi_mem_nhds hz] with x hx
    exact hp.eval_derivative_div_eval_of_ne_zero (he x hx)
  have hDer := hR.unique (hD.congr_of_eventuallyEq hEq.symm)
  rw [← pow_two] at hDer
  have hVal := hp.eval_derivative_div_eval_of_ne_zero (he z hz)
  rw [hVal, ← hDer,rootSum_identity p.roots z hnr]
  have hne := hp.roots_ne_zero hn
  obtain ⟨r,hrm⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨m,hm⟩ := Multiset.exists_cons_of_mem hrm
  rw [hm,Multiset.map_cons,Multiset.sum_cons]
  apply add_pos_of_pos_of_nonneg
  · exact div_pos (by have := hr r hrm; linarith) (sq_pos_of_ne_zero (hnr r hrm))
  · apply Multiset.sum_nonneg
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Multiset.mem_map.mp hx
    have hqm : q ∈ p.roots := by rw [hm]; simp [hq]
    exact (div_pos (by have := hr q hqm; linarith) (sq_pos_of_ne_zero (hnr q hqm))).le

end Fan
