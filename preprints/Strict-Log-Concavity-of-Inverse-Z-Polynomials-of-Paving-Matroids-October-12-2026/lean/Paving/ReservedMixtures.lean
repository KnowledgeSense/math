import Paving.Mixtures

noncomputable section
open Finset
namespace Paving

theorem mixture_ge_constant {ι : Type*} (s : Finset ι) (w x : ι→ℝ) (b : ℝ)
    (hw : ∀i∈s,0 ≤ w i) (hs : ∑i∈s,w i=1) (hx : ∀i∈s,b ≤ x i) :
    b ≤ ∑i∈s,w i*x i := by
  have h := sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hx i hi) (hw i hi))
  simpa only [← sum_mul,hs,one_mul] using h

/-- Reserve one component with its exact weight and bound only the remainder. -/
theorem mixture_reserve_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι→ℝ) (j : ι) (a b : ℝ)
    (hj : j∈s) (hw : ∀i∈s,0 ≤ w i) (hs : ∑i∈s,w i=1)
    (hmain : a ≤ x j) (hother : ∀i∈s,i≠j → b ≤ x i) :
    w j*a+(1-w j)*b ≤ ∑i∈s,w i*x i := by
  have hew : (∑i∈s.erase j,w i)=1-w j := by
    have h := sum_erase_add s w hj
    linarith
  have hel : (∑i∈s.erase j,w i*b) ≤ ∑i∈s.erase j,w i*x i := by
    apply sum_le_sum
    intro i hi
    have his := mem_of_mem_erase hi
    exact mul_le_mul_of_nonneg_left (hother i his (ne_of_mem_erase hi)) (hw i his)
  rw [← sum_mul,hew] at hel
  have hmain' := mul_le_mul_of_nonneg_left hmain (hw j hj)
  have he := sum_erase_add s (fun i => w i*x i) hj
  linarith

end Paving
