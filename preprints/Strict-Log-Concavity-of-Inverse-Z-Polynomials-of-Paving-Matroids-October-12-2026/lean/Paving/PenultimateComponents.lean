import Paving.Penultimate
import Paving.Mixtures

noncomputable section
open Finset
namespace Paving

def penultimateComponent (m N u : ℝ) : ℝ := m*(N-u)/((N+1)*(u+1))
def previousComponent (m N u : ℝ) : ℝ := (m-1)*(N-u)/((N+2)*(u+2))

theorem penultimateComponent_positive {m N u : ℝ}
    (hm : 1 ≤ m) (hu : m-1 ≤ u) (hN : u < N) :
    0 < penultimateComponent m N u := by
  unfold penultimateComponent
  have : 0 < m := by linarith
  have : 0 < N-u := by linarith
  have : 0 < N+1 := by linarith
  have : 0 < u+1 := by linarith
  positivity

theorem previousComponent_ratio {m N u : ℝ}
    (hm : 1 < m) (hu : m-1 ≤ u) (hN : u < N) :
    previousComponent m N u < penultimateRatio N m*penultimateComponent m N u := by
  have hm0 : 0 < m := by linarith
  have hN1 : 0 < N+1 := by linarith
  have hN2 : 0 < N+2 := by linarith
  have hu1 : 0 < u+1 := by linarith
  have hu2 : 0 < u+2 := by linarith
  unfold previousComponent penultimateComponent penultimateRatio
  field_simp
  have hp : 0 < (m-1)*(N-u) := mul_pos (by linarith) (by linarith)
  nlinarith [hp]

theorem penultimateComponent_antitone {m N u v : ℝ}
    (hm : 0 < m) (hN : 0 < N+1) (hu : 0 < u+1) (huv : u ≤ v) :
    penultimateComponent m N v ≤ penultimateComponent m N u := by
  have hv : 0 < v+1 := by linarith
  unfold penultimateComponent
  apply (div_le_div_iff₀ (mul_pos hN hv) (mul_pos hN hu)).mpr
  have hp : 0 ≤ m*(N+1)^2*(v-u) := by positivity
  nlinarith [hp]

theorem small_hyperplane_component_bound {m N u : ℝ}
    (hm : 1 ≤ m) (hN : m ≤ N) (hu : m-1 ≤ u) (hsmall : 2*u ≤ N+m-2) :
    penultimateFloor 1 N m < penultimateComponent m N u := by
  have hm0 : 0 < m := by linarith
  have hN1 : 0 < N+1 := by linarith
  have hNm : 0 < N+m+1 := by linarith
  have hu1 : 0 < u+1 := by linarith
  unfold penultimateFloor penultimateComponent
  apply (div_lt_div_iff₀ (mul_pos hN1 hNm) (mul_pos hN1 hu1)).mpr
  have hstep : 0 < (N-u)*(N+m+1)-(N-m+1)*(u+1) := by
    have hp : 0 ≤ (N+1)*(N+m-2-2*u) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hp := mul_pos (mul_pos hm0 hN1) hstep
  nlinarith [hp]

theorem mixture_strict_bound {ι : Type*} (s : Finset ι) (w x y : ι→ℝ)
    (hw : ∀j∈s,0 ≤ w j) (hs : ∑j∈s,w j=1) (hxy : ∀j∈s,x j < y j) :
    (∑j∈s,w j*x j) < ∑j∈s,w j*y j := by
  have h := mixture_positive s w (fun j => y j-x j) hw hs (fun j hj => sub_pos.mpr (hxy j hj))
  simp only [mul_sub,sum_sub_distrib] at h
  linarith

end Paving
