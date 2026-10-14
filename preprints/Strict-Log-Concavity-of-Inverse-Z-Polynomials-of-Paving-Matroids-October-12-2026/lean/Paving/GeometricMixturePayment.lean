import Paving.ActualWeightPayment

noncomputable section
open Finset
namespace Paving

/-- The full penultimate bound from the actual hyperplane intersection and weight constraints. -/
theorem geometric_mixture_payment {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (w u : ι→ℝ) (C m N : ℝ)
    (hC : 0 < C) (hm : 2 ≤ m) (hN : m ≤ N)
    (hw : ∀i∈t,0 ≤ w i) (hs : ∑i∈t,w i=1)
    (hu : ∀i∈t,m-1 ≤ u i ∧ u i ≤ N-1)
    (hlarge : ∀j∈t,N+m-2 < 2*u j →
      w j ≤ (u j+m)/(u j+m+(2*m-1)*(N-u j)) ∧
      ∀i∈t,i≠j → u i ≤ N+m-2-u j) :
    penultimateFloor C N m < ∑i∈t,w i*(C*penultimateComponent m N (u i)) := by
  classical
  by_cases hall : ∀i∈t,2*u i ≤ N+m-2
  · have hb : ∀i∈t,penultimateFloor C N m < C*penultimateComponent m N (u i) := by
      intro i hi
      have h := small_hyperplane_component_bound (m:=m) (N:=N)
        (by linarith) hN (hu i hi).1 (hall i hi)
      have he : penultimateFloor C N m=C*penultimateFloor 1 N m := by
        unfold penultimateFloor; ring
      rw [he]
      exact mul_lt_mul_of_pos_left h hC
    have hsum := mixture_strict_bound t w (fun _ => penultimateFloor C N m) _ hw hs hb
    simpa only [← sum_mul,hs,one_mul] using hsum
  · push Not at hall
    obtain ⟨j,hj,hjlarge⟩ := hall
    have hjbounds := hu j hj
    have hgeom := hlarge j hj hjlarge
    let a := u j-m+2
    let s := N-u j
    let b := m-1
    have hs1 : 1 ≤ s := by dsimp [s]; linarith
    have hb1 : 1 ≤ b := by dsimp [b]; linarith
    have hsa : s ≤ a := by dsimp [s,a]; linarith
    have hα : w j ≤ (a+2*b)/(a+2*b+(2*b+1)*s) := by
      convert hgeom.1 using 1
      dsimp [a,b,s]
      congr 1 <;> ring
    have hpay : penultimateFloor C (a+s+b-1) (b+1) <
        ∑i∈t,w i*(C*penultimateComponent m N (u i)) := by
      apply large_component_reserve_bound hsa hs1 hb1 hC hα
      have heN : a+s+b-1=N := by dsimp [a,s,b]; ring
      have hem : b+1=m := by dsimp [b]; ring
      have hej : a+b-1=u j := by dsimp [a,b]; ring
      rw [heN,hem,hej]
      apply mixture_reserve_one t w _ j _ _ hj hw hs le_rfl
      intro i hi hij
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply penultimateComponent_antitone (by linarith) (by linarith)
        (show 0 < u i+1 by have := (hu i hi).1; linarith)
      have h := hgeom.2 i hi hij
      dsimp [s,b]
      linarith
    have heN : a+s+b-1=N := by dsimp [a,s,b]; ring
    have hem : b+1=m := by dsimp [b]; ring
    simpa only [heN,hem] using hpay

end Paving
