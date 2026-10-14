import Paving.HyperplaneWeight
import Paving.PenultimateComponents
import Paving.ReservedMixtures

noncomputable section
namespace Paving

/-- The actual large-component reserve pays the even middle increment. -/
theorem large_component_reserve_bound {a s b C α p : ℝ}
    (hsa : s ≤ a) (hs : 1 ≤ s) (hb : 1 ≤ b) (hC : 0 < C)
    (hα : α ≤ (a+2*b)/(a+2*b+(2*b+1)*s))
    (hp : α*(C*penultimateComponent (b+1) (a+s+b-1) (a+b-1))+
      (1-α)*(C*penultimateComponent (b+1) (a+s+b-1) (s+b-1)) ≤ p) :
    penultimateFloor C (a+s+b-1) (b+1) < p := by
  have ha : 0 < a := by linarith
  have hs0 : 0 < s := by linarith
  have hb0 : 0 < b := by linarith
  have hd : 0 < a+s+b := by positivity
  have hab : 0 < a+b := by positivity
  have hsb : 0 < s+b := by positivity
  let γ := C*(b+1)/(a+s+b)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hmain : C*penultimateComponent (b+1) (a+s+b-1) (a+b-1)=γ*(s/(a+b)) := by
    unfold penultimateComponent
    dsimp [γ]
    field_simp (disch := first | positivity | linarith)
    ring
  have hother : C*penultimateComponent (b+1) (a+s+b-1) (s+b-1)=γ*(a/(s+b)) := by
    unfold penultimateComponent
    dsimp [γ]
    field_simp (disch := first | positivity | linarith)
    ring
  have hx : α*(s/(a+b))+(1-α)*(a/(s+b)) ≤ p/γ := by
    apply (le_div_iff₀ hγ).mpr
    rw [hmain,hother] at hp
    nlinarith [hp]
  have h := large_hyperplane_mixture_lower hsa hs hb hα hx
  have he : penultimateFloor C (a+s+b-1) (b+1)=γ*((a+s-1)/(a+s+2*b+1)) := by
    unfold penultimateFloor
    dsimp [γ]
    have ht : a+s+2*b+1≠0 := by positivity
    field_simp (disch := first | positivity | linarith)
    ring
  rw [he]
  have hm := mul_lt_mul_of_pos_left h hγ
  simpa only [mul_div_cancel₀ _ hγ.ne'] using hm

end Paving
