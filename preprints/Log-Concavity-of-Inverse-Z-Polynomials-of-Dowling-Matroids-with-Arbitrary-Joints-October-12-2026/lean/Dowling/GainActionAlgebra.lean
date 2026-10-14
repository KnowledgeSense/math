import Dowling.GainEquations

namespace Dowling
variable {G : Type*} [Group G]

theorem gainAct_eq_none_iff (x : Option G) (g : G) : gainAct G x g = none ↔ x = none := by
  cases x <;> simp [gainAct]

theorem gainAct_right_injective (g : G) : Function.Injective (fun x => gainAct G x g) := by
  intro x y h
  have h' := congrArg (fun z => gainAct G z g⁻¹) h
  simpa only [gainAct_mul, mul_inv_cancel, gainAct_one] using h'

theorem gainAct_compare (x y : Option G) (a b : G) :
    gainAct G x a = gainAct G y b ↔ x = gainAct G y (b*a⁻¹) := by
  constructor
  · intro h
    have h' := congrArg (fun z => gainAct G z a⁻¹) h
    simpa only [gainAct_mul, mul_inv_cancel, gainAct_one] using h'
  · intro h
    rw [h, gainAct_mul]
    simp [mul_assoc]

theorem gainAct_same_base (x : Option G) (a b : G) :
    gainAct G x a = gainAct G x b ↔ x = none ∨ a = b := by
  cases x <;> simp [gainAct]

end Dowling
