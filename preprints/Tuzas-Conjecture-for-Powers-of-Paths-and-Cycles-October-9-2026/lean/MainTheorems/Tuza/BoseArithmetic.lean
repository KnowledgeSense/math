import MainTheorems.Tuza.SteinerOperation
import MainTheorems.Tuza.ReflectionMatching

namespace ResearchMain.Tuza

theorem zmod_three_ne_cases {i j : ZMod 3} (hij : i ≠ j) :
    j = i + 1 ∨ i = j + 1 := by
  revert hij j i
  decide

theorem zmod_three_no_reverse (i : ZMod 3) : i ≠ (i + 1) + 1 := by
  revert i
  decide

variable {K : Type*} [AddCommGroup K]

noncomputable def doublingEquiv [Finite K]
    (hd : Function.Injective (fun x : K => x + x)) : K ≃+ K :=
  AddEquiv.ofBijective
    ({toFun := fun x => x + x, map_zero' := by simp, map_add' := by intro x y; abel} : K →+ K)
    ⟨hd, Finite.surjective_of_injective hd⟩

@[simp]
theorem doublingEquiv_apply [Finite K]
    (hd : Function.Injective (fun x : K => x + x)) (x : K) : doublingEquiv hd x = x + x := rfl

def midpoint (D : K ≃+ K) (x y : K) : K := D.symm (x + y)

@[simp]
theorem midpoint_comm (D : K ≃+ K) (x y : K) : midpoint D x y = midpoint D y x := by
  simp [midpoint, add_comm]

theorem midpoint_double (D : K ≃+ K) (x y : K) : D (midpoint D x y) = x + y :=
  D.apply_symm_apply _

theorem midpoint_self (D : K ≃+ K) (hD : ∀ x, D x = x + x) (x : K) : midpoint D x x = x := by
  apply D.injective
  rw [midpoint_double, hD]

theorem midpoint_ne_left (D : K ≃+ K) (hD : ∀ x, D x = x + x)
    {x y : K} (hxy : x ≠ y) : midpoint D x y ≠ x := by
  intro hh
  have he := midpoint_double D x y
  rw [hh, hD] at he
  exact hxy (add_left_cancel he)

theorem double_sub_ne (D : K ≃+ K) (hD : ∀ x, D x = x + x)
    {x y : K} (hxy : x ≠ y) : D y - x ≠ x := by
  intro hh
  have he : D y = D x := by
    rw [hD x]
    exact sub_eq_iff_eq_add.mp hh
  exact hxy (D.injective he).symm

theorem midpoint_double_sub (D : K ≃+ K) (x y : K) : midpoint D x (D y - x) = y := by
  apply D.injective
  rw [midpoint_double]
  abel

theorem double_sub_ne_self (D : K ≃+ K) (hD : ∀ x, D x = x + x)
    {x y : K} (hxy : x ≠ y) : D x - y ≠ x := by
  intro hh
  have he : x + x = x + y := by rw [← hD x]; exact sub_eq_iff_eq_add.mp hh
  exact hxy (add_left_cancel he)

end ResearchMain.Tuza
