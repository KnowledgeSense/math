import MainTheorems.Tuza.BoseArithmetic

namespace ResearchMain.Tuza

structure HalfQuasigroup (L : Type*) where
  mul : (L × Bool) → (L × Bool) → L × Bool
  comm : ∀ x y, mul x y = mul y x
  bijective : ∀ x, Function.Bijective (mul x)
  diagonal : ∀ x, mul x x = (x.1, false)

namespace HalfQuasigroup

variable {L : Type*} (H : HalfQuasigroup L)

noncomputable def leftEquiv (x : L × Bool) : (L × Bool) ≃ (L × Bool) :=
  Equiv.ofBijective (H.mul x) (H.bijective x)

noncomputable def div (x y : L × Bool) : L × Bool := (H.leftEquiv x).symm y

@[simp]
theorem mul_div (x y : L × Bool) : H.mul x (H.div x y) = y :=
  (H.leftEquiv x).apply_symm_apply y

@[simp]
theorem div_mul (x y : L × Bool) : H.div x (H.mul x y) = y :=
  (H.leftEquiv x).symm_apply_apply y

theorem left_injective (x : L × Bool) : Function.Injective (H.mul x) := (H.bijective x).1

theorem mul_ne_diagonal {x y : L × Bool} (hxy : x ≠ y) : H.mul x y ≠ H.mul x x := by
  intro he
  exact hxy (H.left_injective x he).symm

theorem div_ne {x y : L × Bool} (hxy : y ≠ H.mul x x) : H.div x y ≠ x := by
  intro he
  exact hxy ((H.mul_div x y).symm.trans (congrArg (H.mul x) he))

theorem div_reverse {x y : L × Bool} : H.div (H.div x y) y = x := by
  apply H.left_injective (H.div x y)
  rw [H.mul_div, H.comm, H.mul_div]

theorem div_diagonal_ne {x y : L × Bool} (hxy : y ≠ H.mul x x) :
    y ≠ H.mul (H.div x y) (H.div x y) := by
  intro he
  apply H.div_ne hxy
  apply H.left_injective (H.div x y)
  rw [← he, H.comm, H.mul_div]

end HalfQuasigroup

end ResearchMain.Tuza
