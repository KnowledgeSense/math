import MainTheorems.Chollet.GramExpansion
import Mathlib.GroupTheory.Perm.Option

namespace ResearchMain.Chollet

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

def optionBorder (a : R) (u v : I → R) (B : Matrix I I R) :
    Matrix (Option I) (Option I) R
  | none, none => a
  | none, some j => u j
  | some i, none => v i
  | some i, some j => B i j

theorem optionBorder_fixed_product (a : R) (u v : I → R) (B : Matrix I I R)
    (π : Equiv.Perm I) :
    (∏ j, optionBorder a u v B
      (Equiv.Perm.decomposeOption.symm (none, π) j) j) = a * ∏ j, B (π j) j := by
  simp [Fintype.prod_option, optionBorder]

theorem optionBorder_inserted_product (a : R) (u v : I → R) (B : Matrix I I R)
    (π : Equiv.Perm I) (i : I) :
    (∏ j, optionBorder a u v B
      (Equiv.Perm.decomposeOption.symm (some (π i), π) j) j) =
      v (π i) * u i * ∏ j ∈ Finset.univ.erase i, B (π j) j := by
  have hn : Equiv.Perm.decomposeOption.symm (some (π i), π) none = some (π i) := by
    simp [Equiv.Perm.decomposeOption, Equiv.Perm.mul_apply]
  have hi : Equiv.Perm.decomposeOption.symm (some (π i), π) (some i) = none := by
    simp [Equiv.Perm.decomposeOption, Equiv.Perm.mul_apply]
  have hj : ∀ j, j ≠ i → Equiv.Perm.decomposeOption.symm (some (π i), π) (some j) = some (π j) := by
    intro j hji
    change (Equiv.swap none (some (π i))) (some (π j)) = some (π j)
    apply Equiv.swap_apply_of_ne_of_ne
    · simp
    · exact fun h => hji (π.injective (Option.some.inj h))
  rw [Fintype.prod_option, hn]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => optionBorder a u v B
    (Equiv.Perm.decomposeOption.symm (some (π i), π) (some j)) (some j)) (Finset.mem_univ i)]
  rw [hi]
  simp only [optionBorder]
  rw [mul_assoc]
  apply congrArg (fun x => v (π i) * (u i * x))
  apply Finset.prod_congr rfl
  intro j hj'
  rw [hj j (Finset.mem_erase.mp hj').1]

theorem permanent_optionBorder (a : R) (u v : I → R) (B : Matrix I I R) :
    (optionBorder a u v B).permanent = a * B.permanent +
      ∑ π : Equiv.Perm I, ∑ i, v (π i) * u i * ∏ j ∈ Finset.univ.erase i, B (π j) j := by
  unfold Matrix.permanent
  rw [← Equiv.Perm.decomposeOption.symm.sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  rw [Finset.sum_comm]
  have he : ∀ π : Equiv.Perm I,
      (∑ x : I, ∏ j, optionBorder a u v B
        (Equiv.Perm.decomposeOption.symm (some x, π) j) j) =
      ∑ i, v (π i) * u i * ∏ j ∈ Finset.univ.erase i, B (π j) j := by
    intro π
    calc
      _ = ∑ i, ∏ j, optionBorder a u v B
          (Equiv.Perm.decomposeOption.symm (some (π i), π) j) j :=
        (Fintype.sum_equiv π _ _ (fun _ => rfl)).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => optionBorder_inserted_product a u v B π i)
  simp only [optionBorder_fixed_product, he, ← Finset.mul_sum]

end ResearchMain.Chollet
