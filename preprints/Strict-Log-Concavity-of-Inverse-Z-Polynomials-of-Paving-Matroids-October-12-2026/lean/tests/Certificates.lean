import Paving

open Paving MatroidInverseZ Polynomial

example {α : Type*} [Fintype α] (M : Matroid α) [M.Loopless]
    (hM : IsPaving M) (hr : 1≤rank M) := paving_inverseZ_main M hM hr

example {α : Type*} [Fintype α] (M : Matroid α) (hM : IsPaving M)
    (hr : 3≤rank M) := paving_inverseZ_higher_main M hM hr

example {α : Type*} [Fintype α] (M : Matroid α) (hr : rank M=1) :
    matroidInverseZ M=1+X := rank_one_polynomial M hr

example {α : Type*} [Fintype α] (M : Matroid α) (hr : rank M=2) :=
  rank_two_polynomial M hr

example {α : Type*} [Fintype α] (M : Matroid α) (hM : IsPaving M) (hr : rank M=2) :
    2≤(hyperplanes M).card := hM.rank_two_hyperplanes_card hr

example {α : Type*} [Fintype α] (M : Matroid α) (k : ℕ) (hk : rank M<k) :
    (matroidInverseZ M).coeff k=0 := actual_inverseZ_high_coeff M k hk

example {α : Type*} [Fintype α] (M : Matroid α) (hM : IsPaving M)
    (hr : rank M=3) :
    (matroidInverseZ M).coeff 0*(matroidInverseZ M).coeff 2 < (matroidInverseZ M).coeff 1^2 := by
  simpa using hM.coefficient_strict_higher (by omega) 1 (by omega) (by omega)

example {α : Type*} [Fintype α] (M : Matroid α) (hM : IsPaving M)
    (hr : rank M=4) :
    (matroidInverseZ M).coeff 1*(matroidInverseZ M).coeff 3 < (matroidInverseZ M).coeff 2^2 := by
  simpa using hM.coefficient_strict_higher (by omega) 2 (by omega) (by omega)

example : (uniformY (α:=Fin 4) 2).coeff 1=8 := by
  rw [uniformY_coeff_lower 2 1 (by simp) (by omega)]
  norm_num [Nat.choose]

example : (uniformY (α:=Fin 4) 3).coeff 2=6 := by
  rw [uniformY_coeff_lower 3 2 (by simp) (by omega)]
  norm_num [Nat.choose]

example : IsPaving (Matroid.freeOn (Set.univ : Set (Fin 3))) := by
  intro C hC
  exact False.elim (hC.not_indep (Matroid.freeOn_indep (Set.subset_univ C)))

example : (matroidInverseZ (Matroid.freeOn (Set.univ : Set (Fin 3)))).natDegree=3 := by
  let M := Matroid.freeOn (Set.univ : Set (Fin 3))
  have hM : IsPaving M := by
    intro C hC
    exact False.elim (hC.not_indep (Matroid.freeOn_indep (Set.subset_univ C)))
  have hr : rank M=3 := by simp [M,rank,Matroid.eRank_freeOn,Set.encard_univ]
  have h := (paving_inverseZ_higher_main M hM (by omega)).1
  simpa only [hr] using h
