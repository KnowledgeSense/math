import Fan.InvariantUniquenessSymmetry

namespace MatroidInverseZ
open Finset Polynomial
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

omit [DecidableLE α] in
theorem rank_one_Ico (r : α → ℕ) (hr : StrictMono r) (a b : α)
    (hab : a≤b) (hd : r b=r a+1) : Ico a b={a} := by
  have hn : a≠b := by intro h; subst b; omega
  ext x
  simp only [mem_Ico,mem_singleton]
  constructor
  · rintro ⟨hax,hxb⟩
    by_contra hne
    have h1 := hr (lt_of_le_of_ne hax (Ne.symm hne))
    have h2 := hr hxb
    omega
  · rintro rfl
    exact ⟨le_rfl,lt_of_le_of_ne hab hn⟩

omit [DecidableLE α] in
theorem inverseZ_rank_one_split (r : α → ℕ) (hr : StrictMono r) (a b : α)
    (hab : a≤b) (hd : r b=r a+1) : inverseZ r a b=inverseKL r a b+X := by
  have hn : a≠b := by intro h; subst b; omega
  have hm : IncidenceAlgebra.mu ℤ a b=-1 := by
    rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hn,rank_one_Ico r hr a b hab hd,
      sum_singleton,IncidenceAlgebra.mu_self]
  rw [inverseZ,Icc_eq_cons_Ico hab,sum_cons,rank_one_Ico r hr a b hab hd,sum_singleton]
  simp [hm,hd]

theorem inverseKL_rank_one (r : α → ℕ) (hr : StrictMono r) (a b : α)
    (hab : a≤b) (hd : r b=r a+1) : inverseKL r a b=1 := by
  have hn : a≠b := by intro h; subst b; omega
  have hhigh (i : ℕ) (hi : 1 ≤ i) : (inverseKL r a b).coeff i=0 :=
    inverseKL_high_coeff r hr.monotone a b hab hn i (by omega)
  have hs := inverseZ_coeff_symm r hr.monotone a b 0 (by omega)
  rw [inverseZ_rank_one_split r hr a b hab hd] at hs
  have hd' : r b-r a=1 := by omega
  simp only [hd',Nat.sub_zero,coeff_add,coeff_X_zero,add_zero,coeff_X_one,hhigh 1 le_rfl,zero_add] at hs
  ext i
  cases i with
  | zero => simpa using hs
  | succ i => simpa only [coeff_one, Nat.add_one_ne_zero, ite_false] using hhigh (i+1) (by omega)

end MatroidInverseZ
