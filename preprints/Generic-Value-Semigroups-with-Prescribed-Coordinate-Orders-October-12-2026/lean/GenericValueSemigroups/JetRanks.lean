import GenericValueSemigroups.FormalValues
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- Adding a scalar coordinate increases rank exactly when it is nonzero on the previous kernel. -/
theorem rank_step_iff {K V W W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (f : V →ₗ[K] W) (g : V →ₗ[K] K) (h : V →ₗ[K] W')
    (hk : ∀ x, h x=0 ↔ f x=0 ∧ g x=0) :
    Module.finrank K (LinearMap.range h) = Module.finrank K (LinearMap.range f)+1 ↔
      ∃ x, f x=0 ∧ g x≠0 := by
  let g' := g.domRestrict (LinearMap.ker f)
  let e : LinearMap.ker h ≃ₗ[K] LinearMap.ker g' :=
    { toFun := fun x => ⟨⟨x.val, (hk x.val).mp x.property |>.1⟩, (hk x.val).mp x.property |>.2⟩
      invFun := fun x => ⟨x.val.val, (hk x.val.val).mpr ⟨x.val.property,x.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he := e.finrank_eq
  have hf := f.finrank_range_add_finrank_ker
  have hh := h.finrank_range_add_finrank_ker
  have hg := g'.finrank_range_add_finrank_ker
  by_cases hex : ∃ x, f x=0 ∧ g x≠0
  · obtain ⟨x,hfx,hgx⟩ := hex
    have hsurj : Function.Surjective g' := by
      intro b
      refine ⟨(b / g x) • (⟨x,hfx⟩ : LinearMap.ker f), ?_⟩
      simp only [map_smul]
      change (b / g x) * g x = b
      exact div_mul_cancel₀ b hgx
    have hdim : Module.finrank K (LinearMap.range g')=1 := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
    constructor
    · intro _; exact ⟨x,hfx,hgx⟩
    · intro _; omega
  · have hzero : g'=0 := by
      ext x
      have hx : g x.val=0 := by
        by_contra hne
        exact hex ⟨x.val,x.property,hne⟩
      exact hx
    have hdim : Module.finrank K (LinearMap.range g')=0 := by rw [hzero]; simp
    constructor
    · intro heq; omega
    · exact fun hx => False.elim (hex hx)

/-- The actual coefficient matrix of a finite family of power series. -/
noncomputable def coefficientMatrix {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ) (N : ℕ) :
    Matrix (Fin N) (ι) ℂ := fun i j => PowerSeries.coeff i (f j)

/-- The actual linear combination of a finite family of series. -/
noncomputable def seriesCombination {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ) (c : ι → ℂ) :
    PowerSeries ℂ := ∑ j, c j • f j

@[simp] theorem coeff_seriesCombination {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ)
    (c : ι → ℂ) (n : ℕ) : PowerSeries.coeff n (seriesCombination f c) =
      ∑ j, PowerSeries.coeff n (f j) * c j := by
  simp [seriesCombination, mul_comm]

noncomputable def coefficientFunctional {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ) (n : ℕ) :
    (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := ∑ j, PowerSeries.coeff n (f j) * c j
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem coefficientFunctional_apply {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ)
    (n : ℕ) (c : ι → ℂ) : coefficientFunctional f n c =
      PowerSeries.coeff n (seriesCombination f c) := (coeff_seriesCombination f c n).symm

@[simp] theorem coefficientMatrix_mulVecLin_apply {ι : Type*} [Fintype ι] {N : ℕ}
    (f : ι → PowerSeries ℂ) (c : ι → ℂ) (i : Fin N) :
    (coefficientMatrix f N).mulVecLin c i = PowerSeries.coeff i (seriesCombination f c) :=
  (coeff_seriesCombination f c i).symm

theorem coefficientMatrix_kernel_step {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ)
    (n : ℕ) (c : ι → ℂ) :
    (coefficientMatrix f (n+1)).mulVecLin c=0 ↔
      (coefficientMatrix f n).mulVecLin c=0 ∧ coefficientFunctional f n c=0 := by
  constructor
  · intro h
    constructor
    · funext i
      have hh := congrFun h (⟨i.val, by omega⟩ : Fin (n+1))
      simpa only [coefficientMatrix_mulVecLin_apply, Pi.zero_apply] using hh
    · have hh := congrFun h (Fin.last n)
      simpa only [coefficientMatrix_mulVecLin_apply, coefficientFunctional_apply,
        Fin.val_last, Pi.zero_apply] using hh
  · rintro ⟨h1,h2⟩
    funext i
    by_cases hi : i.val<n
    · have hh := congrFun h1 (⟨i.val,hi⟩ : Fin n)
      simpa only [coefficientMatrix_mulVecLin_apply, Pi.zero_apply] using hh
    · have he : i.val=n := by have hh := i.isLt; omega
      simpa only [coefficientMatrix_mulVecLin_apply, coefficientFunctional_apply,
        he, Pi.zero_apply] using h2

/-- An order occurs in the actual linear span exactly at a one-dimensional prefix-rank increase. -/
theorem order_attained_iff_rank_step {ι : Type*} [Fintype ι] (f : ι → PowerSeries ℂ) (n : ℕ) :
    (∃ c : ι → ℂ, PowerSeries.order (seriesCombination f c)=n) ↔
      (coefficientMatrix f (n+1)).rank=(coefficientMatrix f n).rank+1 := by
  have hs := rank_step_iff (coefficientMatrix f n).mulVecLin (coefficientFunctional f n)
    (coefficientMatrix f (n+1)).mulVecLin (coefficientMatrix_kernel_step f n)
  rw [Matrix.rank, Matrix.rank]
  rw [hs]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨hne,hzero⟩ := PowerSeries.order_eq_nat.mp hc
    refine ⟨c,?_,?_⟩
    · funext i
      simpa only [coefficientMatrix_mulVecLin_apply, Pi.zero_apply] using hzero i i.isLt
    · simpa only [coefficientFunctional_apply] using hne
  · rintro ⟨c,hzero,hne⟩
    refine ⟨c,PowerSeries.order_eq_nat.mpr ⟨?_,?_⟩⟩
    · simpa only [coefficientFunctional_apply] using hne
    · intro j hj
      have hh := congrFun hzero (⟨j,hj⟩ : Fin n)
      simpa only [coefficientMatrix_mulVecLin_apply, Pi.zero_apply] using hh

end GenericValueSemigroups
