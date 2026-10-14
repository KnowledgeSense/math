import ThagomizerTuran.IntervalTransport

/-! The characteristic incidence kernel needed to verify the KL functional equation. -/
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

noncomputable def constantMu : IncidenceAlgebra (Polynomial ℤ) α where
  toFun a b := C (IncidenceAlgebra.mu ℤ a b)
  eq_zero_of_not_le' {_ _} h := by rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]; simp

noncomputable def rankZeta (r : α → ℕ) : IncidenceAlgebra (Polynomial ℤ) α where
  toFun a b := IncidenceAlgebra.zeta (Polynomial ℤ) a b * X ^ (r b - r a)
  eq_zero_of_not_le' {_ _} h := by rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]; simp

noncomputable def rankMu (r : α → ℕ) : IncidenceAlgebra (Polynomial ℤ) α where
  toFun a b := C (IncidenceAlgebra.mu ℤ a b) * X ^ (r b - r a)
  eq_zero_of_not_le' {_ _} h := by rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]; simp

theorem zeta_mul_constantMu :
    (IncidenceAlgebra.zeta (Polynomial ℤ) * constantMu : IncidenceAlgebra (Polynomial ℤ) α) = 1 := by
  ext a b : 1
  rw [IncidenceAlgebra.mul_apply, IncidenceAlgebra.one_apply]
  calc
    _ = C (∑ x ∈ Icc a b, IncidenceAlgebra.mu ℤ x b) := by
      rw [map_sum]
      apply sum_congr rfl
      intro x hx
      rw [IncidenceAlgebra.zeta_of_le (mem_Icc.mp hx).1, one_mul]
      rfl
    _ = _ := by rw [IncidenceAlgebra.sum_Icc_mu_left]; split_ifs <;> simp

theorem rankMu_mul_rankZeta (r : α → ℕ) (hr : Monotone r) :
    rankMu r * rankZeta r = (1 : IncidenceAlgebra (Polynomial ℤ) α) := by
  ext a b : 1
  rw [IncidenceAlgebra.mul_apply, IncidenceAlgebra.one_apply]
  calc
    _ = C (∑ x ∈ Icc a b, IncidenceAlgebra.mu ℤ a x) * X ^ (r b - r a) := by
      rw [map_sum, sum_mul]
      apply sum_congr rfl
      intro x hx
      have hax := mem_Icc.mp hx
      change (C (IncidenceAlgebra.mu ℤ a x) * X ^ (r x - r a)) *
        (IncidenceAlgebra.zeta (Polynomial ℤ) x b * X ^ (r b - r x)) = _
      rw [IncidenceAlgebra.zeta_of_le hax.2, one_mul, mul_assoc, ← pow_add]
      congr 2
      have ha := hr hax.1
      have hb := hr hax.2
      omega
    _ = _ := by
      rw [IncidenceAlgebra.sum_Icc_mu_right]
      by_cases h : a = b
      · subst b
        simp
      · simp [h]

theorem characteristic_incidence (r : α → ℕ) (a b : α) :
    (constantMu * rankZeta r : IncidenceAlgebra (Polynomial ℤ) α) a b = characteristic r a b := by
  rw [IncidenceAlgebra.mul_apply, characteristic]
  apply sum_congr rfl
  intro x hx
  change C (IncidenceAlgebra.mu ℤ a x) *
    (IncidenceAlgebra.zeta (Polynomial ℤ) x b * X ^ (r b - r x)) = _
  rw [IncidenceAlgebra.zeta_of_le (mem_Icc.mp hx).2, one_mul]

theorem reflect_characteristic_incidence (r : α → ℕ) (hr : Monotone r) (a b : α) :
    reflect (r b - r a) (characteristic r a b) =
      (rankMu r * IncidenceAlgebra.zeta (Polynomial ℤ) : IncidenceAlgebra (Polynomial ℤ) α) a b := by
  rw [characteristic, IncidenceAlgebra.mul_apply]
  have hsum : ∀ (s : Finset α),
      reflect (r b - r a) (∑ x ∈ s, C (IncidenceAlgebra.mu ℤ a x) * X ^ (r b - r x)) =
        ∑ x ∈ s, reflect (r b - r a) (C (IncidenceAlgebra.mu ℤ a x) * X ^ (r b - r x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [reflect_zero]
    | @insert x s hx ih => rw [sum_insert hx, reflect_add, ih, sum_insert hx]
  rw [hsum]
  apply sum_congr rfl
  intro x hx
  have hax := mem_Icc.mp hx
  have hra := hr hax.1
  have hrb := hr hax.2
  rw [reflect_C_mul_X_pow, Polynomial.revAt_le (by omega : r b - r x ≤ r b - r a)]
  change C (IncidenceAlgebra.mu ℤ a x) * X ^ (r b - r a - (r b - r x)) =
    C (IncidenceAlgebra.mu ℤ a x) * X ^ (r x - r a) * IncidenceAlgebra.zeta (Polynomial ℤ) x b
  rw [IncidenceAlgebra.zeta_of_le hax.2, mul_one]
  congr 2
  omega

/-- The true characteristic polynomial satisfies the incidence kernel relation. -/
theorem characteristic_kernel (r : α → ℕ) (hr : Monotone r) (a b : α) :
    (∑ x ∈ Icc a b, reflect (r x - r a) (characteristic r a x) * characteristic r x b) =
      if a = b then 1 else 0 := by
  have h : (rankMu r * IncidenceAlgebra.zeta (Polynomial ℤ)) * (constantMu * rankZeta r) =
      (1 : IncidenceAlgebra (Polynomial ℤ) α) := by
    calc
      _ = rankMu r * ((IncidenceAlgebra.zeta (Polynomial ℤ) * constantMu) * rankZeta r) := by
        simp only [mul_assoc]
      _ = _ := by rw [zeta_mul_constantMu, one_mul, rankMu_mul_rankZeta r hr]
  have he := congrArg (fun f : IncidenceAlgebra (Polynomial ℤ) α => f a b) h
  rw [IncidenceAlgebra.mul_apply, IncidenceAlgebra.one_apply] at he
  simpa only [characteristic_incidence, ← reflect_characteristic_incidence r hr] using he

end MatroidInverseZ

namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

/-- The kernel relation after convolution with any interval polynomial family. -/
theorem characteristic_kernel_convolve (r : α → ℕ) (hr : Monotone r)
    (p : α → α → Polynomial ℤ) (a b : α) (hab : a ≤ b) :
    (∑ x ∈ Icc a b, reflect (r x - r a) (characteristic r a x) *
      ∑ y ∈ Icc x b, characteristic r x y * p y b) = p a b := by
  let A : IncidenceAlgebra (Polynomial ℤ) α := rankMu r * IncidenceAlgebra.zeta (Polynomial ℤ)
  let B : IncidenceAlgebra (Polynomial ℤ) α := constantMu * rankZeta r
  let P : IncidenceAlgebra (Polynomial ℤ) α :=
    ⟨fun x y => if x ≤ y then p x y else 0, fun {_ _} h => ite_eq_right h⟩
  have hAB : A * B = 1 := by
    calc
      _ = rankMu r * ((IncidenceAlgebra.zeta (Polynomial ℤ) * constantMu) * rankZeta r) := by
        simp only [A, B, mul_assoc]
      _ = _ := by rw [zeta_mul_constantMu, one_mul, rankMu_mul_rankZeta r hr]
  have hAP : A * (B * P) = P := by rw [← mul_assoc, hAB, one_mul]
  calc
    _ = (A * (B * P)) a b := by
      rw [IncidenceAlgebra.mul_apply]
      apply sum_congr rfl
      intro x hx
      rw [show A a x = reflect (r x - r a) (characteristic r a x) from
        (reflect_characteristic_incidence r hr a x).symm]
      congr 1
      rw [IncidenceAlgebra.mul_apply]
      apply sum_congr rfl
      intro y hy
      rw [show B x y = characteristic r x y from characteristic_incidence r x y]
      change characteristic r x y * p y b =
        characteristic r x y * (if y ≤ b then p y b else 0)
      rw [ite_eq_left (mem_Icc.mp hy).2]
    _ = _ := by rw [hAP]; exact ite_eq_left hab

end MatroidInverseZ
