import ThagomizerTuran.KLIncidence
import ThagomizerTuran.InverseKLDegree

/-! Rank reversal of ordinary inverse-Z, proved from the verified KL incidence
functional equation. This supplies rank symmetry for the actual fan invariant. -/
namespace MatroidInverseZ
open Finset Polynomial IncidenceAlgebra
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

noncomputable def barKernel (r : α → ℕ) (f : IncidenceAlgebra (Polynomial ℤ) α) :
    IncidenceAlgebra (Polynomial ℤ) α where
  toFun a b := reflect (r b - r a) (f a b)
  eq_zero_of_not_le' {_ _} h := by rw [IncidenceAlgebra.apply_eq_zero_of_not_le h, reflect_zero]

omit [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α] in
@[simp] theorem barKernel_apply (r : α → ℕ) (f : IncidenceAlgebra (Polynomial ℤ) α)
    (a b : α) : barKernel r f a b = reflect (r b - r a) (f a b) := rfl

def RankBounded (r : α → ℕ) (f : IncidenceAlgebra (Polynomial ℤ) α) : Prop :=
  ∀ a b, a ≤ b → (f a b).natDegree ≤ r b - r a

omit [DecidableEq α] [DecidableLE α] in
theorem barKernel_mul (r : α → ℕ) (hr : Monotone r)
    (f g : IncidenceAlgebra (Polynomial ℤ) α) (hf : RankBounded r f) (hg : RankBounded r g) :
    barKernel r (f * g) = barKernel r f * barKernel r g := by
  apply IncidenceAlgebra.ext
  intro a b _
  rw [barKernel_apply, IncidenceAlgebra.mul_apply, reflect_finset_sum, IncidenceAlgebra.mul_apply]
  apply sum_congr rfl
  intro x hx
  have hax := mem_Icc.mp hx
  have h1 := hr hax.1
  have h2 := hr hax.2
  have he : r b - r a = (r x - r a) + (r b - r x) := by omega
  rw [he, reflect_mul _ _ (hf a x hax.1) (hg x b hax.2)]
  rfl

omit [LocallyFiniteOrder α] [DecidableLE α] in
@[simp] theorem barKernel_one (r : α → ℕ) :
    barKernel r (1 : IncidenceAlgebra (Polynomial ℤ) α) = 1 := by
  apply IncidenceAlgebra.ext
  intro a b _
  simp only [barKernel_apply, IncidenceAlgebra.one_apply]
  by_cases h : a = b
  · subst b
    simp [reflect_one]
  · simp [h]

omit [DecidableLE α] in
theorem klKernel_rankBounded (r : α → ℕ) : RankBounded r (klKernel r) :=
  fun a b _ => kl_natDegree_le r a b

omit [DecidableLE α] in
theorem klInverseKernel_rankBounded (r : α → ℕ) (hr : Monotone r) :
    RankBounded r (klInverseKernel r) := by
  intro a b hab
  change (klInverse r a b).natDegree ≤ _
  by_cases he : a = b
  · subst b
    simp
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact klInverse_high_coeff r hr a b hab he i (by omega)

omit [DecidableLE α] in
theorem rankMu_rankBounded (r : α → ℕ) : RankBounded r (rankMu r) := by
  intro a b _
  change (C (IncidenceAlgebra.mu ℤ a b) * X ^ (r b - r a)).natDegree ≤ _
  exact (natDegree_mul_le).trans (by simp)

omit [DecidableLE α] in
@[simp] theorem barKernel_rankMu (r : α → ℕ) : barKernel r (rankMu r) = constantMu := by
  apply IncidenceAlgebra.ext
  intro a b _
  change reflect (r b - r a) (C (IncidenceAlgebra.mu ℤ a b) * X ^ (r b - r a)) = _
  rw [reflect_C_mul_X_pow]
  simp [constantMu]

theorem barKernel_kl (r : α → ℕ) (hr : Monotone r) :
    barKernel r (klKernel r) = constantMu * rankZeta r * klKernel r := by
  apply IncidenceAlgebra.ext
  intro a b hab
  rw [barKernel_apply, klKernel_apply, kl_functional_equation r hr a b hab,
    IncidenceAlgebra.mul_apply]
  apply sum_congr rfl
  intro x _
  rw [characteristic_incidence]
  rfl

/-- Reversal of the actual inverse KL kernel, with no assumed inverse-Q formula. -/
theorem barKernel_klInverse (r : α → ℕ) (hr : Monotone r) :
    barKernel r (klInverseKernel r) = klInverseKernel r * rankMu r * IncidenceAlgebra.zeta _ := by
  apply incidence_leftInverse_unique (barKernel r (klKernel r))
  · intro x
    simp [reflect_one]
  · rw [← barKernel_mul r hr _ _ (klInverseKernel_rankBounded r hr) (klKernel_rankBounded r),
      klInverseKernel_mul_klKernel, barKernel_one]
  · rw [barKernel_kl r hr]
    calc
      _ = klInverseKernel r * rankMu r *
          (IncidenceAlgebra.zeta (Polynomial ℤ) * constantMu) * rankZeta r * klKernel r := by
        simp only [mul_assoc]
      _ = klInverseKernel r * (rankMu r * rankZeta r) * klKernel r := by
        rw [zeta_mul_constantMu]
        simp only [mul_one, mul_assoc]
      _ = 1 := by rw [rankMu_mul_rankZeta r hr, mul_one, klInverseKernel_mul_klKernel]

/-- The unsigned incidence product underlying inverse-Z is rank-palindromic. -/
theorem barKernel_inverseZ_product (r : α → ℕ) (hr : Monotone r) :
    barKernel r (klInverseKernel r * rankMu r) = klInverseKernel r * rankMu r := by
  rw [barKernel_mul r hr _ _ (klInverseKernel_rankBounded r hr) (rankMu_rankBounded r),
    barKernel_klInverse r hr, barKernel_rankMu, mul_assoc, zeta_mul_constantMu, mul_one]

omit [DecidableLE α] in
/-- Exact sign normalization between the original inverse-Z definition and
its incidence-algebra product. -/
theorem inverseZ_eq_signed_product (r : α → ℕ) (hr : Monotone r) (a b : α) :
    inverseZ r a b = C ((-1 : ℤ) ^ (r b - r a)) *
      (klInverseKernel r * rankMu r) a b := by
  rw [inverseZ, IncidenceAlgebra.mul_apply, mul_sum]
  apply sum_congr rfl
  intro x hx
  have ha := hr (mem_Icc.mp hx).1
  have hb := hr (mem_Icc.mp hx).2
  have he : r b - r a = (r b - r x) + (r x - r a) := by omega
  simp only [inverseKL, klInverseKernel_apply, rankMu, IncidenceAlgebra.coe_mk]
  rw [he, pow_add, map_mul, map_mul]
  ring

/-- Full rank reversal of the actual ordinary inverse-Z polynomial. -/
theorem inverseZ_reflect (r : α → ℕ) (hr : Monotone r) (a b : α) :
    reflect (r b - r a) (inverseZ r a b) = inverseZ r a b := by
  rw [inverseZ_eq_signed_product r hr, reflect_C_mul]
  have h := congrArg (fun f : IncidenceAlgebra (Polynomial ℤ) α => f a b)
    (barKernel_inverseZ_product r hr)
  rw [barKernel_apply] at h
  rw [h]

theorem inverseZ_coeff_symm (r : α → ℕ) (hr : Monotone r) (a b : α)
    (k : ℕ) (hk : k ≤ r b - r a) :
    (inverseZ r a b).coeff k = (inverseZ r a b).coeff (r b - r a - k) := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff k) (inverseZ_reflect r hr a b)
  simpa only [coeff_reflect, revAt_le hk] using h.symm

end MatroidInverseZ
