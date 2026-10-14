import HonestEmbeddingDimension.PlaneValues

namespace HonestEmbeddingDimension

noncomputable def parameterAlgebra (m : ℕ) : Subalgebra ℂ (PowerSeries ℂ) :=
  Algebra.adjoin ℂ {PowerSeries.X ^ m}

theorem parameterAlgebra_le_expand_range (m : ℕ) (hm : m ≠ 0) :
    parameterAlgebra m ≤ (PowerSeries.expand m hm (R := ℂ)).range := by
  apply Algebra.adjoin_le
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact ⟨PowerSeries.X, PowerSeries.expand_X m hm⟩

theorem parameterAlgebra_values (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    n ∈ subalgebraValues (parameterAlgebra m) ↔ m ∣ n := by
  constructor
  · rintro ⟨f,hf,horder⟩
    obtain ⟨u,hu⟩ := parameterAlgebra_le_expand_range m hm hf
    have hu0 : u ≠ 0 := by
      intro hz
      have hf0 : f = 0 := by simpa [hz] using hu.symm
      simp [hf0] at horder
    rw [← hu] at horder
    change (PowerSeries.expand m hm u).order = n at horder
    rw [PowerSeries.order_expand, ← PowerSeries.coe_toNat_order hu0, nsmul_eq_mul] at horder
    have he : m*u.order.toNat = n := by exact_mod_cast horder
    exact ⟨u.order.toNat,he.symm⟩
  · rintro ⟨k,rfl⟩
    refine ⟨(PowerSeries.X ^ m)^k, ?_, ?_⟩
    · exact (parameterAlgebra m).pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) k
    · simp [PowerSeries.order_pow, nsmul_eq_mul, mul_comm]

end HonestEmbeddingDimension
