import HonestEmbeddingDimension.ResidueOrders
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace HonestEmbeddingDimension

/-- The number of different value residues in a parameter-module span is at most its number of generators. -/
theorem distinct_residues_le_parameter_generators (p q m : ℕ) (hm : m ≠ 0)
    (f : Fin p → PowerSeries ℂ) (b : Fin q → PowerSeries ℂ)
    (c : Fin p → Fin q → PowerSeries ℂ) (a : Fin p → ℕ)
    (hf : ∀ i, (f i).order = a i)
    (ha : Function.Injective (fun i => a i % m))
    (hrep : ∀ i, f i = ∑ j, PowerSeries.expand m hm (c i j) * b j) : p ≤ q := by
  classical
  have hli : LinearIndependent (PowerSeries ℂ) c := by
    apply Fintype.linearIndependent_iff.mpr
    intro u hu
    have hrel : ∑ i, PowerSeries.expand m hm (u i) * f i = 0 := by
      simp_rw [hrep, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      have hj : ∑ i, u i * c i j = 0 := by
        have h := congrFun hu j
        simpa using h
      calc
        ∑ i, PowerSeries.expand m hm (u i) * (PowerSeries.expand m hm (c i j) * b j) =
            PowerSeries.expand m hm (∑ i, u i * c i j) * b j := by
              simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
        _ = 0 := by rw [hj, map_zero, zero_mul]
    have hz := parameter_relation_eq_zero Finset.univ m hm u f a
      (by intro i _; exact hf i)
      (by intro i _ j _ hij he; exact hij (ha he)) hrel
    intro i
    exact hz i (Finset.mem_univ i)
  have hb := hli.fintype_card_le_finrank
  simpa using hb

end HonestEmbeddingDimension
