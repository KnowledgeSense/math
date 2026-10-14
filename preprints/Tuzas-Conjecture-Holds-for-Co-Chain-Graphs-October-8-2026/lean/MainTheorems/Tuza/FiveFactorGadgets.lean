import MainTheorems.Tuza.ThreeFactorInflation
import MainTheorems.Tuza.DecompositionTransport

namespace ResearchMain.Tuza

theorem five_factor_six : Nonempty (FactorDecomposition (ZMod 6) (Fin 5)) := by
  classical
  let e : Fin 6 ≃ ZMod 6 := Fintype.equivOfCardEq (by simp)
  exact sixFactorDecomposition.congr e (Equiv.refl _)

theorem five_factor_two_three : Nonempty (FactorDecomposition (Fin 2 × ZMod 3) (Fin 5)) := by
  classical
  let e : Fin 6 ≃ Fin 2 × ZMod 3 := Fintype.equivOfCardEq (by simp)
  exact sixFactorDecomposition.congr e (Equiv.refl _)

theorem five_factor_two_six : Nonempty (FactorDecomposition (Fin 2 × ZMod 6) (Fin 5)) := by
  classical
  obtain ⟨D⟩ := inflate_three_factor_decomposition fourFactorDecomposition
  let e : Fin 4 × ZMod 3 ≃ Fin 2 × ZMod 6 := Fintype.equivOfCardEq (by simp)
  let f : Fin 2 ⊕ ZMod 3 ≃ Fin 5 := Fintype.equivOfCardEq (by simp)
  exact D.congr e f

end ResearchMain.Tuza
