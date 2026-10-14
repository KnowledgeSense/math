import Fan.ConfigurationBounds

namespace Fan
open Finset IncidenceAlgebra

/-- A finite upper Möbius column is determined by its interval sums. -/
theorem mu_column_unique {α : Type*} [PartialOrder α] [OrderTop α]
    [LocallyFiniteOrder α] [DecidableEq α] (f : α → ℤ)
    (hf : ∀ x, ∑ y ∈ Icc x ⊤, f y=if x=⊤ then 1 else 0) (x : α) :
    f x=IncidenceAlgebra.mu ℤ x ⊤ := by
  classical
  have h := IncidenceAlgebra.moebius_inversion_top f (fun x => if x=⊤ then 1 else 0)
    (fun x => by simpa only [Ici_eq_Icc] using (hf x).symm) x
  simpa using h

noncomputable def upperMu {n : ℕ} (p : Configuration n) : ℤ :=
  IncidenceAlgebra.mu ℤ p ⊤

theorem upperMu_sum {n : ℕ} (p : Configuration n) :
    (∑ q : Configuration n, if p≤q then upperMu q else 0)=if p=⊤ then 1 else 0 := by
  classical
  have hi : Icc p ⊤=univ.filter (p≤·) := by ext q; simp
  rw [← sum_filter,← hi]
  exact IncidenceAlgebra.sum_Icc_mu_left p ⊤

end Fan
