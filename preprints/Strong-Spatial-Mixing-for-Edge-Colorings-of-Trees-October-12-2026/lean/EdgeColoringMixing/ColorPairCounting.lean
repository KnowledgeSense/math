import EdgeColoringMixing.RootedCounting
import EdgeColoringMixing.ObservedMarginal

set_option autoImplicit false

namespace EdgeColoringMixing
open Finset
attribute [local instance] Classical.propDecidable

/-- Exact normalized product formula for the color fibers of a finite gluing bijection. -/
theorem normalized_color_pair_counts {q : ℕ} {A B Ω : Type*}
    [Fintype A] [Fintype B] [Fintype Ω]
    (P : Fin q → A → Prop) (Q : Fin q → B → Prop)
    (χ : Ω → Fin q)
    (E : Ω ≃ ((c : Fin q) × ({a : A // P c a} × {b : B // Q c b})))
    (hE : ∀ ω, (E ω).1 = χ ω)
    (hA : Nonempty A) (hB : Nonempty B) (c : Fin q) :
    (Fintype.card {ω : Ω // χ ω = c} : ℝ) / Fintype.card Ω =
      observedMarginal
        (fun b => (Fintype.card {a : A // P b a} : ℝ) / Fintype.card A)
        (fun a => (Fintype.card {b : B // Q a b} : ℝ) / Fintype.card B) c := by
  classical
  let := hA
  let := hB
  have hden : (Fintype.card Ω : ℝ) =
      ∑ b, (Fintype.card {a : A // P b a} : ℝ) * Fintype.card {a : B // Q b a} := by
    rw [Fintype.card_congr E, Fintype.card_sigma]
    simp only [Fintype.card_prod, Nat.cast_sum, Nat.cast_mul]
  have hnum : (Fintype.card {ω : Ω // χ ω = c} : ℝ) =
      (Fintype.card {a : A // P c a} : ℝ) * Fintype.card {b : B // Q c b} := by
    rw [Fintype.card_congr (E.subtypeEquiv
      (q := fun z => z.1 = c) (fun ω => by rw [hE]))]
    rw [RootedCounting.card_sigma_event (fun b : Fin q =>
      {a : A // P b a} × {a : B // Q b a}) (fun b => b = c)]
    simp
  have ha : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hden, hnum]
  unfold observedMarginal
  simp_rw [div_mul_div_comm, ← Finset.sum_div]
  field_simp

end EdgeColoringMixing
