import SumsetRanges.OrdinaryReindexModel

namespace SumsetRanges

/-- The actual sparse and dense ordinary construction, embedded with the exact
 exponent of the release. -/
theorem ordinary_large_value_realized (h c b x : ℕ) (r u : ℕ → ℕ)
    (hh : 2≤h) (hk : h^2+2*h+2≤c+b) (hb : 2≤b)
    (hc : ordinaryNonfreeSize h r u≤c) (hx : b-1≤x) (hxb : x≤h*(b-2)+1) :
    ∃B : Finset ℤ,B.card=c+b ∧
      (∀a∈B,0≤a ∧ a≤((c+b)^(ordinaryExponent h):ℕ)) ∧
      ((ordinarySums B h).card:ℤ)=ordinaryValue h c b r u x := by
  classical
  let A := ordinaryLargeSet h c b x r u
  have hι := (ordinarySparseAtom_card h c r u hh hc).trans (Nat.le_add_right c b)
  have hτ : Fintype.card (OrdinarySparseTag h)+1≤2*h := by
    rw [ordinarySparseTag_card h hh]
    omega
  obtain ⟨B,hBc,hB,hBs⟩ := ordinary_finite_integer_model h (c+b) hh hk hι hτ A
    (card_ordinaryLargeSet h c b x r u hh (by omega) hc hx)
    (ordinaryLargeSet_bounds h c b x r u hh hb hxb)
  refine ⟨B,hBc,hB,?_⟩
  rw [hBs h le_rfl]
  exact ordinaryValue_actual h c b x r u hh

end SumsetRanges
