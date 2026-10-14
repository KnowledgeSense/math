import EdgeColoringMixing.RootedInterpolation

set_option autoImplicit false

namespace EdgeColoringMixing
open Finset RootedCounting
universe u

/-- The endpoint estimate to be proved by the two exact buffer levels and the
Jacobian contraction. Every message and cutoff here belongs to an actual finite tree. -/
def RootMessageDecay (Δ q : ℕ) (κ E : ℝ) : Prop :=
  ∀ (V : Type u) (_ : Fintype V) (G : SimpleGraph V), G.IsTree →
    ∀ (r : V) (F F' : V → Finset (Fin q)),
      Nonempty (Coloring G q F) → Nonempty (Coloring G q F') →
      VertexBudget Δ q G F → VertexBudget Δ q G F' →
      RootBudget Δ q G r F → RootBudget Δ q G r F' →
      ∀ n : ℕ, 2 ≤ n → AgreeToDepth n G r q F F' →
        (∑ c, |rootAvailability (G := G) r q F c - rootAvailability (G := G) r q F' c|) ≤
          Real.sqrt q / 2 * (κ^(n - 2) * E)

end EdgeColoringMixing
