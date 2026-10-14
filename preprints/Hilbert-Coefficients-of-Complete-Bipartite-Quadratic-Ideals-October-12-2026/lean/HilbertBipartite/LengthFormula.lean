import HilbertBipartite.Membership
import HilbertBipartite.StandardCount

namespace HilbertBipartite

/-- The vector-space dimension formula for the quotient by every positive power
 of the complete-bipartite quadratic ideal over an arbitrary field. -/
theorem bipartiteIdeal_length_formula (K : Type*) [Field K]
    (p q s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s) :
    Module.finrank K (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) =
      (2*s+p+q-1).choose (p+q) + correction p q s + correction q p s := by
  rw [finrank_bipartiteIdeal_pow, standardExponents_card p q s hp hq hs]

end HilbertBipartite
