import CokernelPolynomiality.TwinExpansion
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace CokernelPolynomiality

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- Admissibility is inherited by every order-preserving induced subgraph. -/
 theorem admissible_comap (G : SimpleGraph V) (hG : Admissible G)
    (f : W → V) (hf : StrictMono f) : Admissible (G.comap f) := by
  constructor
  · intro s t x y hst hxy hsx hxt hty
    exact hG.1 (f s) (f t) (f x) (f y) hst hxy (hf.monotone hsx) (hf hxt) (hf hty)
  · intro s t x y z w hst hxy hzw hsx hxt hty hsz hzt htw
    change G.Adj (f (max x z)) (f (max y w))
    rw [monotone_max f hf.monotone, monotone_max f hf.monotone]
    exact hG.2 (f s) (f t) (f x) (f y) (f z) (f w) hst hxy hzw
      (hf.monotone hsx) (hf hxt) (hf.monotone hty)
      (hf.monotone hsz) (hf hzt) (hf.monotone htw)

/-- Add a final interval of universal vertices. -/
def universalExtension (G : SimpleGraph V) (k : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (k ≤ u ∨ k ≤ v ∨ G.Adj u v)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hu | hv | huv
    · exact Or.inr (Or.inl hu)
    · exact Or.inl hv
    · exact Or.inr (Or.inr huv.symm)⟩
  loopless := ⟨by intro u; simp⟩

 theorem universalExtension_projection {G : SimpleGraph V} {k u v : V}
    (h : (universalExtension G k).Adj u v) (hu : u < k) (hv : v < k) :
    G.Adj u v := (h.2.resolve_left (not_le.mpr hu)).resolve_left (not_le.mpr hv)

 theorem universalExtension_admissible (G : SimpleGraph V) (hG : Admissible G)
    (k : V) : Admissible (universalExtension G k) := by
  constructor
  · intro s t x y hst hxy hsx hxt hty
    refine ⟨ne_of_lt hty, ?_⟩
    by_cases hky : k ≤ y
    · exact Or.inr (Or.inl hky)
    · apply Or.inr ∘ Or.inr
      have hyk : y < k := lt_of_not_ge hky
      exact hG.1 s t x y
        (universalExtension_projection hst (by order) (by order))
        (universalExtension_projection hxy (by order) hyk) hsx hxt hty
  · intro s t x y z w hst hxy hzw hsx hxt hty hsz hzt htw
    have hsep : max x z < max y w := lt_of_lt_of_le (max_lt hxt hzt)
      (le_trans hty (le_max_left y w))
    refine ⟨ne_of_lt hsep, ?_⟩
    by_cases hky : k ≤ max y w
    · exact Or.inr (Or.inl hky)
    · apply Or.inr ∘ Or.inr
      have hyk : y < k := lt_of_le_of_lt (le_max_left y w) (lt_of_not_ge hky)
      have hwk : w < k := lt_of_le_of_lt (le_max_right y w) (lt_of_not_ge hky)
      exact hG.2 s t x y z w
        (universalExtension_projection hst (by order) (by order))
        (universalExtension_projection hxy (by order) hyk)
        (universalExtension_projection hzw (by order) hwk)
        hsx hxt hty hsz hzt htw

end CokernelPolynomiality
