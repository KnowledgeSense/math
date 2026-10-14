import CokernelPolynomiality.OrderedGraphs
import Mathlib.Tactic.Order

namespace CokernelPolynomiality

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- Replace each ordered vertex by a clique of true twins. -/
def twinExpansion (G : SimpleGraph V) (f : W → V) : SimpleGraph W where
  Adj u v := u ≠ v ∧ (f u = f v ∨ G.Adj (f u) (f v))
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with he | ha
    · exact Or.inl he.symm
    · exact Or.inr ha.symm⟩
  loopless := ⟨by intro u; simp⟩

 omit [LinearOrder V] [LinearOrder W] in
 theorem expanded_adj_projection {G : SimpleGraph V} {f : W → V} {u v : W}
    (h : (twinExpansion G f).Adj u v) (hne : f u ≠ f v) : G.Adj (f u) (f v) :=
  h.2.resolve_left hne

 theorem twinExpansion_ruleP (G : SimpleGraph V) (hG : RuleP G)
    (f : W → V) (hf : Monotone f) : RuleP (twinExpansion G f) := by
  intro s t x y hst hxy hsx hxt hty
  refine ⟨ne_of_lt hty, ?_⟩
  by_cases hty' : f t = f y
  · exact Or.inl hty'
  · apply Or.inr
    have hsx' := hf hsx
    have hxt' := hf (le_of_lt hxt)
    have htylt : f t < f y := lt_of_le_of_ne (hf (le_of_lt hty)) hty'
    by_cases hxtEq : f x = f t
    · have hproj := expanded_adj_projection hxy (by order)
      simpa only [hxtEq] using hproj
    · have hxtlt : f x < f t := lt_of_le_of_ne hxt' hxtEq
      exact hG (f s) (f t) (f x) (f y)
        (expanded_adj_projection hst (by order))
        (expanded_adj_projection hxy (by order)) hsx' hxtlt htylt

 theorem monotone_max (f : W → V) (hf : Monotone f) (u v : W) :
    f (max u v) = max (f u) (f v) := by
  rcases le_total u v with huv | hvu
  · simp only [max_eq_right huv, max_eq_right (hf huv)]
  · simp only [max_eq_left hvu, max_eq_left (hf hvu)]

/-- The collapsed-strict-inequality case in the three-input closure rule. -/
 theorem twinExpansion_ruleQ_collapsed (G : SimpleGraph V) (hG : RuleP G)
    (f : W → V) (hf : Monotone f)
    (s t x y z w : W)
    (hst : (twinExpansion G f).Adj s t)
    (hxy : (twinExpansion G f).Adj x y)
    (hzw : (twinExpansion G f).Adj z w)
    (_hsx : s ≤ x) (_hxt : x < t) (hty : t ≤ y)
    (hsz : s ≤ z) (hzt : z < t) (htw : t ≤ w)
    (hxtEq : f x = f t)
    (hout : f (max x z) ≠ f (max y w)) :
    G.Adj (f (max x z)) (f (max y w)) := by
  have hfxz : f (max x z) = f t := by
    rw [monotone_max f hf, hxtEq, max_eq_left (hf (le_of_lt hzt))]
  rw [hfxz] at hout ⊢
  have hty' := hf hty
  have htw' := hf htw
  have hsz' := hf hsz
  have hzt' := hf (le_of_lt hzt)
  rcases le_total w y with hwy | hyw
  · rw [max_eq_left hwy] at hout ⊢
    have hproj := expanded_adj_projection hxy (by order)
    simpa only [hxtEq] using hproj
  · rw [max_eq_right hyw] at hout ⊢
    by_cases hztEq : f z = f t
    · have hproj := expanded_adj_projection hzw (by order)
      simpa only [hztEq] using hproj
    · have hztlt : f z < f t := lt_of_le_of_ne hzt' hztEq
      have htwlt : f t < f w := lt_of_le_of_ne htw' hout
      exact hG (f s) (f t) (f z) (f w)
        (expanded_adj_projection hst (by order))
        (expanded_adj_projection hzw (by order)) hsz' hztlt htwlt

 theorem twinExpansion_ruleQ (G : SimpleGraph V) (hG : Admissible G)
    (f : W → V) (hf : Monotone f) : RuleQ (twinExpansion G f) := by
  intro s t x y z w hst hxy hzw hsx hxt hty hsz hzt htw
  have hout : max x z < max y w := lt_of_lt_of_le (max_lt hxt hzt)
    (le_trans hty (le_max_left y w))
  refine ⟨ne_of_lt hout, ?_⟩
  by_cases hcollapse : f (max x z) = f (max y w)
  · exact Or.inl hcollapse
  · apply Or.inr
    by_cases hxtEq : f x = f t
    · exact twinExpansion_ruleQ_collapsed G hG.1 f hf s t x y z w
        hst hxy hzw hsx hxt hty hsz hzt htw hxtEq hcollapse
    · by_cases hztEq : f z = f t
      · have hh := twinExpansion_ruleQ_collapsed G hG.1 f hf s t z w x y
          hst hzw hxy hsz hzt htw hsx hxt hty hztEq
          (by simpa only [max_comm] using hcollapse)
        simpa only [max_comm] using hh
      · have hsx' := hf hsx
        have hsz' := hf hsz
        have hxtlt : f x < f t := lt_of_le_of_ne (hf (le_of_lt hxt)) hxtEq
        have hztlt : f z < f t := lt_of_le_of_ne (hf (le_of_lt hzt)) hztEq
        have hty' := hf hty
        have htw' := hf htw
        rw [monotone_max f hf, monotone_max f hf]
        exact hG.2 (f s) (f t) (f x) (f y) (f z) (f w)
          (expanded_adj_projection hst (by order))
          (expanded_adj_projection hxy (by order))
          (expanded_adj_projection hzw (by order))
          hsx' hxtlt hty' hsz' hztlt htw'

 theorem twinExpansion_admissible (G : SimpleGraph V) (hG : Admissible G)
    (f : W → V) (hf : Monotone f) : Admissible (twinExpansion G f) :=
  ⟨twinExpansion_ruleP G hG.1 f hf, twinExpansion_ruleQ G hG f hf⟩

end CokernelPolynomiality
