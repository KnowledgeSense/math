import CokernelPolynomiality.Definitions
import Mathlib.Basic.Real.Basic

namespace CokernelPolynomiality

variable {V : Type*} [LinearOrder V]

/-- The threshold construction used for the highest-degree templates. -/
def thresholdGraph (p h : V → ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ h u < p v ∧ h v < p u
  symm := ⟨by
    intro u v huv
    exact ⟨Ne.symm huv.1, huv.2.2, huv.2.1⟩⟩
  loopless := ⟨by intro u; simp⟩

 theorem thresholdGraph_ruleP (p h : V → ℝ) (hp : StrictMono p) :
    RuleP (thresholdGraph p h) := by
  intro s t x y hst hxy hsx hxt hty
  exact ⟨ne_of_lt hty,
    lt_trans (lt_of_lt_of_le hst.2.2 (hp.monotone hsx))
      (hp (lt_trans hxt hty)),
    lt_trans hxy.2.2 (hp hxt)⟩

 theorem thresholdGraph_ruleQ (p h : V → ℝ) (hp : StrictMono p) :
    RuleQ (thresholdGraph p h) := by
  intro s t x y z w _ hxy hzw _ hxt hty _ hzt htw
  have hsep : max x z < min y w :=
    lt_of_lt_of_le (max_lt hxt hzt) (le_min hty htw)
  have hne : max x z ≠ max y w := ne_of_lt
    (lt_of_lt_of_le hsep (min_le_max (a := y) (b := w)))
  refine ⟨hne, ?_, ?_⟩
  · rcases le_total x z with hxz | hzx
    · rw [max_eq_right hxz]
      exact lt_of_lt_of_le hzw.2.1 (hp.monotone (le_max_right y w))
    · rw [max_eq_left hzx]
      exact lt_of_lt_of_le hxy.2.1 (hp.monotone (le_max_left y w))
  · rcases le_total y w with hyw | hwy
    · rw [max_eq_right hyw]
      exact lt_of_lt_of_le hzw.2.2 (hp.monotone (le_max_right x z))
    · rw [max_eq_left hwy]
      exact lt_of_lt_of_le hxy.2.2 (hp.monotone (le_max_left x z))

 theorem thresholdGraph_admissible (p h : V → ℝ) (hp : StrictMono p) :
    Admissible (thresholdGraph p h) :=
  ⟨thresholdGraph_ruleP p h hp, thresholdGraph_ruleQ p h hp⟩

/-- All neighbors of the least distinguished vertex form a clique. -/
 theorem root_neighbors_adj (G : SimpleGraph V) (hG : Admissible G)
    (ρ b c : V) (hρ : ρ < b) (hbc : b < c) (hb : G.Adj ρ b)
    (hc : G.Adj ρ c) : G.Adj b c :=
  hG.1 ρ b ρ c hb hc le_rfl hρ hbc

/-- A nonneighbor's neighborhood among regular vertices is a final segment. -/
 theorem regular_neighbors_final (G : SimpleGraph V) (hG : Admissible G)
    (ρ a b c : V) (hρa : ρ < a) (hρb : ρ < b) (hbc : b < c)
    (hb : G.Adj ρ b) (hc : G.Adj ρ c) (hab : G.Adj a b)
    (hac : a ≠ c) : G.Adj a c := by
  have hclique := root_neighbors_adj G hG ρ b c hρb hbc hb hc
  rcases lt_or_gt_of_ne hab.ne with hablt | hblt
  · have hmax : max a ρ = a := max_eq_left (le_of_lt hρa)
    have hh := hG.2 ρ b a b ρ c hb hab hc
      (le_of_lt hρa) hablt le_rfl le_rfl hρb (le_of_lt hbc)
    simpa only [hmax, max_eq_right (le_of_lt hbc)] using hh
  · rcases lt_or_gt_of_ne hac with haclt | hcalt
    · exact hG.1 b a b c hab.symm hclique le_rfl hblt haclt
    · exact (hG.1 ρ c b a hc hab.symm (le_of_lt hρb) hbc hcalt).symm

end CokernelPolynomiality
