import CokernelPolynomiality.OrderedGraphs

namespace CokernelPolynomiality

/-- Shift the source's vertex -1 to zero; (a,b) becomes edge a--(b+1). -/
def pointGraph (Y : Finset (ℕ × ℕ)) : SimpleGraph ℕ where
  Adj u v := (u < v ∧ (u,v-1) ∈ Y) ∨ (v < u ∧ (v,u-1) ∈ Y)
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro u; simp⟩

 theorem pointGraph_adj_iff {Y : Finset (ℕ × ℕ)} {u v : ℕ} (h : u < v) :
    (pointGraph Y).Adj u v ↔ (u,v-1) ∈ Y := by
  simp only [pointGraph, h, true_and, not_lt_of_ge (le_of_lt h), false_and, or_false]

 theorem pointGraph_point {Y : Finset (ℕ × ℕ)} {a b : ℕ} (h : a ≤ b) :
    (pointGraph Y).Adj a (b+1) ↔ (a,b) ∈ Y := by
  simpa using (pointGraph_adj_iff (Y := Y) (u := a) (v := b+1) (by omega))

 theorem closed_pointGraph_ruleP {Y : Finset (ℕ × ℕ)} (hY : IsClosed Y) :
    RuleP (pointGraph Y) := by
  intro s t x y hst hxy hsx hxt hty
  have hst' := (pointGraph_adj_iff (lt_of_le_of_lt hsx hxt)).mp hst
  have hxy' := (pointGraph_adj_iff (lt_trans hxt hty)).mp hxy
  have hh := (hY s (t-1) x (y-1) x (y-1) hst' hxy' hxy'
    hsx (by omega) (by omega) hsx (by omega) (by omega)).2 (by omega)
  apply (pointGraph_adj_iff hty).mpr
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t), min_self] using hh

 theorem closed_pointGraph_ruleQ {Y : Finset (ℕ × ℕ)} (hY : IsClosed Y) :
    RuleQ (pointGraph Y) := by
  intro s t x y z w hst hxy hzw hsx hxt hty hsz hzt htw
  have hst' := (pointGraph_adj_iff (lt_of_le_of_lt hsx hxt)).mp hst
  have hxy' := (pointGraph_adj_iff (lt_of_lt_of_le hxt hty)).mp hxy
  have hzw' := (pointGraph_adj_iff (lt_of_lt_of_le hzt htw)).mp hzw
  have hh := (hY s (t-1) x (y-1) z (w-1) hst' hxy' hzw'
    hsx (by omega) (by omega) hsz (by omega) (by omega)).1
  have hmax : max (y-1) (w-1) = max y w-1 := by omega
  have hsep : max x z < max y w := by omega
  apply (pointGraph_adj_iff hsep).mpr
  simpa only [hmax] using hh

 theorem closed_iff_pointGraph_admissible (Y : Finset (ℕ × ℕ))
    (htri : ∀ p ∈ Y, p.1 ≤ p.2) : IsClosed Y ↔ Admissible (pointGraph Y) := by
  constructor
  · intro hY
    exact ⟨closed_pointGraph_ruleP hY, closed_pointGraph_ruleQ hY⟩
  · intro hG a b c d e f hab hcd hef hac hcb hbd hae heb hbf
    have ha := htri (a,b) hab
    have hc := htri (c,d) hcd
    have he := htri (e,f) hef
    have hab' := (pointGraph_point ha).mpr hab
    have hcd' := (pointGraph_point hc).mpr hcd
    have hef' := (pointGraph_point he).mpr hef
    constructor
    · have hh := hG.2 a (b+1) c (d+1) e (f+1) hab' hcd' hef'
        hac (by omega) (by omega) hae (by omega) (by omega)
      have hmax : max (d+1) (f+1) = max d f+1 := by omega
      rw [hmax] at hh
      exact (pointGraph_point (by omega : max c e ≤ max d f)).mp hh
    · intro hbf'
      rcases le_total d f with hdf | hfd
      · have hh := hG.1 a (b+1) c (d+1) hab' hcd' hac (by omega) (by omega)
        have hp := (pointGraph_point (by omega : b+1 ≤ d)).mp hh
        simpa only [min_eq_left hdf] using hp
      · have hh := hG.1 a (b+1) e (f+1) hab' hef' hae (by omega) (by omega)
        have hp := (pointGraph_point (by omega : b+1 ≤ f)).mp hh
        simpa only [min_eq_right hfd] using hp

end CokernelPolynomiality
