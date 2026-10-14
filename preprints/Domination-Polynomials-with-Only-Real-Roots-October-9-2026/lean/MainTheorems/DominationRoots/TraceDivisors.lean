import MainTheorems.DominationRoots.Reflection

namespace ResearchMain.DominationRoots

open Polynomial

theorem reflection_mul {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic) :
    reflection (f * g) = reflection f * reflection g := by
  unfold reflection
  rw [hf.natDegree_mul hg, pow_add, C_mul, mul_comp]
  ring

theorem reflection_dvd {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic) (h : f ∣ g) :
    reflection f ∣ reflection g := by
  obtain ⟨q, rfl⟩ := h
  have hq : q.Monic := hf.of_mul_monic_left hg
  exact ⟨reflection q, reflection_mul hf hq⟩

theorem allowedProduct_of_monic_dvd {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic)
    (ht : TotallyPositive f) (ha : AllowedProduct f) (hd : g ∣ f) : AllowedProduct g := by
  obtain ⟨q, he⟩ := hd
  have hq : q.Monic := hg.of_mul_monic_left (he ▸ hf)
  have htg := totallyPositive_of_dvd hf hg ht ⟨q, he⟩
  have htq := totallyPositive_of_dvd hf hq ht ⟨g, he.trans (mul_comm _ _)⟩
  obtain ⟨hbg, heg⟩ := rootTrace_classification hg htg
  have hbq := (rootTrace_classification hq htq).1
  have htrace := allowedProduct_trace ha
  rw [he, rootTrace_mul hg hq, hg.natDegree_mul hq, Nat.cast_add] at htrace
  exact heg.mp (by linarith)

end ResearchMain.DominationRoots
