import MainTheorems.Chollet.RankCoefficients.EdgeColumn
import MainTheorems.Chollet.RankCoefficients.FixedColumns

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I E : Type*} [Fintype I] [DecidableEq I]

def edgeColumns (edges : E → UnitEdge I) (w : E → ℂ) : Matrix I E ℂ :=
  fun i e => w e * (edges e).column i

omit [DecidableEq I] in
theorem linearForm_scale (x : I → ℂ) (c : ℂ) :
    linearForm (fun i => c * x i) = scalar c * linearForm x := by
  simp only [linearForm, scalar_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weighted_normal_form (edges : E → UnitEdge I) (w : E → ℂ)
    (s : Finset I) (l : s → E) :
    ∃ p : RootedPartition I, ∃ c : ℂ,
      (∏ j : s, linearForm (fun i => edgeColumns edges w i (l j))) =
        scalar c * p.polynomial ∧
      (c = 0 ∨ p.parts.card + s.card = Fintype.card I) := by
  classical
  let L := ((Finset.univ : Finset s).toList.map (fun j => edges (l j)))
  obtain ⟨p, c, hp, hc⟩ := edgeProduct_counted_normal_form L
  let W : ℂ := ∏ j : s, w (l j)
  have he : edgeProduct L = ∏ j : s, (edges (l j)).polynomial := by
    simp only [edgeProduct, L, List.map_map, Function.comp_def, Finset.prod_map_toList]
  have hlen : L.length = s.card := by simp [L]
  refine ⟨p, W * c, ?_, ?_⟩
  · simp only [edgeColumns, linearForm_scale, UnitEdge.linearForm_column,
      Finset.prod_mul_distrib, ← scalar_prod]
    rw [← he, hp, scalar_mul]
    ring
  · rcases hc with hc | hc
    · exact Or.inl (by rw [hc, mul_zero])
    · exact Or.inr (by rwa [hlen] at hc)

theorem remaining_equiv (p : RootedPartition I) (s : Finset I)
    (h : p.parts.card + s.card = Fintype.card I) :
    Nonempty (p.parts ≃ {i : I // i ∉ s}) := by
  apply Nonempty.intro
  apply Fintype.equivOfCardEq
  rw [Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_coe]
  omega

end ResearchMain.Chollet.RankCoefficients
