import R34.ExpandedWords
import R34.KernelCollapse
import R34.ReducedCharge

noncomputable section

namespace R34.ExpandedCharge

open ChargeSites ExpandedWords ReducedCharge MvPolynomial
open scoped BigOperators

def chargedMatrices (sites : List (ChargedSite × List Bool)) :
    List (Transfer.Mat × List Bool) := sites.map (fun p => (p.1.matrix,p.2))

def chargedChain (first : ChargedSite) (gap : List Bool) :
    List (ChargedSite × List Bool) → ReducedCharge.Chain
  | [] => .last first
  | (next,nextGap) :: rest => .cons first (gapKernel gap) (chargedChain next nextGap rest)

theorem chargedChain_admissible (first : ChargedSite) (gap : List Bool)
    (rest : List (ChargedSite × List Bool)) : (chargedChain first gap rest).Admissible := by
  induction rest generalizing first gap with
  | nil => trivial
  | cons p rest ih =>
    exact ⟨⟨gap.count true,gapKernel_contracted gap⟩,ih p.1 p.2⟩

theorem gapMatrices_eq_neutral (gap : List Bool) :
    gapMatrices gap=gap.map ExpandedWords.neutralMatrix := by
  apply List.map_congr_left
  intro b hb
  cases b <;> simp [gapSite, ExpandedWords.neutralMatrix]

theorem collapsedSites_eq_matrixBlocks (leading : List Bool)
    (sites : List (ChargedSite × List Bool)) :
    collapsedSites leading (chargedMatrices sites)=
      matrixBlocks ChargedSite.matrix ⟨leading,sites⟩ := by
  unfold collapsedSites GapGrouping.flatten mappedBlocks chargedMatrices matrixBlocks
  rw [gapMatrices_eq_neutral]
  simp only [List.map_map, List.flatMap_map, Function.comp_def]
  congr 1
  apply List.flatMap_congr
  intro p hp
  rw [gapMatrices_eq_neutral]

theorem collapsedCore_eq_chargedChain (first : ChargedSite) (gap : List Bool)
    (rest : List (ChargedSite × List Bool)) :
    collapsedCore (chargedMatrices ((first,gap)::rest))=(chargedChain first gap rest).matrix := by
  induction rest generalizing first gap with
  | nil => rfl
  | cons p rest ih =>
    simp only [chargedMatrices, List.map_cons, collapsedCore, chargedChain, Chain.matrix] at *
    rw [ih]
    rfl

theorem charged_blocks_value (leading : List Bool) (first : ChargedSite) (gap : List Bool)
    (rest : List (ChargedSite × List Bool)) :
    Transfer.value (matrixBlocks ChargedSite.matrix ⟨leading,(first,gap)::rest⟩)=
      ReducedCharge.matrixValue (chargedChain first gap rest) (gapFree leading.reverse)
        (gapFree (lastGap (chargedMatrices ((first,gap)::rest)))) := by
  rw [← collapsedSites_eq_matrixBlocks]
  rw [collapsed_value leading (chargedMatrices ((first,gap)::rest)) (by simp [chargedMatrices])]
  rw [collapsedCore_eq_chargedChain]
  rfl

theorem expandedWord_schurPositive_of_reduced
    (hReduced : ∀ (ch : ReducedCharge.Chain) (left right : ℝ × ℝ),
      Free left → Free right → ch.Admissible → SchurPositive (ReducedCharge.matrixValue ch left right))
    (word : List (ExpandedWords.Atom ChargedSite)) :
    SchurPositive (Transfer.value (word.map (atomMatrix ChargedSite.matrix))) := by
  rw [value_blocks]
  obtain ⟨leading,sites⟩ := blocks word
  cases sites with
  | nil =>
    simp only [matrixBlocks, List.flatMap_nil, List.append_nil]
    rw [← gapMatrices_eq_neutral, neutral_value_eq]
    have hp := schurPositive_scale (neutralScalar leading) (neutralScalar_positive leading).le schurPositive_one
    simpa using hp
  | cons p rest =>
    rw [charged_blocks_value]
    apply hReduced
    · exact gapFree_free _
    · exact gapFree_free _
    · exact chargedChain_admissible p.1 p.2 rest

theorem expandedWord_schurPositive
    (word : List (ExpandedWords.Atom ChargedSite)) :
    SchurPositive (Transfer.value (word.map (atomMatrix ChargedSite.matrix))) :=
  expandedWord_schurPositive_of_reduced ReducedCharge.matrixValue_schurPositive word

end R34.ExpandedCharge

