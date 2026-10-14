import MainTheorems.Domination.CompositionSelection

namespace ResearchMain.Domination

def compositionOfParts {r N : ℕ} (p : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ p i) (hsum : ∑ i, p i = N) : Composition N where
  blocks := List.ofFn p
  blocks_pos := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hpos i
  blocks_sum := by simpa only [List.sum_ofFn] using hsum

@[simp] theorem compositionOfParts_length {r N : ℕ} (p : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ p i) (hsum : ∑ i, p i = N) :
    (compositionOfParts p hpos hsum).length = r := by
  simp [compositionOfParts, Composition.length]

def fixedParts {N r : ℕ} (c : Composition N) (hlen : c.length = r) : Fin r → ℕ :=
  fun i => c.blocksFun (Fin.cast hlen.symm i)

theorem fixedParts_sum {N r : ℕ} (c : Composition N) (hlen : c.length = r) :
    ∑ i, fixedParts c hlen i = N := by
  calc
    (∑ i, fixedParts c hlen i) = ∑ i, c.blocksFun i :=
      Fintype.sum_equiv (finCongr hlen.symm) _ _ (fun _ => rfl)
    _ = N := c.sum_blocksFun

theorem fixedParts_ofParts {r N : ℕ} (p : Fin r → ℕ)
    (hpos : ∀ i, 1 ≤ p i) (hsum : ∑ i, p i = N) :
    fixedParts (compositionOfParts p hpos hsum) (compositionOfParts_length p hpos hsum) = p := by
  funext i
  simp only [fixedParts, compositionOfParts, Composition.blocksFun, List.get_eq_getElem,
    List.getElem_ofFn]
  congr 1

theorem fixedParts_eq_of_blocks {r N : ℕ} (c : Composition N) (p : Fin r → ℕ)
    (hlen : c.length = r) (hblocks : c.blocks = List.ofFn p) :
    fixedParts c hlen = p := by
  funext i
  simp only [fixedParts, Composition.blocksFun, List.get_eq_getElem, hblocks,
    List.getElem_ofFn]
  congr 1

theorem compositionOfParts_fixedParts {N r : ℕ} (c : Composition N) (hlen : c.length = r) :
    compositionOfParts (fixedParts c hlen)
      (fun i => c.one_le_blocksFun (Fin.cast hlen.symm i)) (fixedParts_sum c hlen) = c := by
  cases hlen
  apply Composition.ext
  change List.ofFn (fun i => c.blocksFun (Fin.cast rfl i)) = c.blocks
  simpa only [Fin.cast_refl, id_eq] using c.ofFn_blocksFun

def PositiveParts (r N : ℕ) :=
  {p : Fin r → ℕ // (∀ i, 1 ≤ p i) ∧ ∑ i, p i = N}

def fixedCompositionEquiv (N r : ℕ) :
    {c : Composition N // c.length = r} ≃ PositiveParts r N where
  toFun c := ⟨fixedParts c.1 c.2,
    (fun i => c.1.one_le_blocksFun (Fin.cast c.2.symm i)), fixedParts_sum c.1 c.2⟩
  invFun p := ⟨compositionOfParts p.1 p.2.1 p.2.2,
    compositionOfParts_length p.1 p.2.1 p.2.2⟩
  left_inv c := Subtype.ext (compositionOfParts_fixedParts c.1 c.2)
  right_inv p := Subtype.ext (fixedParts_ofParts p.1 p.2.1 p.2.2)

end ResearchMain.Domination
