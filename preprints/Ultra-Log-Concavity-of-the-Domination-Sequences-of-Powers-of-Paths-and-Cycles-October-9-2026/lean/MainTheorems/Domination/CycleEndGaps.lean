import MainTheorems.Domination.CycleCounts

namespace ResearchMain.Domination

open Classical

def collapseEnds {k : ℕ} (p : Fin (k + 2) → ℕ) : Fin (k + 1) → ℕ :=
  Fin.cons (p 0 + p (Fin.last (k + 1)) - 1) (fun i => p i.succ.castSucc)

def expandEnds {k : ℕ} (p : Fin (k + 1) → ℕ) (a : ℕ) : Fin (k + 2) → ℕ :=
  Fin.lastCases (p 0 + 1 - a) (Fin.cons a (fun i => p i.succ))

@[simp] theorem expandEnds_first {k : ℕ} (p : Fin (k + 1) → ℕ) (a : ℕ) :
    expandEnds p a 0 = a := by
  change expandEnds p a (0 : Fin (k + 1)).castSucc = a
  simp only [expandEnds, Fin.lastCases_castSucc, Fin.cons_zero]

@[simp] theorem expandEnds_last {k : ℕ} (p : Fin (k + 1) → ℕ) (a : ℕ) :
    expandEnds p a (Fin.last (k + 1)) = p 0 + 1 - a := by simp [expandEnds]

@[simp] theorem expandEnds_inner {k : ℕ} (p : Fin (k + 1) → ℕ) (a : ℕ) (i : Fin k) :
    expandEnds p a i.succ.castSucc = p i.succ := by
  simp only [expandEnds, Fin.lastCases_castSucc, Fin.cons_succ]

theorem parts_sum_endpoints {k : ℕ} (p : Fin (k + 2) → ℕ) :
    (∑ i, p i) = p 0 + (∑ i : Fin k, p i.succ.castSucc) + p (Fin.last (k + 1)) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  rfl

theorem collapse_expand {k : ℕ} (p : Fin (k + 1) → ℕ) (a : ℕ)
    (ha : 1 ≤ a) (hpa : a ≤ p 0) : collapseEnds (expandEnds p a) = p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [collapseEnds, Fin.cons_zero, expandEnds_first, expandEnds_last]
    omega
  · simp only [collapseEnds, Fin.cons_succ, expandEnds_inner]

theorem expand_collapse {k : ℕ} (p : Fin (k + 2) → ℕ)
    (hp : 1 ≤ p (Fin.last (k + 1))) : expandEnds (collapseEnds p) (p 0) = p := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [expandEnds_last, collapseEnds, Fin.cons_zero]
    omega
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact expandEnds_first _ _
    · simp only [expandEnds_inner, collapseEnds, Fin.cons_succ]

theorem collapseEnds_mem {n k m : ℕ} (p : Fin (k + 2) → ℕ)
    (hp : p ∈ cycleParts n k m) :
    collapseEnds p ∈ (boundedParts (fun _ : Fin (k + 1) => m)).filter
        (fun q => ∑ i, q i = n) ∧ p 0 ∈ Finset.Icc 1 (collapseEnds p 0) := by
  obtain ⟨hpsum, hend⟩ := Finset.mem_filter.mp hp
  obtain ⟨hparts, hsum⟩ := Finset.mem_filter.mp hpsum
  have hb := (mem_boundedParts _ p).mp hparts
  have h0 := (hb 0).1
  have hl := (hb (Fin.last (k + 1))).1
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · apply (mem_boundedParts _ _).mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [collapseEnds, Fin.cons_zero]
        omega
      · simpa only [collapseEnds, Fin.cons_succ] using hb j.succ.castSucc
    · have hs := parts_sum_endpoints p
      rw [Fin.sum_univ_succ]
      simp only [collapseEnds, Fin.cons_zero, Fin.cons_succ]
      omega
  · apply Finset.mem_Icc.mpr
    simp only [collapseEnds, Fin.cons_zero]
    omega

theorem expandEnds_mem {n k m : ℕ} (p : Fin (k + 1) → ℕ)
    (hp : p ∈ (boundedParts (fun _ : Fin (k + 1) => m)).filter (fun p => ∑ i, p i = n))
    (a : ℕ) (ha : a ∈ Finset.Icc 1 (p 0)) : expandEnds p a ∈ cycleParts n k m := by
  obtain ⟨hparts, hsum⟩ := Finset.mem_filter.mp hp
  have hb := (mem_boundedParts _ p).mp hparts
  obtain ⟨halo, hahi⟩ := Finset.mem_Icc.mp ha
  have h0 := hb 0
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · apply (mem_boundedParts _ _).mpr
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [expandEnds_last]
        omega
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [expandEnds, Fin.lastCases_castSucc, Fin.cons_zero]
          omega
        · simpa only [expandEnds_inner] using hb j.succ
    · rw [parts_sum_endpoints]
      simp only [expandEnds_first, expandEnds_inner, expandEnds_last]
      rw [Fin.sum_univ_succ] at hsum
      omega
  · simp only [expandEnds_first, expandEnds_last]
    omega

theorem cycleParts_card {n k m : ℕ} : (cycleParts n k m).card =
    ∑ p ∈ (boundedParts (fun _ : Fin (k + 1) => m)).filter (fun p => ∑ i, p i = n), p 0 := by
  let S := (boundedParts (fun _ : Fin (k + 1) => m)).filter (fun p => ∑ i, p i = n)
  calc
    (cycleParts n k m).card = (S.sigma (fun p => Finset.Icc 1 (p 0))).card := by
      apply Finset.card_bij (fun p _ => Sigma.mk (collapseEnds p) (p 0))
      · intro p hp
        exact Finset.mem_sigma.mpr (collapseEnds_mem p hp)
      · intro p hp q hq heq
        have hfirst := congrArg Sigma.fst heq
        change collapseEnds p = collapseEnds q at hfirst
        have hlast : p 0 = q 0 := congrArg (fun x => x.2) heq
        have hpLast := ((mem_boundedParts _ p).mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1 (Fin.last (k + 1))).1
        have hqLast := ((mem_boundedParts _ q).mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1 (Fin.last (k + 1))).1
        rw [← expand_collapse p hpLast, ← expand_collapse q hqLast, hfirst, hlast]
      · intro pa hpa
        obtain ⟨hp, ha⟩ := Finset.mem_sigma.mp hpa
        obtain ⟨halo, hahi⟩ := Finset.mem_Icc.mp ha
        refine ⟨expandEnds pa.1 pa.2, expandEnds_mem pa.1 hp pa.2 ha, ?_⟩
        apply Sigma.ext (collapse_expand pa.1 pa.2 halo hahi)
        simp only [expandEnds_first]
        rfl
    _ = ∑ p ∈ S, p 0 := by simp [Finset.card_sigma]

theorem cycleParts_card_moment (n k m : ℕ) :
    ((cycleParts n k m).card : ℤ) = compositionMoment (fun _ : Fin (k + 1) => m) n 0 := by
  rw [cycleParts_card, Nat.cast_sum]
  unfold compositionMoment
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Nat.cast_inj]

theorem cyclePower_count_composition (n k ℓ : ℕ) :
    ((k + 1 : ℕ) : ℤ) * dominationCount (cyclePower n ℓ) (k + 1) =
      (n : ℤ) * compositionCountZ (fun _ : Fin (k + 1) => 2 * ℓ + 1) n := by
  rw [dominationCount_cyclePower, cycleParts_card_moment]
  exact uniform_compositionMoment _ _ _

end ResearchMain.Domination
