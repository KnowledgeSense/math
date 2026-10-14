import MainTheorems.DominationRoots.LeafExtensions

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {C I : Type} {W : C → Type}

theorem extension_isolated_no_adj (H : SimpleGraph C) (i : I)
    (u : Σ j, LeafFiber I W j) : ¬(leafExtension H I W).Adj u ⟨none, i⟩ := by
  rcases u with ⟨_ | c, x⟩
  · exact id
  · cases x <;> exact id

theorem extension_leaf_adj (H : SimpleGraph C) (c : C) (w : W c)
    (u : Σ i, LeafFiber I W i) :
    (leafExtension H I W).Adj u ⟨some c, some w⟩ ↔ u = ⟨some c, none⟩ := by
  rcases u with ⟨_ | d, x⟩
  · constructor
    · exact False.elim
    · intro h
      have he := congrArg Sigma.fst h
      cases he
  · cases x with
    | none =>
      constructor
      · intro h
        change d = c at h
        subst d
        rfl
      · intro h
        exact Option.some.inj (congrArg Sigma.fst h)
    | some x =>
      constructor
      · exact False.elim
      · intro h
        have he := Option.some.inj (congrArg Sigma.fst h)
        subst d
        have hx := (Sigma.mk.inj_iff.mp h).2
        have hx' : some x = (none : Option (W c)) := eq_of_heq hx
        cases hx'

variable [Fintype C] [Fintype I] [∀ c, Fintype (W c)]

abbrev CoversLeafFiber (I : Type) [Fintype I] (W : C → Type) :
    ∀ i : Option C, Finset (LeafFiber I W i) → Prop
  | none, S => S = Finset.univ
  | some _, S => CoversStar S

omit [Fintype C] in
theorem extension_dominates_iff (H : SimpleGraph C) (hne : ∀ c, Nonempty (W c))
    (R : Finset (Σ i, LeafFiber I W i)) :
    Dominates (leafExtension H I W) R ↔ ∀ i, CoversLeafFiber I W i (subsetFiber R i) := by
  constructor
  · intro hdom i
    cases i with
    | none =>
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      obtain ⟨u, hu, he | hadj⟩ := hdom ⟨none, v⟩
      · subst u
        exact (mem_subsetFiber R none v).mpr hu
      · exact False.elim (extension_isolated_no_adj H v u hadj)
    | some c =>
      change none ∈ subsetFiber R (some c) ∨ ∀ w, some w ∈ subsetFiber R (some c)
      by_cases hc : none ∈ subsetFiber R (some c)
      · exact Or.inl hc
      · right
        intro w
        obtain ⟨u, hu, he | hadj⟩ := hdom ⟨some c, some w⟩
        · subst u
          exact (mem_subsetFiber R (some c) (some w)).mpr hu
        · have he := (extension_leaf_adj H c w u).mp hadj
          subst u
          exact False.elim (hc ((mem_subsetFiber R (some c) none).mpr hu))
  · intro hlocal z
    rcases z with ⟨_ | c, x⟩
    · have hm : x ∈ subsetFiber R none := by
        rw [show subsetFiber R none = Finset.univ from hlocal none]
        exact Finset.mem_univ _
      exact ⟨⟨none, x⟩, (mem_subsetFiber R none x).mp hm, Or.inl rfl⟩
    · rcases (show CoversStar (subsetFiber R (some c)) from hlocal (some c)) with hc | hl
      · have hm := (mem_subsetFiber R (some c) none).mp hc
        cases x with
        | none => exact ⟨⟨some c, none⟩, hm, Or.inl rfl⟩
        | some x => exact ⟨⟨some c, none⟩, hm, Or.inr rfl⟩
      · cases x with
        | none =>
          let w := Classical.choice (hne c)
          exact ⟨⟨some c, some w⟩, (mem_subsetFiber R (some c) (some w)).mp (hl w), Or.inr rfl⟩
        | some x =>
          exact ⟨⟨some c, some x⟩, (mem_subsetFiber R (some c) (some x)).mp (hl x), Or.inl rfl⟩

theorem dominationPolynomial_extension (H : SimpleGraph C) (hne : ∀ c, Nonempty (W c)) :
    dominationPolynomial (leafExtension H I W) =
      X ^ Fintype.card I * ∏ c, starFactor (Fintype.card (W c)) := by
  calc
    _ = ∑ R : Finset (Σ i, LeafFiber I W i),
        if ∀ i, CoversLeafFiber I W i (subsetFiber R i) then (X : ℤ[X]) ^ R.card else 0 := by
      simp [dominationPolynomial, allDominatingSets, Finset.sum_filter, extension_dominates_iff H hne]
    _ = ∏ i, ∑ S : Finset (LeafFiber I W i),
        if CoversLeafFiber I W i S then (X : ℤ[X]) ^ S.card else 0 := polynomial_fiber_sum _
    _ = _ := by
      rw [Fintype.prod_option]
      simp only [CoversLeafFiber, star_subset_polynomial]
      congr 1
      have hi := Fintype.sum_ite_eq' (Finset.univ : Finset I) (fun S => (X : ℤ[X]) ^ S.card)
      convert (show (∑ S : Finset I, if S = Finset.univ then (X : ℤ[X]) ^ S.card else 0) =
          X ^ Fintype.card I from by simpa only [Finset.card_univ] using hi) using 1
      apply Finset.sum_congr rfl
      intro S _
      by_cases hs : S = Finset.univ <;> simp [hs]

theorem leafExtension_realRooted (H : SimpleGraph C)
    (hs : ∀ c, Fintype.card (W c) = 1 ∨ Fintype.card (W c) = 2) :
    RealRooted (dominationPolynomial (leafExtension H I W)) := by
  have hne (c : C) : Nonempty (W c) := by
    apply Fintype.card_pos_iff.mp
    rcases hs c with h | h <;> omega
  rw [dominationPolynomial_extension H hne]
  unfold RealRooted realPolynomial
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod]
  apply (Splits.X_pow _).mul
  apply Splits.prod
  intro c _
  rcases hs c with h | h
  · simpa only [h, RealRooted, realPolynomial] using starFactor_one_realRooted
  · simpa only [h, RealRooted, realPolynomial] using starFactor_two_realRooted

end ResearchMain.DominationRoots
