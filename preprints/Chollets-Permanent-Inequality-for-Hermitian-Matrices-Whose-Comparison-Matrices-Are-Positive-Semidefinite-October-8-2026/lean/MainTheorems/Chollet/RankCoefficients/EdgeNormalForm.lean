import MainTheorems.Chollet.RankCoefficients.MergePartition

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

structure UnitEdge (I : Type*) where
  left : I
  right : I
  distinct : left ≠ right
  first : ℂ
  second : ℂ
  first_unit : ‖first‖ = 1
  second_unit : ‖second‖ = 1

def UnitEdge.polynomial (e : UnitEdge I) : SquareFree I :=
  scalar e.first * rowVariable e.left + scalar e.second * rowVariable e.right

omit [Fintype I] in
theorem RootedPartition.edge_factor (p : RootedPartition I) (e : UnitEdge I) :
    ∃ q : RootedPartition I, ∃ c : ℂ,
      e.polynomial * p.polynomial = scalar c * q.polynomial ∧
        (c = 0 ∨ q.parts.card + 1 = p.parts.card) := by
  by_cases hil : e.left ∈ p.closed
  · by_cases hir : e.right ∈ p.closed
    · refine ⟨p, 0, ?_, Or.inl rfl⟩
      have h := internal_edge_monomial p.closed hil hir e.first e.second
      change e.polynomial * (monomial p.closed * _) = _
      rw [← mul_assoc, UnitEdge.polynomial, h, zero_mul, scalar_zero, zero_mul]
    · obtain ⟨t, ht, hrt⟩ := (p.cover e.right).resolve_left hir
      let q := p.closePart t ht
      refine ⟨q, e.second * p.phase t e.right, ?_, Or.inr (p.closePart_card t ht)⟩
      apply p.closePart_factor t ht
      have he : e.polynomial = scalar e.second * rowVariable e.right +
          scalar e.first * rowVariable e.left := by
        unfold UnitEdge.polynomial
        ring
      rw [he]
      have hj := join_rooted_closed t p.closed (p.closed_disjoint t ht).symm
        (p.phase t) hrt hil e.second e.first
      rw [monomial_union t p.closed (p.closed_disjoint t ht).symm] at hj
      simpa only [mul_assoc] using hj
  · obtain ⟨s, hs, hls⟩ := (p.cover e.left).resolve_left hil
    by_cases hir : e.right ∈ p.closed
    · let q := p.closePart s hs
      refine ⟨q, e.first * p.phase s e.left, ?_, Or.inr (p.closePart_card s hs)⟩
      apply p.closePart_factor s hs
      have hj := join_rooted_closed s p.closed (p.closed_disjoint s hs).symm
        (p.phase s) hls hir e.first e.second
      rw [monomial_union s p.closed (p.closed_disjoint s hs).symm] at hj
      simpa only [UnitEdge.polynomial, mul_assoc] using hj
    · obtain ⟨t, ht, hrt⟩ := (p.cover e.right).resolve_left hir
      by_cases hst : s = t
      · subst t
        let q := p.closePart s hs
        refine ⟨q, e.first * p.phase s e.left + e.second * p.phase s e.right,
          ?_, Or.inr (p.closePart_card s hs)⟩
        apply p.closePart_factor s hs
        have h := internal_edge_rooted s (p.phase s) hls hrt e.first e.second
        change e.polynomial * rooted s (p.phase s) * _ = _
        rw [UnitEdge.polynomial, h]
      · let c : I → ℂ := fun r => if r ∈ s then
          e.second * p.phase t e.right * p.phase s r else
          e.first * p.phase s e.left * p.phase t r
        have hunit : ∀ r ∈ s ∪ t, ‖c r‖ = 1 :=
          joined_phases_unit s t (p.disjoint s hs t ht hst) (p.phase s) (p.phase t)
            hls hrt e.first e.second e.first_unit e.second_unit
            (p.unit s hs) (p.unit t ht)
        let q := p.mergeParts s t hs ht c hunit
        refine ⟨q, 1, ?_, Or.inr (p.mergeParts_card s t hs ht hst c hunit)⟩
        rw [scalar_one, one_mul]
        rw [p.polynomial_two_parts s t hs ht hst]
        rw [p.mergeParts_polynomial s t hs ht c hunit]
        have hj := join_rooted s t (p.disjoint s hs t ht hst) (p.phase s) (p.phase t)
          hls hrt e.first e.second
        calc
          e.polynomial * (rooted s (p.phase s) * rooted t (p.phase t) * monomial p.closed *
              ∏ r ∈ (p.parts.erase s).erase t, rooted r (p.phase r)) =
            (e.polynomial * rooted s (p.phase s) * rooted t (p.phase t)) *
              monomial p.closed * ∏ r ∈ (p.parts.erase s).erase t, rooted r (p.phase r) := by ring
          _ = _ := by rw [UnitEdge.polynomial, hj]

def edgeProduct (edges : List (UnitEdge I)) : SquareFree I := (edges.map UnitEdge.polynomial).prod

theorem edgeProduct_normal_form (edges : List (UnitEdge I)) :
    ∃ p : RootedPartition I, ∃ c : ℂ, edgeProduct edges = scalar c * p.polynomial := by
  induction edges with
  | nil =>
    refine ⟨RootedPartition.initial, 1, ?_⟩
    simp [edgeProduct]
  | cons e edges ih =>
    obtain ⟨p, c, hp⟩ := ih
    obtain ⟨q, d, hq, _⟩ := p.edge_factor e
    refine ⟨q, c * d, ?_⟩
    change e.polynomial * edgeProduct edges = _
    rw [hp, scalar_mul]
    calc
      e.polynomial * (scalar c * p.polynomial) =
        scalar c * (e.polynomial * p.polynomial) := by ring
      _ = _ := by rw [hq]; ring

theorem edgeProduct_counted_normal_form (edges : List (UnitEdge I)) :
    ∃ p : RootedPartition I, ∃ c : ℂ,
      edgeProduct edges = scalar c * p.polynomial ∧
        (c = 0 ∨ p.parts.card + edges.length = Fintype.card I) := by
  induction edges with
  | nil =>
    refine ⟨RootedPartition.initial, 1, ?_, Or.inr ?_⟩
    · simp [edgeProduct]
    · simp only [List.length_nil, add_zero, RootedPartition.initial_card]
  | cons e edges ih =>
    obtain ⟨p, c, hp, hpc⟩ := ih
    obtain ⟨q, d, hq, hqc⟩ := p.edge_factor e
    refine ⟨q, c * d, ?_, ?_⟩
    · change e.polynomial * edgeProduct edges = _
      rw [hp, scalar_mul]
      calc
        e.polynomial * (scalar c * p.polynomial) =
          scalar c * (e.polynomial * p.polynomial) := by ring
        _ = _ := by rw [hq]; ring
    · rcases hpc with hc | hpc
      · exact Or.inl (by rw [hc, zero_mul])
      · rcases hqc with hd | hqc
        · exact Or.inl (by rw [hd, mul_zero])
        · apply Or.inr
          simp only [List.length_cons]
          omega

end ResearchMain.Chollet.RankCoefficients
