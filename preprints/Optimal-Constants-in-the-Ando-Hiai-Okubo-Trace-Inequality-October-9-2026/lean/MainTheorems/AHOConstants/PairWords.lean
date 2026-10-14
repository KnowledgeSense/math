import MainTheorems.AHOConstants.WordReduction
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Induction

namespace ResearchMain.AHOConstants

def pairWord (xs : List (ℝ × ℝ)) : TraceWord :=
  xs.flatMap (fun pq => [(true, pq.1), (false, pq.2)])

def StartsTrue (w : TraceWord) : Prop := ∀ x, w.head? = some x → x.1 = true

def EndsFalse (w : TraceWord) : Prop := ∀ x, w.getLast? = some x → x.1 = false

theorem no_adjacent_chain {w : TraceWord} (h : ¬AdjacentEqual w) :
    w.IsChain (fun x y => x.1 ≠ y.1) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y u v hw hxy
  rcases x with ⟨c, a⟩
  rcases y with ⟨d, b⟩
  dsimp at hxy
  subst d
  apply h
  exact ⟨u, v, c, a, b, by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hw⟩

theorem pairWord_cons (pq : ℝ × ℝ) (xs : List (ℝ × ℝ)) :
    pairWord (pq :: xs) = [(true, pq.1), (false, pq.2)] ++ pairWord xs := rfl

theorem paired_of_chain (w : TraceWord) (hc : w.IsChain (fun x y => x.1 ≠ y.1))
    (hs : StartsTrue w) (he : EndsFalse w) : ∃ xs, w = pairWord xs := by
  revert hc hs he
  induction w using List.twoStepInduction with
  | nil =>
    intro _ _ _
    exact ⟨[], rfl⟩
  | singleton x =>
    intro _ hs he
    have h₁ := hs x rfl
    have h₂ := he x rfl
    rw [h₁] at h₂
    cases h₂
  | cons_cons x y w ih _ =>
    intro hc hs he
    have hx := hs x rfl
    have hxy := (List.isChain_cons_cons.mp hc).1
    have hy : y.1 = false := by
      cases h : y.1
      · rfl
      · exact False.elim (hxy (hx.trans h.symm))
    have hcw : w.IsChain (fun x y => x.1 ≠ y.1) := hc.tail.tail
    have hsw : StartsTrue w := by
      cases w with
      | nil =>
        intro z hz
        simp at hz
      | cons z w =>
        intro t ht
        simp only [List.head?_cons, Option.some.injEq] at ht
        subst t
        have hyz := (List.isChain_cons_cons.mp hc.tail).1
        cases h : z.1
        · exact False.elim (hyz (hy.trans h.symm))
        · rfl
    have hew : EndsFalse w := by
      cases w with
      | nil =>
        intro z hz
        simp at hz
      | cons z w =>
        intro t ht
        apply he t
        simpa only [List.getLast?_cons_cons] using ht
    obtain ⟨xs, hxs⟩ := ih hcw hsw hew
    refine ⟨(x.2, y.2) :: xs, ?_⟩
    rcases x with ⟨c, a⟩
    rcases y with ⟨d, b⟩
    dsimp at hx hy
    subst c
    subst d
    rw [pairWord_cons, ← hxs]
    rfl

theorem pairWord_mass_true (xs : List (ℝ × ℝ)) :
    exponentMass true (pairWord xs) = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => simp [pairWord, exponentMass]
  | cons pq xs ih =>
    rw [pairWord_cons, exponentMass_append, ih]
    simp [exponentMass]

theorem pairWord_mass_false (xs : List (ℝ × ℝ)) :
    exponentMass false (pairWord xs) = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => simp [pairWord, exponentMass]
  | cons pq xs ih =>
    rw [pairWord_cons, exponentMass_append, ih]
    simp [exponentMass]

theorem pairWord_positive {xs : List (ℝ × ℝ)} (h : WordPositive (pairWord xs)) :
    ∀ pq ∈ xs, 0 < pq.1 ∧ 0 < pq.2 := by
  intro pq hpq
  have hA : (true, pq.1) ∈ pairWord xs := by
    apply List.mem_flatMap.mpr
    exact ⟨pq, hpq, by simp⟩
  have hB : (false, pq.2) ∈ pairWord xs := by
    apply List.mem_flatMap.mpr
    exact ⟨pq, hpq, by simp⟩
  exact ⟨h _ hA, h _ hB⟩

theorem exponentMass_zero_of_no_colour (c : Bool) (w : TraceWord)
    (h : ∀ r : ℝ, (c, r) ∉ w) : exponentMass c w = 0 := by
  revert h
  induction w with
  | nil => intro _; simp [exponentMass]
  | cons cr w ih =>
    intro h
    have hc : cr.1 ≠ c := by
      intro hc
      rcases cr with ⟨d, r⟩
      dsimp at hc
      subst d
      exact h r (by simp)
    have ht := ih (fun r hr => h r (by simp [hr]))
    simp only [exponentMass, List.map_cons, List.sum_cons, hc, ite_false, zero_add]
    exact ht

theorem mass_nonzero_has_colour (c : Bool) (w : TraceWord) (h : exponentMass c w ≠ 0) :
    ∃ r : ℝ, (c, r) ∈ w := by
  by_contra hn
  push Not at hn
  exact h (exponentMass_zero_of_no_colour c w hn)

theorem normalized_head_ends_false (p : ℝ) (w : TraceWord)
    (hn : ¬CyclicEqual ((true, p) :: w))
    (hm : exponentMass false ((true, p) :: w) ≠ 0) : EndsFalse ((true, p) :: w) := by
  cases w with
  | nil =>
    exfalso
    apply hm
    simp [exponentMass]
  | cons y w =>
    intro cr hcr
    have hmem : cr ∈ ((true, p) :: y :: w).getLast? := by rw [hcr]; rfl
    have hsplit := List.dropLast_append_getLast? cr hmem
    have heq : (true, p) :: y :: w =
        [(true, p)] ++ (y :: w).dropLast ++ [cr] := by
      simpa only [List.dropLast_cons_cons, List.singleton_append, List.cons_append,
        List.nil_append] using hsplit.symm
    cases h : cr.1
    · rfl
    · exfalso
      rcases cr with ⟨c, q⟩
      dsimp at h
      subst c
      exact hn ⟨(y :: w).dropLast, true, p, q, heq⟩

end ResearchMain.AHOConstants
