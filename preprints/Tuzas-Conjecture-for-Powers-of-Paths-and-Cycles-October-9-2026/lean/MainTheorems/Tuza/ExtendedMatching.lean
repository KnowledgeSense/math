import MainTheorems.Tuza.ReflectionMatching

namespace ResearchMain.Tuza

variable {K : Type*} [AddCommGroup K]

def extendedReflectionGraph (t : K) : SimpleGraph (Option K) where
  Adj x y := match x, y with
    | none, none => False
    | none, some y => y = t
    | some x, none => x = t
    | some x, some y => x ≠ y ∧ x + y = t + t
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> simp_all [ne_comm, add_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance [DecidableEq K] (t : K) : DecidableRel (extendedReflectionGraph t).Adj := by
  intro x y
  cases x <;> cases y <;> unfold extendedReflectionGraph <;> dsimp <;> infer_instance

theorem extended_factor_unique
    (hd : Function.Injective (fun x : K => x + x)) {t s : K} {x y : Option K}
    (ht : (extendedReflectionGraph t).Adj x y)
    (hs : (extendedReflectionGraph s).Adj x y) : t = s := by
  cases x with
  | none =>
    cases y with
    | none => exact False.elim ht
    | some y => exact (Eq.symm ht).trans hs
  | some x =>
    cases y with
    | none => exact (Eq.symm ht).trans hs
    | some y => exact hd (ht.2.symm.trans hs.2)

theorem extended_adj_unique {t : K} {x y z : Option K}
    (hy : (extendedReflectionGraph t).Adj x y)
    (hz : (extendedReflectionGraph t).Adj x z) : y = z := by
  cases x with
  | none =>
    cases y with
    | none => exact False.elim hy
    | some y =>
      cases z with
      | none => exact False.elim hz
      | some z => exact congrArg some (Eq.trans hy (Eq.symm hz))
  | some x =>
    cases y with
    | none =>
      cases z with
      | none => rfl
      | some z =>
        have hx : x = t := hy
        have hzt : z = t := add_left_cancel (hx ▸ hz.2)
        exact False.elim (hz.1 (hx.trans hzt.symm))
    | some y =>
      cases z with
      | none =>
        have hx : x = t := hz
        have hyt : y = t := add_left_cancel (hx ▸ hy.2)
        exact False.elim (hy.1 (hx.trans hyt.symm))
      | some z => exact congrArg some (add_left_cancel (hy.2.trans hz.2.symm))

variable [Fintype K] [DecidableEq K]

theorem extended_degree (hd : Function.Injective (fun x : K => x + x))
    (t : K) (x : Option K) : (extendedReflectionGraph t).degree x = 1 := by
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  cases x with
  | none =>
    refine ⟨some t, rfl, ?_⟩
    intro y hy
    exact extended_adj_unique hy rfl
  | some x =>
    by_cases hx : x = t
    · refine ⟨none, hx, ?_⟩
      intro y hy
      exact extended_adj_unique hy hx
    · have hne : x ≠ t + t - x := by
        intro hh
        apply hx
        apply hd
        calc
          x + x = (t + t - x) + x := congrArg (fun z => z + x) hh
          _ = t + t := sub_add_cancel _ _
      have ha : (extendedReflectionGraph t).Adj (some x) (some (t + t - x)) :=
        ⟨hne, by abel⟩
      exact ⟨some (t + t - x), ha, fun _ hy => extended_adj_unique hy ha⟩

theorem extended_card (hd : Function.Injective (fun x : K => x + x)) (t : K) :
    2 * (extendedReflectionGraph t).edgeFinset.card = Fintype.card K + 1 := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [extended_degree hd]
  simp

end ResearchMain.Tuza
