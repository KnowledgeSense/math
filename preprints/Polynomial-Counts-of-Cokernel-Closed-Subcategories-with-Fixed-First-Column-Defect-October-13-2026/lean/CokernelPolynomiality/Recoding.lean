import CokernelPolynomiality.Levels

namespace CokernelPolynomiality
noncomputable section

variable {i q m : ℕ} (e : ℕ → ℕ) (he : StrictMono e) (heq : e q = m)

def recodeLevel (k : Fin (q+1)) : Fin (m+1) :=
  ⟨e k, by have hh := he.monotone (show k.val ≤ q by omega); omega⟩

 theorem recodeLevel_monotone : Monotone (recodeLevel e he heq) := by
  intro j k hjk
  exact he.monotone hjk

 theorem recodeLevel_strictMono : StrictMono (recodeLevel e he heq) := by
  intro j k hjk
  exact he hjk

variable (hzero : e 0 = 0)

def contractRegular (t : Fin m) : Fin q :=
  ⟨levelCeil e he (t.val+1)-1, by
    have hp := levelCeil_positive e he hzero (t.val+1) (by omega)
    have hb := (levelCeil_le_iff e he (t.val+1) q).mpr (by omega)
    omega⟩

 theorem contractRegular_succ (t : Fin m) :
    (contractRegular e he heq hzero t).val+1 = levelCeil e he (t.val+1) := by
  simp only [contractRegular]
  have hp := levelCeil_positive e he hzero (t.val+1) (by omega)
  omega

def contractVertex : Vertex i m → Vertex i q
  | .root => .root
  | .exceptional j => .exceptional j
  | .regular t => .regular (contractRegular e he heq hzero t)

 theorem contractRegular_monotone : Monotone (contractRegular e he heq hzero) := by
  intro s t hst
  have hh := levelCeil_monotone e he (show s.val+1 ≤ t.val+1 by omega)
  change levelCeil e he (s.val+1)-1 ≤ levelCeil e he (t.val+1)-1
  omega

 theorem contractVertex_monotone (d : Fin i → Fin (q+1)) (hd : Monotone d) :
    @Monotone (Vertex i m) (Vertex i q)
      (codeOrder (fun j => recodeLevel e he heq (d j))).toPreorder
      (codeOrder d).toPreorder (contractVertex e he heq hzero) := by
  let _ := codeOrder d
  let _ := codeOrder (fun j => recodeLevel e he heq (d j))
  have hdm : Monotone (fun j => recodeLevel e he heq (d j)) :=
    (recodeLevel_monotone e he heq).comp hd
  intro u v huv
  rcases lt_or_eq_of_le huv with huv | rfl
  · cases u with
    | root =>
      cases v with
      | root => exact False.elim ((lt_irrefl _) huv)
      | exceptional j => exact le_of_lt (root_lt_exceptional d j)
      | regular t => exact le_of_lt (root_lt_regular d _)
    | exceptional j =>
      cases v with
      | root => exact False.elim (not_lt_of_gt (root_lt_exceptional _ j) huv)
      | exceptional k =>
        have hjk := (exceptional_lt_exceptional _ hdm j k).mp huv
        exact le_of_lt ((exceptional_lt_exceptional d hd j k).mpr hjk)
      | regular t =>
        have hdt := (exceptional_lt_regular _ j t).mp huv
        have hceil : (d j).val < levelCeil e he (t.val+1) :=
          (lt_levelCeil_iff e he (t.val+1) (d j)).mpr (by change e (d j) ≤ t.val at hdt; omega)
        apply le_of_lt
        apply (exceptional_lt_regular d j _).mpr
        change (d j).val ≤ levelCeil e he (t.val+1)-1
        omega
    | regular t =>
      cases v with
      | root => exact False.elim (not_lt_of_gt (root_lt_regular _ t) huv)
      | exceptional j =>
        have htd := (regular_lt_exceptional _ t j).mp huv
        have hceil : levelCeil e he (t.val+1) ≤ (d j).val :=
          (levelCeil_le_iff e he (t.val+1) (d j)).mpr (by change t.val < e (d j) at htd; omega)
        have hp := levelCeil_positive e he hzero (t.val+1) (by omega)
        apply le_of_lt
        apply (regular_lt_exceptional d _ j).mpr
        change levelCeil e he (t.val+1)-1 < (d j).val
        omega
      | regular s =>
        have hts := (regular_lt_regular _ t s).mp huv
        have hh := contractRegular_monotone e he heq hzero (le_of_lt hts)
        rcases lt_or_eq_of_le hh with hh | hh
        · exact le_of_lt ((regular_lt_regular d _ _).mpr hh)
        · change Vertex.regular (contractRegular e he heq hzero t) ≤
            Vertex.regular (contractRegular e he heq hzero s)
          rw [hh]
  · exact le_rfl

 theorem recoded_graph_twinExpansion (y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i)) :
    codeGraph (fun j => recodeLevel e he heq (y j)) E =
      twinExpansion (codeGraph y E) (contractVertex e he heq hzero) := by
  ext u v
  cases u with
  | root =>
    cases v <;> simp [codeGraph,codeAdj,twinExpansion,contractVertex]
  | exceptional j =>
    cases v with
    | root => simp [codeGraph,codeAdj,twinExpansion,contractVertex]
    | exceptional k =>
      simp only [codeGraph,codeAdj,twinExpansion,contractVertex,ne_eq,Vertex.exceptional.injEq]
      constructor
      · intro h; exact ⟨h.ne,Or.inr h⟩
      · intro h; exact h.2.resolve_left h.1
    | regular t =>
      simp only [codeGraph,codeAdj,twinExpansion,contractVertex]
      simp only [ne_eq,reduceCtorEq,not_false_eq_true,true_and,false_or]
      rw [contractRegular_succ]
      exact (lt_levelCeil_iff e he (t.val+1) (y j)).symm
  | regular t =>
    cases v with
    | root => simp [codeGraph,codeAdj,twinExpansion,contractVertex]
    | exceptional j =>
      simp only [codeGraph,codeAdj,twinExpansion,contractVertex]
      simp only [ne_eq,reduceCtorEq,not_false_eq_true,true_and,false_or]
      rw [contractRegular_succ]
      exact (lt_levelCeil_iff e he (t.val+1) (y j)).symm
    | regular s =>
      simp [codeGraph,codeAdj,twinExpansion,contractVertex,ne_eq,Vertex.regular.injEq,
        or_not]

 include hzero in
 theorem recoded_admissible (d y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i))
    (hd : Monotone d)
    (hG : @Admissible (Vertex i q) (codeOrder d) (codeGraph y E)) :
    @Admissible (Vertex i m)
      (codeOrder (fun j => recodeLevel e he heq (d j)))
      (codeGraph (fun j => recodeLevel e he heq (y j)) E) := by
  let _ := codeOrder d
  let _ := codeOrder (fun j => recodeLevel e he heq (d j))
  rw [recoded_graph_twinExpansion e he heq hzero]
  exact twinExpansion_admissible _ hG _ (contractVertex_monotone e he heq hzero d hd)

end
end CokernelPolynomiality
