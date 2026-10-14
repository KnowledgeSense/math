import CokernelPolynomiality.Recoding

namespace CokernelPolynomiality
noncomputable section

variable {i q m : ℕ} (e : ℕ → ℕ) (he : StrictMono e) (heq : e q = m) (hzero : e 0 = 0)

def expandRegular (t : Fin q) : Fin m :=
  ⟨e (t.val+1)-1, by
    have hp := strictly_increasing_unbounded e he (t.val+1)
    have hb := he.monotone (show t.val+1 ≤ q by omega)
    omega⟩

 theorem expandRegular_succ (t : Fin q) :
    (expandRegular e he heq t).val+1 = e (t.val+1) := by
  simp only [expandRegular]
  have hp := strictly_increasing_unbounded e he (t.val+1)
  omega

def expandVertex : Vertex i q → Vertex i m
  | .root => .root
  | .exceptional j => .exceptional j
  | .regular t => .regular (expandRegular e he heq t)

 theorem contract_expand (v : Vertex i q) :
    contractVertex e he heq hzero (expandVertex e he heq v) = v := by
  cases v with
  | root => rfl
  | exceptional j => rfl
  | regular t =>
    simp only [expandVertex,contractVertex]
    congr 1
    apply Fin.ext
    change levelCeil e he ((expandRegular e he heq t).val+1)-1 = t.val
    rw [expandRegular_succ,levelCeil_at_level]
    omega

 theorem expandVertex_strictMono (d : Fin i → Fin (q+1)) (hd : Monotone d) :
    @StrictMono (Vertex i q) (Vertex i m)
      (codeOrder d).toPreorder
      (codeOrder (fun j => recodeLevel e he heq (d j))).toPreorder
      (expandVertex e he heq) := by
  let _ := codeOrder d
  let _ := codeOrder (fun j => recodeLevel e he heq (d j))
  have hdm : Monotone (fun j => recodeLevel e he heq (d j)) :=
    (recodeLevel_monotone e he heq).comp hd
  intro u v huv
  cases u with
  | root =>
    cases v with
    | root => exact False.elim ((lt_irrefl _) huv)
    | exceptional j => exact root_lt_exceptional _ j
    | regular t => exact root_lt_regular _ _
  | exceptional j =>
    cases v with
    | root => exact False.elim (not_lt_of_gt (root_lt_exceptional _ j) huv)
    | exceptional k =>
      exact (exceptional_lt_exceptional _ hdm j k).mpr
        ((exceptional_lt_exceptional d hd j k).mp huv)
    | regular t =>
      have hdt := (exceptional_lt_regular d j t).mp huv
      have hh := he (show (d j).val < t.val+1 by omega)
      apply (exceptional_lt_regular _ j _).mpr
      change e (d j) ≤ e (t.val+1)-1
      omega
  | regular t =>
    cases v with
    | root => exact False.elim (not_lt_of_gt (root_lt_regular _ t) huv)
    | exceptional j =>
      have htd := (regular_lt_exceptional d t j).mp huv
      have hh := he.monotone (show t.val+1 ≤ (d j).val by omega)
      have hp := strictly_increasing_unbounded e he (t.val+1)
      apply (regular_lt_exceptional _ _ j).mpr
      change e (t.val+1)-1 < e (d j)
      omega
    | regular s =>
      have hts := (regular_lt_regular d t s).mp huv
      have hh := he (show t.val+1 < s.val+1 by omega)
      have hp := strictly_increasing_unbounded e he (t.val+1)
      apply (regular_lt_regular _ _ _).mpr
      change e (t.val+1)-1 < e (s.val+1)-1
      omega

 theorem comap_twin_section {V W : Type*} (G : SimpleGraph V) (f : W → V) (g : V → W)
    (hfg : Function.LeftInverse f g) : (twinExpansion G f).comap g = G := by
  ext u v
  change (g u ≠ g v ∧ (f (g u) = f (g v) ∨ G.Adj (f (g u)) (f (g v)))) ↔ G.Adj u v
  rw [hfg u,hfg v]
  constructor
  · rintro ⟨hne,he|h⟩
    · exact False.elim (hne (congrArg g he))
    · exact h
  · intro h
    exact ⟨fun he => h.ne (hfg.injective he),Or.inr h⟩

 include hzero in
 theorem recoded_admissible_iff (d y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i))
    (hd : Monotone d) :
    @Admissible (Vertex i m) (codeOrder (fun j => recodeLevel e he heq (d j)))
      (codeGraph (fun j => recodeLevel e he heq (y j)) E) ↔
    @Admissible (Vertex i q) (codeOrder d) (codeGraph y E) := by
  let _ := codeOrder d
  let _ := codeOrder (fun j => recodeLevel e he heq (d j))
  constructor
  · intro hG
    have hh := admissible_comap _ hG _ (expandVertex_strictMono e he heq d hd)
    rw [recoded_graph_twinExpansion e he heq hzero,
      comap_twin_section _ _ _ (contract_expand e he heq hzero)] at hh
    exact hh
  · exact recoded_admissible e he heq hzero d y E hd

end
end CokernelPolynomiality
