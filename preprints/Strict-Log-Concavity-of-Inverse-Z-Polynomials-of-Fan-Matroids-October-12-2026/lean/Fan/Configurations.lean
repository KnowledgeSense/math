import Fan.FlatClassification

namespace Fan

/-- Selected spokes and selected path joins, each join indexed by its right endpoint. -/
abbrev Pair (n : ℕ) := Finset (Fin n) × Finset (Fin n)

def selectedGraph {n : ℕ} (p : Pair n) : SimpleGraph (Vertex n) where
  Adj v w := match v,w with
    | none,some i => i ∈ p.1
    | some i,none => i ∈ p.1
    | some i,some j => (i.val+1=j.val ∧ j∈p.2) ∨ (j.val+1=i.val ∧ i∈p.2)
    | none,none => False
  symm := ⟨by intro v w; cases v <;> cases w <;> simp [or_comm]⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

def Valid {n : ℕ} (p : Pair n) : Prop :=
  (∀ j∈p.2, 0<j.val) ∧ ∀ i j : Fin n, i.val+1=j.val →
    (j∈p.2 → (i∈p.1 ↔ j∈p.1)) ∧ (i∈p.1 → j∈p.1 → j∈p.2)

abbrev Configuration (n : ℕ) := {p : Pair n // Valid p}

@[simp] theorem spoke_selected {n : ℕ} (p : Pair n) (i : Fin n) :
    spoke i ∈ (selectedGraph p).edgeSet ↔ i∈p.1 := Iff.rfl

theorem rim_selected {n : ℕ} (p : Pair n) (i j : Fin n) (hij : i.val+1=j.val) :
    rim i j ∈ (selectedGraph p).edgeSet ↔ j∈p.2 := by
  change (i.val+1=j.val ∧ j∈p.2) ∨ (j.val+1=i.val ∧ i∈p.2) ↔ j∈p.2
  have hne : ¬j.val+1=i.val := by omega
  simp only [hij,hne,true_and,false_and,or_false]

theorem selectedGraph_le {n : ℕ} (p : Pair n) : selectedGraph p ≤ graph n := by
  intro v w h
  cases v <;> cases w
  · exact h
  · trivial
  · trivial
  · exact h.imp And.left And.left

theorem Valid.isGraphicFlat {n : ℕ} {p : Pair n} (hp : Valid p) :
    IsGraphicFlat (graph n) (selectedGraph p).edgeSet := by
  apply isGraphicFlat_iff_triangleClosed.mpr
  refine ⟨SimpleGraph.edgeSet_mono (selectedGraph_le p),?_⟩
  intro i j hij
  simpa only [rim_selected p i j hij,spoke_selected] using hp.2 i j hij

noncomputable def readPair {n : ℕ} (F : Set (Sym2 (Vertex n))) : Pair n := by
  classical
  exact (Finset.univ.filter fun i => spoke i∈F,
    Finset.univ.filter fun j => ∃ i : Fin n, i.val+1=j.val ∧ rim i j∈F)

@[simp] theorem mem_read_spokes {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    i∈(readPair F).1 ↔ spoke i∈F := by classical simp [readPair]

theorem mem_read_joins {n : ℕ} (F : Set (Sym2 (Vertex n))) (i j : Fin n)
    (hij : i.val+1=j.val) : j∈(readPair F).2 ↔ rim i j∈F := by
  classical
  simp only [readPair,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨k,hk,hr⟩
    have he : k=i := Fin.ext (by omega)
    simpa only [he] using hr
  · intro hr
    exact ⟨i,hij,hr⟩

theorem IsGraphicFlat.readPair_valid {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) : Valid (readPair F) := by
  classical
  constructor
  · intro j hj
    simp only [readPair,Finset.mem_filter,Finset.mem_univ,true_and] at hj
    obtain ⟨i,hi,_⟩ := hj
    omega
  · intro i j hij
    simpa only [mem_read_spokes,mem_read_joins F i j hij] using hF.triangleClosed i j hij

theorem edgeSets_ext {n : ℕ} {F H : Set (Sym2 (Vertex n))}
    (hF : F ⊆ (graph n).edgeSet) (hH : H ⊆ (graph n).edgeSet)
    (hs : ∀ i, spoke i∈F ↔ spoke i∈H)
    (hr : ∀ i j : Fin n, i.val+1=j.val → (rim i j∈F ↔ rim i j∈H)) : F=H := by
  ext e
  induction e using Sym2.inductionOn with
  | hf v w =>
    by_cases ha : (graph n).Adj v w
    · cases v with
      | none =>
        cases w with
        | none => exact False.elim ha
        | some j => exact hs j
      | some i =>
        cases w with
        | none => simpa only [spoke,Sym2.eq_swap] using hs i
        | some j =>
          obtain hij | hji := ha
          · exact hr i j hij
          · simpa only [rim,Sym2.eq_swap] using hr j i hji
    · exact iff_of_false (fun he => ha (hF he)) (fun he => ha (hH he))

theorem readPair_selected_eq {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : F ⊆ (graph n).edgeSet) : (selectedGraph (readPair F)).edgeSet=F := by
  apply edgeSets_ext (SimpleGraph.edgeSet_mono (selectedGraph_le _)) hF
  · intro i
    simp only [spoke_selected,mem_read_spokes]
  · intro i j hij
    rw [rim_selected _ i j hij,mem_read_joins F i j hij]

theorem Valid.readPair_selected {n : ℕ} {p : Pair n} (hp : Valid p) :
    readPair (selectedGraph p).edgeSet=p := by
  classical
  apply Prod.ext
  · ext i
    simp only [mem_read_spokes,spoke_selected]
  · ext j
    by_cases hj : 0<j.val
    · let i : Fin n := ⟨j.val-1,by omega⟩
      have hij : i.val+1=j.val := by dsimp [i]; omega
      rw [mem_read_joins _ i j hij,rim_selected _ i j hij]
    · have hjp : j∉p.2 := fun h => hj (hp.1 j h)
      have hjr : j∉(readPair (selectedGraph p).edgeSet).2 := by
        simp only [readPair,Finset.mem_filter,Finset.mem_univ,true_and,not_exists,not_and]
        intro i hi
        omega
      exact iff_of_false hjr hjp

/-- Exact finite encoding of the genuine connectivity-flat lattice. -/
noncomputable def configurationEquiv (n : ℕ) : GraphicFlat n ≃ Configuration n where
  toFun F := ⟨readPair F.val,F.property.readPair_valid⟩
  invFun p := ⟨(selectedGraph p.val).edgeSet,p.property.isGraphicFlat⟩
  left_inv F := Subtype.ext (readPair_selected_eq F.property.1)
  right_inv p := Subtype.ext p.property.readPair_selected


theorem readPair_mono {n : ℕ} {F H : Set (Sym2 (Vertex n))} (h : F ⊆ H) :
    readPair F ≤ readPair H := by
  classical
  constructor
  · intro i hi
    exact (mem_read_spokes H i).mpr (h ((mem_read_spokes F i).mp hi))
  · intro j hj
    simp only [readPair,Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
    obtain ⟨i,hij,hi⟩ := hj
    exact ⟨i,hij,h hi⟩

theorem selectedGraph_mono {n : ℕ} {p q : Pair n} (h : p ≤ q) :
    selectedGraph p ≤ selectedGraph q := by
  intro v w ha
  cases v <;> cases w
  · exact ha
  · exact h.1 ha
  · exact h.1 ha
  · exact ha.imp (fun ⟨he,hm⟩ => ⟨he,h.2 hm⟩) (fun ⟨he,hm⟩ => ⟨he,h.2 hm⟩)

noncomputable def configurationOrderIso (n : ℕ) : GraphicFlat n ≃o Configuration n where
  toEquiv := configurationEquiv n
  map_rel_iff' := by
    intro F H
    change readPair F.val ≤ readPair H.val ↔ F.val ⊆ H.val
    constructor
    · intro h
      have hs := SimpleGraph.edgeSet_mono (selectedGraph_mono h)
      simpa only [readPair_selected_eq F.property.1,readPair_selected_eq H.property.1] using hs
    · exact readPair_mono

end Fan
