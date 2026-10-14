import CokernelPolynomiality.CodeOrder

namespace CokernelPolynomiality

 theorem forced_exceptional_edge {i m : ℕ} (c : Code i m) (hc : c.IsAdmissible)
    (hd : StrictMono c.d) (hne : ∀ j k, c.y j ≠ c.d k)
    (j k : Fin i) (hjk : j < k) :
    c.epsilon.Adj j k ↔ c.y j < c.d k ∧ c.y k < c.d j := by
  let _ := codeOrder c.d
  let G := codeGraph c.y c.epsilon
  have hG : Admissible G := hc
  have hdk : c.d j < c.d k := hd hjk
  have hdjbound : (c.d j).val < m := by have := (c.d k).isLt; omega
  let r : Fin m := ⟨(c.d j).val, hdjbound⟩
  have hr : G.Adj .root (.regular r) := trivial
  have hrootj := root_lt_exceptional c.d j
  have hrootr := root_lt_regular c.d r
  have hjr : (Vertex.exceptional j : Vertex i m) < .regular r :=
    (exceptional_lt_regular c.d j r).mpr le_rfl
  have hrk : (Vertex.regular r : Vertex i m) < .exceptional k :=
    (regular_lt_exceptional c.d r k).mpr hdk
  have hjk' : (Vertex.exceptional j : Vertex i m) < .exceptional k :=
    (exceptional_lt_exceptional c.d c.monotone_d j k).mpr hjk
  constructor
  · intro hedge
    have hedge' : G.Adj (.exceptional j) (.exceptional k) := hedge
    have hkr := hG.1 .root (.regular r) (.exceptional j) (.exceptional k)
      hr hedge' (le_of_lt hrootj) hjr hrk
    have hky_le : (c.y k).val ≤ (c.d j).val := by
      change (c.y k).val < r.val+1 at hkr
      dsimp [r] at hkr
      omega
    have hky : c.y k < c.d j := lt_of_le_of_ne hky_le (hne k j)
    refine ⟨?_,hky⟩
    by_cases hdkbound : (c.d k).val < m
    · let z : Fin m := ⟨(c.d k).val,hdkbound⟩
      have hz : G.Adj .root (.regular z) := trivial
      have hkz : (Vertex.exceptional k : Vertex i m) < .regular z :=
        (exceptional_lt_regular c.d k z).mpr le_rfl
      have hrz : (Vertex.regular r : Vertex i m) < .regular z :=
        (regular_lt_regular c.d r z).mpr hdk
      have hh := hG.2 .root (.regular r) (.exceptional j) (.exceptional k)
        .root (.regular z) hr hedge' hz (le_of_lt hrootj) hjr (le_of_lt hrk)
        le_rfl hrootr (le_of_lt hrz)
      rw [max_eq_left (le_of_lt hrootj), max_eq_right (le_of_lt hkz)] at hh
      change (c.y j).val < z.val+1 at hh
      have hle : c.y j ≤ c.d k := by dsimp [z] at hh; omega
      exact lt_of_le_of_ne hle (hne j k)
    · have hle : c.y j ≤ c.d k := by
        have := (c.y j).isLt
        have := (c.d k).isLt
        omega
      exact lt_of_le_of_ne hle (hne j k)
  · rintro ⟨hyj,hyk⟩
    have hdjpos : 0 < (c.d j).val := by omega
    have hdkpos : 0 < (c.d k).val := by omega
    let t : Fin m := ⟨(c.d j).val-1,by omega⟩
    let u : Fin m := ⟨(c.d k).val-1,by have := (c.d k).isLt; omega⟩
    have htu : (Vertex.regular t : Vertex i m) < .regular u :=
      (regular_lt_regular c.d t u).mpr (by change (c.d j).val-1 < (c.d k).val-1; omega)
    have htj : (Vertex.regular t : Vertex i m) < .exceptional j :=
      (regular_lt_exceptional c.d t j).mpr (by dsimp [t]; omega)
    have hju : (Vertex.exceptional j : Vertex i m) < .regular u :=
      (exceptional_lt_regular c.d j u).mpr (by dsimp [u]; omega)
    have huk : (Vertex.regular u : Vertex i m) < .exceptional k :=
      (regular_lt_exceptional c.d u k).mpr (by dsimp [u]; omega)
    have hrootu := root_lt_regular c.d u
    have hroott := root_lt_regular c.d t
    have hu : G.Adj .root (.regular u) := trivial
    have hjuedge : G.Adj (.exceptional j) (.regular u) := by
      change (c.y j).val < u.val+1
      dsimp [u]
      omega
    have htkedge : G.Adj (.regular t) (.exceptional k) := by
      change (c.y k).val < t.val+1
      dsimp [t]
      omega
    have hh := hG.2 .root (.regular u) (.exceptional j) (.regular u)
      (.regular t) (.exceptional k) hu hjuedge htkedge
      (le_of_lt hrootj) hju le_rfl (le_of_lt hroott) htu (le_of_lt huk)
    rw [max_eq_left (le_of_lt htj), max_eq_right (le_of_lt huk)] at hh
    exact hh

 theorem normalized_top_forced_edge {i : ℕ} (c : Code i (2*i))
    (hc : c.IsAdmissible) (hn : c.IsNormalized) (j k : Fin i) (hjk : j < k) :
    c.epsilon.Adj j k ↔ c.y j < c.d k ∧ c.y k < c.d j := by
  have hi := (top_coordinates_bijective c hn).1
  have hd : StrictMono c.d := by
    intro j k hjk
    apply lt_of_le_of_ne (c.monotone_d (le_of_lt hjk))
    intro he
    have hh := hi (show c.coordinate (Sum.inl j) = c.coordinate (Sum.inl k) from he)
    exact (ne_of_lt hjk) (Sum.inl.inj hh)
  have hne : ∀ j k, c.y j ≠ c.d k := by
    intro j k he
    have hh := hi (show c.coordinate (Sum.inr j) = c.coordinate (Sum.inl k) from he)
    cases hh
  exact forced_exceptional_edge c hc hd hne j k hjk

end CokernelPolynomiality
