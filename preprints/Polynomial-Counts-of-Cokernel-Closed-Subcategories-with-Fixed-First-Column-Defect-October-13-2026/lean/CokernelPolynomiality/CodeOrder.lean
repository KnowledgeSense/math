import CokernelPolynomiality.Templates

namespace CokernelPolynomiality

 theorem root_lt_exceptional {i m : ℕ} (d : Fin i → Fin (m+1)) (j : Fin i) :
    let _ := codeOrder d
    (Vertex.root : Vertex i m) < .exceptional j := by
  let _ := codeOrder d
  change position d .root < position d (.exceptional j)
  simp only [position, Prod.Lex.toLex_lt_toLex]
  omega

 theorem root_lt_regular {i m : ℕ} (d : Fin i → Fin (m+1)) (t : Fin m) :
    let _ := codeOrder d
    (Vertex.root : Vertex i m) < .regular t := by
  let _ := codeOrder d
  change position d .root < position d (.regular t)
  simp only [position, Prod.Lex.toLex_lt_toLex]
  omega

 theorem exceptional_lt_regular {i m : ℕ} (d : Fin i → Fin (m+1)) (j : Fin i) (t : Fin m) :
    let _ := codeOrder d
    (Vertex.exceptional j : Vertex i m) < .regular t ↔ (d j).val ≤ t.val := by
  let _ := codeOrder d
  change position d (.exceptional j) < position d (.regular t) ↔ _
  simp only [position, Prod.Lex.toLex_lt_toLex]
  omega

 theorem regular_lt_exceptional {i m : ℕ} (d : Fin i → Fin (m+1)) (t : Fin m) (j : Fin i) :
    let _ := codeOrder d
    (Vertex.regular t : Vertex i m) < .exceptional j ↔ t.val < (d j).val := by
  let _ := codeOrder d
  change position d (.regular t) < position d (.exceptional j) ↔ _
  simp only [position, Prod.Lex.toLex_lt_toLex]
  omega

 theorem regular_lt_regular {i m : ℕ} (d : Fin i → Fin (m+1)) (s t : Fin m) :
    let _ := codeOrder d
    (Vertex.regular s : Vertex i m) < .regular t ↔ s < t := by
  let _ := codeOrder d
  change position d (.regular s) < position d (.regular t) ↔ _
  simp only [position, Prod.Lex.toLex_lt_toLex]
  omega

 theorem exceptional_lt_exceptional {i m : ℕ} (d : Fin i → Fin (m+1))
    (hd : Monotone d) (j k : Fin i) :
    let _ := codeOrder d
    (Vertex.exceptional j : Vertex i m) < .exceptional k ↔ j < k := by
  let _ := codeOrder d
  change position d (.exceptional j) < position d (.exceptional k) ↔ _
  simp only [position, Prod.Lex.toLex_lt_toLex]
  have hjk : j ≤ k → d j ≤ d k := fun h => hd h
  have hkj : k ≤ j → d k ≤ d j := fun h => hd h
  omega

end CokernelPolynomiality
