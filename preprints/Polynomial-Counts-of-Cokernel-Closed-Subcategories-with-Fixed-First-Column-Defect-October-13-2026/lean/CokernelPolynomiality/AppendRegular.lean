import CokernelPolynomiality.CodeOrder
import CokernelPolynomiality.GreatestVertex

namespace CokernelPolynomiality
noncomputable section

variable {i q : ℕ}

def appendVertex : Vertex i q → Vertex i (q+1)
  | .root => .root
  | .exceptional j => .exceptional j
  | .regular t => .regular t.castSucc

 theorem appendVertex_ne_last (v : Vertex i q) :
    appendVertex v ≠ .regular (Fin.last q) := by
  cases v <;> simp [appendVertex]

def removeLast : {v : Vertex i (q+1) // v ≠ .regular (Fin.last q)} → Vertex i q
  | ⟨.root,_⟩ => .root
  | ⟨.exceptional j,_⟩ => .exceptional j
  | ⟨.regular t,ht⟩ => .regular ⟨t.val,by
      have hn : t ≠ Fin.last q := fun h => ht (congrArg Vertex.regular h)
      have hv : t.val ≠ q := fun h => hn (Fin.ext h)
      have := t.isLt
      omega⟩

 theorem removeLast_appendVertex (v : Vertex i q) :
    removeLast ⟨appendVertex v,appendVertex_ne_last v⟩ = v := by
  cases v <;> rfl

 theorem appendVertex_removeLast (v : {v : Vertex i (q+1) // v ≠ .regular (Fin.last q)}) :
    appendVertex (removeLast v) = v.val := by
  rcases v with ⟨v,hv⟩
  cases v with
  | root => rfl
  | exceptional j => rfl
  | regular t =>
    change Vertex.regular _ = Vertex.regular t
    congr 1

 def appendOrderIso (d : Fin i → Fin (q+1)) :
    let _ := codeOrder d
    let _ := codeOrder (fun j => (d j).castSucc)
    Vertex i q ≃o {v : Vertex i (q+1) // v ≠ .regular (Fin.last q)} := by
  let _ := codeOrder d
  let _ := codeOrder (fun j => (d j).castSucc)
  exact {
    toFun := fun v => ⟨appendVertex v,appendVertex_ne_last v⟩
    invFun := removeLast
    left_inv := removeLast_appendVertex
    right_inv := fun v => Subtype.ext (appendVertex_removeLast v)
    map_rel_iff' := by
      intro u v
      change position (fun j => (d j).castSucc) (appendVertex u) ≤
          position (fun j => (d j).castSucc) (appendVertex v) ↔ position d u ≤ position d v
      cases u <;> cases v <;> rfl }

 theorem last_regular_greatest (d : Fin i → Fin (q+1)) :
    let _ := codeOrder (fun j => (d j).castSucc)
    ∀ v : Vertex i (q+1), v ≤ .regular (Fin.last q) := by
  let _ := codeOrder (fun j => (d j).castSucc)
  change ∀ v : Vertex i (q+1), v ≤ .regular (Fin.last q)
  intro v
  cases v with
  | root => exact le_of_lt (root_lt_regular _ _)
  | exceptional j =>
    apply le_of_lt
    apply (exceptional_lt_regular _ j _).mpr
    change (d j).val ≤ q
    omega
  | regular t =>
    by_cases ht : t = Fin.last q
    · subst t; exact le_rfl
    · apply le_of_lt
      apply (regular_lt_regular _ _ _).mpr
      exact lt_of_le_of_ne (Fin.le_last t) ht

 theorem last_regular_universal (y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i))
    (v : Vertex i (q+1)) (hv : v ≠ .regular (Fin.last q)) :
    (codeGraph (fun j => (y j).castSucc) E).Adj v (.regular (Fin.last q)) := by
  cases v with
  | root => trivial
  | exceptional j => exact (y j).isLt
  | regular t => exact fun ht => hv (congrArg Vertex.regular ht)

 theorem append_comap (y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i)) :
    (codeGraph (fun j => (y j).castSucc) E).comap appendVertex = codeGraph y E := by
  ext u v
  cases u <;> cases v <;> simp [SimpleGraph.comap,codeGraph,codeAdj,appendVertex] <;> rfl

 theorem admissible_append_regular_iff (d y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i)) :
    @Admissible (Vertex i (q+1)) (codeOrder (fun j => (d j).castSucc))
      (codeGraph (fun j => (y j).castSucc) E) ↔
    @Admissible (Vertex i q) (codeOrder d) (codeGraph y E) := by
  let _ := codeOrder d
  let _ := codeOrder (fun j => (d j).castSucc)
  let G := codeGraph (fun j => (y j).castSucc) E
  let a : Vertex i (q+1) := .regular (Fin.last q)
  let f : Vertex i q ≃o {v : Vertex i (q+1) // v ≠ a} := appendOrderIso d
  have hcomp : (G.comap (Subtype.val : {v : Vertex i (q+1) // v ≠ a} → _)).comap f =
      codeGraph y E := by
    exact append_comap y E
  constructor
  · intro hG
    have hs := admissible_comap _ hG _
      ((show StrictMono (Subtype.val : {v : Vertex i (q+1) // v ≠ a} → _) from fun _ _ h => h).comp f.strictMono)
    exact hcomp ▸ hs
  · intro hG
    apply admissible_of_delete_greatest G a (last_regular_greatest d) (last_regular_universal y E)
    have hh := admissible_comap _ hG _ f.symm.strictMono
    have hback : (codeGraph y E).comap f.symm =
        G.comap (Subtype.val : {v : Vertex i (q+1) // v ≠ a} → _) := by
      rw [← hcomp]
      ext u v
      change G.Adj (f (f.symm u)).val (f (f.symm v)).val ↔ G.Adj u.val v.val
      simp
    rw [hback] at hh
    exact hh

end
end CokernelPolynomiality
