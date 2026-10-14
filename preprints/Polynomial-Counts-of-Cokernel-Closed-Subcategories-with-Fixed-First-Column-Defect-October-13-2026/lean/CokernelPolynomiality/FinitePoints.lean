import CokernelPolynomiality.GraphEquivalence
import CokernelPolynomiality.PointGraph

namespace CokernelPolynomiality
noncomputable section

 theorem mem_triangle {n a b : ℕ} : (a,b) ∈ triangle n ↔ a ≤ b ∧ b ≤ n := by
  simp [triangle]
  constructor <;> omega

 def boundedPointGraph (n : ℕ) (Y : Finset (ℕ × ℕ)) : SimpleGraph (Fin (n+2)) :=
  (pointGraph Y).comap Fin.val

 def graphPoints {n : ℕ} (G : SimpleGraph (Fin (n+2))) : Finset (ℕ × ℕ) := by
  classical
  exact (triangle n).filter (fun p => ∃ (ha : p.1 < n+2) (hb : p.2+1 < n+2),
    G.Adj ⟨p.1,ha⟩ ⟨p.2+1,hb⟩)

 theorem graphPoints_subset {n : ℕ} (G : SimpleGraph (Fin (n+2))) : graphPoints G ⊆ triangle n := by
  classical
  exact Finset.filter_subset _ _

 theorem mem_graphPoints {n a b : ℕ} (G : SimpleGraph (Fin (n+2)))
    (hab : a ≤ b) (hbn : b ≤ n) :
    (a,b) ∈ graphPoints G ↔ G.Adj ⟨a,by omega⟩ ⟨b+1,by omega⟩ := by
  classical
  simp only [graphPoints,Finset.mem_filter,mem_triangle]
  constructor
  · rintro ⟨_,ha,hb,h⟩
    exact h
  · intro h
    exact ⟨⟨hab,hbn⟩,by omega,by omega,h⟩

 theorem boundedPointGraph_graphPoints {n : ℕ} (G : SimpleGraph (Fin (n+2))) :
    boundedPointGraph n (graphPoints G) = G := by
  ext u v
  rcases lt_trichotomy u v with huv | rfl | hvu
  · change (pointGraph (graphPoints G)).Adj u.val v.val ↔ G.Adj u v
    rw [pointGraph_adj_iff huv]
    have hpos : 0 < v.val := by change u.val < v.val at huv; omega
    simpa only [Nat.sub_add_cancel hpos] using
      mem_graphPoints G (a:=u.val) (b:=v.val-1) (by change u.val < v.val at huv; omega)
        (by have := v.isLt; omega)
  · simp
  · rw [SimpleGraph.adj_comm,SimpleGraph.adj_comm (G:=G)]
    change (pointGraph (graphPoints G)).Adj v.val u.val ↔ G.Adj v u
    rw [pointGraph_adj_iff hvu]
    have hpos : 0 < u.val := by change v.val < u.val at hvu; omega
    simpa only [Nat.sub_add_cancel hpos] using
      mem_graphPoints G (a:=v.val) (b:=u.val-1) (by change v.val < u.val at hvu; omega)
        (by have := u.isLt; omega)

 theorem graphPoints_boundedPointGraph {n : ℕ} (Y : Finset (ℕ × ℕ)) (hY : Y ⊆ triangle n) :
    graphPoints (boundedPointGraph n Y) = Y := by
  ext p
  rcases p with ⟨a,b⟩
  by_cases hp : (a,b) ∈ triangle n
  · obtain ⟨hab,hbn⟩ := mem_triangle.mp hp
    rw [mem_graphPoints _ hab hbn]
    exact pointGraph_point hab
  · exact iff_of_false (fun h => hp (graphPoints_subset _ h)) (fun h => hp (hY h))

 theorem boundedPointGraph_admissible {n : ℕ} {Y : Finset (ℕ × ℕ)} (hY : IsClosed Y) :
    Admissible (boundedPointGraph n Y) :=
  admissible_comap _ ⟨closed_pointGraph_ruleP hY,closed_pointGraph_ruleQ hY⟩ _
    (fun _ _ h => h)

 theorem graphPoints_closed {n : ℕ} (G : SimpleGraph (Fin (n+2))) (hG : Admissible G) :
    IsClosed (graphPoints G) := by
  intro a b c d e f hab hcd hef hac hcb hbd hae heb hbf
  obtain ⟨habord,hbn⟩ := mem_triangle.mp (graphPoints_subset G hab)
  obtain ⟨hcdord,hdn⟩ := mem_triangle.mp (graphPoints_subset G hcd)
  obtain ⟨heford,hfn⟩ := mem_triangle.mp (graphPoints_subset G hef)
  have hab' := (mem_graphPoints G habord hbn).mp hab
  have hcd' := (mem_graphPoints G hcdord hdn).mp hcd
  have hef' := (mem_graphPoints G heford hfn).mp hef
  let aa : Fin (n+2) := ⟨a,by omega⟩
  let bb : Fin (n+2) := ⟨b+1,by omega⟩
  let cc : Fin (n+2) := ⟨c,by omega⟩
  let dd : Fin (n+2) := ⟨d+1,by omega⟩
  let ee : Fin (n+2) := ⟨e,by omega⟩
  let ff : Fin (n+2) := ⟨f+1,by omega⟩
  constructor
  · apply (mem_graphPoints G (by omega : max c e ≤ max d f) (by omega)).mpr
    have h := hG.2 aa bb cc dd ee ff hab' hcd' hef'
      hac (by change c < b+1; omega) (by change b+1 ≤ d+1; omega)
      hae (by change e < b+1; omega) (by change b+1 ≤ f+1; omega)
    have hx : max cc ee = (⟨max c e,by omega⟩ : Fin (n+2)) := by rfl
    have hy : max dd ff = (⟨max d f+1,by omega⟩ : Fin (n+2)) := by
      apply Fin.ext
      change max (d+1) (f+1) = max d f+1
      omega
    rw [hx,hy] at h
    exact h
  · intro hmin
    rcases le_total d f with hdf | hfd
    · rw [min_eq_left hdf]
      apply (mem_graphPoints G (by omega : b+1 ≤ d) hdn).mpr
      exact hG.1 aa bb cc dd hab' hcd' hac
        (by change c < b+1; omega) (by change b+1 < d+1; omega)
    · rw [min_eq_right hfd]
      apply (mem_graphPoints G (by omega : b+1 ≤ f) hfn).mpr
      exact hG.1 aa bb ee ff hab' hef' hae
        (by change e < b+1; omega) (by change b+1 < f+1; omega)

end
end CokernelPolynomiality
