import Dowling.GainWalks
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- A finite selected-link traversal, retaining its vertices and ordered gains. -/
inductive GainPath (S : Set (Edge G n)) : Fin n → Fin n → Type _
  | nil (i) : GainPath S i i
  | cons {i j k} (g : G) : Arc S i j g → GainPath S j k → GainPath S i k

namespace GainPath
variable {S : Set (Edge G n)}

def gain {i j : Fin n} : GainPath S i j → G
  | nil _ => 1
  | cons g _ p => g*p.gain

def length {i j : Fin n} : GainPath S i j → ℕ
  | nil _ => 0
  | cons _ _ p => 1+p.length

/-- The source vertices of the successive links; the final endpoint is omitted. -/
def vertices {i j : Fin n} : GainPath S i j → List (Fin n)
  | nil _ => []
  | @cons _ _ _ _ i _ _ _ _ p => i::p.vertices

theorem vertices_length {i j : Fin n} (p : GainPath S i j) : p.vertices.length=p.length := by
  induction p with
  | nil => rfl
  | cons g h p ih => simp only [vertices,List.length_cons,length,ih]; omega

def append {i j k : Fin n} : GainPath S i j → GainPath S j k → GainPath S i k
  | nil _,q => q
  | cons g h p,q => cons g h (p.append q)

theorem gain_append {i j k : Fin n} (p : GainPath S i j) (q : GainPath S j k) :
    (p.append q).gain=p.gain*q.gain := by
  induction p with
  | nil => simp [append,gain]
  | cons g h p ih => simp only [append,gain,ih,mul_assoc]

theorem length_append {i j k : Fin n} (p : GainPath S i j) (q : GainPath S j k) :
    (p.append q).length=p.length+q.length := by
  induction p with
  | nil => simp [append,length]
  | cons g h p ih => simp only [append,length,ih,Nat.add_assoc]

theorem vertices_append {i j k : Fin n} (p : GainPath S i j) (q : GainPath S j k) :
    (p.append q).vertices=p.vertices++q.vertices := by
  induction p with
  | nil => rfl
  | cons g h p ih => simp only [append,vertices,ih,List.cons_append]

theorem to_walk {i j : Fin n} (p : GainPath S i j) : GainWalk S i j p.gain := by
  induction p with
  | nil i => exact GainWalk.nil i
  | cons g h p ih => exact GainWalk.cons h ih

theorem gain_eq_one_of_length_zero {i j : Fin n} (p : GainPath S i j) (hp : p.length=0) :
    p.gain=1 := by
  cases p with
  | nil => rfl
  | cons g h p => simp [length] at hp

/-- Splitting at an actual occurrence of a source vertex leaves a nonempty suffix. -/
theorem split_at_vertex {i j v : Fin n} (p : GainPath S i j) (hv : v∈p.vertices) :
    ∃ a:GainPath S i v, ∃ b:GainPath S v j,
      p.gain=a.gain*b.gain ∧ p.length=a.length+b.length ∧ 0<b.length := by
  induction p with
  | nil i => simp [vertices] at hv
  | @cons i k j g h p ih =>
    simp only [vertices,List.mem_cons] at hv
    rcases hv with hv | hv
    · subst v
      exact ⟨nil i,cons g h p,by simp [gain],by simp [length],by simp [length]⟩
    · obtain ⟨a,b,hgain,hlen,hpos⟩ := ih hv
      refine ⟨cons g h a,b,?_,?_,hpos⟩
      · simp only [gain,hgain,mul_assoc]
      · simp only [length,hlen,Nat.add_assoc]

end GainPath

theorem GainWalk.exists_gainPath {S : Set (Edge G n)} {i j : Fin n} {g : G}
    (h : GainWalk S i j g) : ∃ p:GainPath S i j,p.gain=g := by
  induction h with
  | nil i => exact ⟨GainPath.nil i,rfl⟩
  | cons ha hb ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨GainPath.cons _ ha p,by simp only [GainPath.gain,hp]⟩

end Dowling
