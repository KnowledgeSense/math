import Dowling.GainCirclesComponents

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ} {S : Set (Edge G n)}

theorem Arc.ne {i j : Fin n} {g : G} (h : Arc S i j g) : i≠j := by
  rcases h with ⟨e,_,h | h⟩
  · rcases h with ⟨rfl,rfl,_⟩
    exact ne_of_lt e.ordered
  · rcases h with ⟨rfl,rfl,_⟩
    exact ne_of_gt e.ordered

namespace GainPath

def reverse {i j : Fin n} : GainPath S i j → GainPath S j i
  | nil i => nil i
  | @cons _ _ _ _ i _ _ g h p => p.reverse.append (cons g⁻¹ h.reverse (nil i))

theorem gain_reverse {i j : Fin n} (p : GainPath S i j) : p.reverse.gain=p.gain⁻¹ := by
  induction p with
  | nil => simp [reverse,gain]
  | cons g h p ih => simp only [reverse,gain_append,ih,gain,mul_one,mul_inv_rev]

theorem length_reverse {i j : Fin n} (p : GainPath S i j) : p.reverse.length=p.length := by
  induction p with
  | nil => rfl
  | cons g h p ih => simp only [reverse,length_append,ih,length]; omega

theorem IsCircle.length_ge_two {i : Fin n} {p : GainPath S i i} (hp : p.IsCircle) :
    2≤p.length := by
  cases p with
  | nil => simp [IsCircle,length] at hp
  | cons g h p =>
    cases p with
    | nil => exact False.elim (h.ne rfl)
    | cons g' h' p => simp only [length]; omega

/-- Traversing one selected link and immediately reversing it has neutral gain. -/
theorem immediate_reversal_gain {i j : Fin n} {g : G} (h : Arc S i j g) :
    (cons g h (cons g⁻¹ h.reverse (nil i))).gain=1 := by
  simp [gain]

/-- The harmless backtracking case is included by the vertex-simple convention. -/
theorem immediate_reversal_isCircle {i j : Fin n} {g : G} (h : Arc S i j g) :
    (cons g h (cons g⁻¹ h.reverse (nil i))).IsCircle := by
  constructor
  · simp [length]
  · simp [vertices,h.ne]

/-- Two selected parallel traversals retain their ordered gain product. -/
theorem parallel_isCircle {i j : Fin n} {g h : G} (a : Arc S i j g) (b : Arc S j i h) :
    (cons g a (cons h b (nil i))).IsCircle := by
  constructor
  · simp [length]
  · simp [vertices,a.ne]

theorem parallel_gain {i j : Fin n} {g h : G} (a : Arc S i j g) (b : Arc S j i h) :
    (cons g a (cons h b (nil i))).gain=g*h := by simp [gain]

end GainPath
end Dowling
