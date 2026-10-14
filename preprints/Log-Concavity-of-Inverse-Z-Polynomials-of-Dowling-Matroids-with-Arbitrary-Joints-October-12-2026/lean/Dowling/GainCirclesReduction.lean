import Dowling.GainCirclesPaths

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ} {S : Set (Edge G n)}
namespace GainPath

/-- A repeated source vertex gives a genuine positive-length closed subwalk and
leaves a nonempty suffix. Ordered products are preserved without commuting factors. -/
theorem repeated_vertex_decomposition {i j : Fin n} (p : GainPath S i j)
    (hp : ¬p.vertices.Nodup) :
    ∃ v:Fin n, ∃ a:GainPath S i v, ∃ b:GainPath S v v, ∃ c:GainPath S v j,
      p.gain=a.gain*b.gain*c.gain ∧
      p.length=a.length+b.length+c.length ∧ 0<b.length ∧ 0<c.length := by
  induction p with
  | nil i => simp [vertices] at hp
  | @cons i k j g h p ih =>
    by_cases hi : i∈p.vertices
    · obtain ⟨a,c,hgain,hlen,hc⟩ := p.split_at_vertex hi
      refine ⟨i,nil i,cons g h a,c,?_,?_,?_,hc⟩
      · simp only [gain,hgain,one_mul,mul_assoc]
      · simp only [length,hlen,zero_add,Nat.add_assoc]
      · simp [length]
    · have ht : ¬p.vertices.Nodup := by
        intro ht
        apply hp
        exact List.nodup_cons.mpr ⟨hi,ht⟩
      obtain ⟨v,a,b,c,hgain,hlen,hb,hc⟩ := ih ht
      refine ⟨v,cons g h a,b,c,?_,?_,hb,hc⟩
      · simp only [gain,hgain,mul_assoc]
      · simp only [length,hlen,Nat.add_assoc]

/-- A nonempty closed traversal with no repeated source vertex. This includes
length-two immediate reversals, whose ordered gain is automatically the identity. -/
def IsCircle {i : Fin n} (p : GainPath S i i) : Prop :=
  0<p.length ∧ p.vertices.Nodup

/-- Neutrality of vertex-simple closed traversals implies neutrality of every
closed walk, by deleting genuine closed subwalks. -/
theorem gain_eq_one_of_circles
    (hcircle : ∀ (i:Fin n) (p:GainPath S i i),p.IsCircle → p.gain=1)
    {i : Fin n} (p : GainPath S i i) : p.gain=1 := by
  have hmain (L:ℕ) : ∀ (i:Fin n) (p:GainPath S i i),p.length=L → p.gain=1 := by
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro i p hpL
      by_cases hzero : p.length=0
      · exact p.gain_eq_one_of_length_zero hzero
      by_cases hnodup : p.vertices.Nodup
      · exact hcircle i p ⟨Nat.pos_of_ne_zero hzero,hnodup⟩
      obtain ⟨v,a,b,c,hgain,hlen,hb,hc⟩ := p.repeated_vertex_decomposition hnodup
      have hblt : b.length<L := by omega
      have hclt : (a.append c).length<L := by rw [length_append]; omega
      have hbgain := ih b.length hblt v b rfl
      have hcgain := ih (a.append c).length hclt i (a.append c) rfl
      rw [gain_append] at hcgain
      rw [hgain,hbgain,mul_one,hcgain]
  exact hmain p.length i p rfl

end GainPath

theorem closed_gainWalks_iff_circles :
    (∀ (i:Fin n) (g:G),GainWalk S i i g → g=1) ↔
      (∀ (i:Fin n) (p:GainPath S i i),p.IsCircle → p.gain=1) := by
  constructor
  · intro h i p _
    exact h i p.gain p.to_walk
  · intro h i g hg
    obtain ⟨p,hp⟩ := hg.exists_gainPath
    rw [← hp]
    exact p.gain_eq_one_of_circles h

end Dowling
