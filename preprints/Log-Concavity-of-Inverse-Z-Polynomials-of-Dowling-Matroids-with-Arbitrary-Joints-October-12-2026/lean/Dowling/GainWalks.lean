import Dowling.MatroidRank

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

/-- A selected gain link traversed in either direction, with inverse gain on reversal. -/
def Arc (S : Set (Edge G n)) (i j : Fin n) (g : G) : Prop :=
  ∃ e : Link G n, Sum.inr e ∈ S ∧
    ((e.tail = i ∧ e.head = j ∧ e.gain = g) ∨
     (e.head = i ∧ e.tail = j ∧ e.gain⁻¹ = g))

theorem Arc.reverse {S : Set (Edge G n)} {i j : Fin n} {g : G} (h : Arc S i j g) :
    Arc S j i g⁻¹ := by
  rcases h with ⟨e,he,h | h⟩
  · rcases h with ⟨rfl,rfl,rfl⟩
    exact ⟨e,he,Or.inr ⟨rfl,rfl,rfl⟩⟩
  · rcases h with ⟨rfl,rfl,rfl⟩
    exact ⟨e,he,Or.inl ⟨rfl,rfl,by simp⟩⟩

/-- Finite gain walks retain the ordered, potentially noncommutative gain product. -/
inductive GainWalk (S : Set (Edge G n)) : Fin n → Fin n → G → Prop
  | nil (i) : GainWalk S i i 1
  | cons {i j k g h} : Arc S i j g → GainWalk S j k h → GainWalk S i k (g*h)

theorem GainWalk.single {S : Set (Edge G n)} {i j : Fin n} {g : G} (h : Arc S i j g) :
    GainWalk S i j g := by simpa using GainWalk.cons h (GainWalk.nil j)

theorem GainWalk.trans {S : Set (Edge G n)} {i j k : Fin n} {g h : G}
    (p : GainWalk S i j g) (q : GainWalk S j k h) : GainWalk S i k (g*h) := by
  induction p with
  | nil i => simpa using q
  | @cons i j l a b ha hb ih =>
    simpa only [mul_assoc] using GainWalk.cons ha (ih q)

theorem GainWalk.reverse {S : Set (Edge G n)} {i j : Fin n} {g : G}
    (p : GainWalk S i j g) : GainWalk S j i g⁻¹ := by
  induction p with
  | nil i => simpa using GainWalk.nil i
  | cons ha hb ih => simpa only [mul_inv_rev] using ih.trans (GainWalk.single ha.reverse)

theorem Arc.equation {S : Set (Edge G n)} {i j : Fin n} {g : G} (h : Arc S i j g)
    {x : Fin n → Option G} (hx : x ∈ solutions G n S) : x j = gainAct G (x i) g := by
  rcases h with ⟨e,he,h | h⟩
  · rcases h with ⟨rfl,rfl,rfl⟩
    exact hx (Sum.inr e) he
  · rcases h with ⟨rfl,rfl,rfl⟩
    exact (gainAct_reverse _ _ _).mp (hx (Sum.inr e) he)

theorem GainWalk.equation {S : Set (Edge G n)} {i j : Fin n} {g : G}
    (p : GainWalk S i j g) {x : Fin n → Option G} (hx : x ∈ solutions G n S) :
    x j = gainAct G (x i) g := by
  induction p with
  | nil i => simp
  | cons ha hb ih => rw [ih, ha.equation hx, gainAct_mul]

/-- Connectivity of the literal selected link graph; joints do not add vertices or links. -/
def Connected (S : Set (Edge G n)) (i j : Fin n) : Prop := ∃ g, GainWalk S i j g

def componentSetoid (S : Set (Edge G n)) : Setoid (Fin n) where
  r := Connected S
  iseqv := ⟨fun i => ⟨1,GainWalk.nil i⟩,
    fun ⟨g,h⟩ => ⟨g⁻¹,h.reverse⟩,
    fun ⟨g,p⟩ ⟨h,q⟩ => ⟨g*h,p.trans q⟩⟩

/-- A component has no joint and every closed ordered gain walk has identity gain. -/
def BalancedAt (S : Set (Edge G n)) (i : Fin n) : Prop :=
  (∀ j, Connected S i j → Sum.inl j ∉ S) ∧
  (∀ g, GainWalk S i i g → g = 1)

end Dowling
