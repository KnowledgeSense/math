import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
F_11 with offset 2 is a counterexample to Sun's circular-permutation conjecture.
The obstruction comes from the two vertices 2 and 9, whose distinct nonzero
neighbours are exactly 3 and 8.
-/

namespace SunCounterexample

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

abbrev F11 := ZMod 11
abbrev Nonzero := {x : F11 // x ≠ 0}

def next (i : Fin 10) : Fin 10 := i + 1
def prev (i : Fin 10) : Fin 10 := i - 1

lemma primitive_iff_finite (z : F11) :
    IsPrimitiveRoot z 10 ↔
      z ^ 10 = 1 ∧ ∀ k : Fin 10, k.val ≠ 0 → z ^ k.val ≠ 1 := by
  constructor
  · intro h
    exact ⟨h.pow_eq_one, fun k hk => h.pow_ne_one_of_pos_of_lt hk k.isLt⟩
  · rintro ⟨hpow, h⟩
    exact IsPrimitiveRoot.mk_of_lt z (by decide) hpow
      (fun k hk hlt => h ⟨k, hlt⟩ (Nat.ne_of_gt hk))

lemma primitive_elements (z : F11) :
    IsPrimitiveRoot z 10 ↔ z = 2 ∨ z = 6 ∨ z = 7 ∨ z = 8 := by
  rw [primitive_iff_finite]
  have h : ∀ z : F11,
      (z ^ 10 = 1 ∧ ∀ k : Fin 10, k.val ≠ 0 → z ^ k.val ≠ 1) ↔
        z = 2 ∨ z = 6 ∨ z = 7 ∨ z = 8 := by decide
  exact h z

lemma neighbours (x y : F11) (hx : x = 2 ∨ x = 9)
    (hy : y ≠ 0) (hxy : y ≠ x) (h : IsPrimitiveRoot (2 + x * y) 10) :
    y = 3 ∨ y = 8 := by
  have hs := (primitive_elements (2 + x * y)).mp h
  have hc : ∀ x y : F11, (x = 2 ∨ x = 9) → y ≠ 0 → y ≠ x →
      (2 + x * y = 2 ∨ 2 + x * y = 6 ∨
        2 + x * y = 7 ∨ 2 + x * y = 8) → (y = 3 ∨ y = 8) := by decide
  exact hc x y hx hy hxy hs

lemma cycle_facts : ∀ i : Fin 10,
    next (prev i) = i ∧ prev (next i) = i ∧
      prev i ≠ next i ∧ prev i ≠ i ∧ next i ≠ i := by decide

lemma different_neighbour_pairs : ∀ i j : Fin 10, i ≠ j →
    ¬ ((prev i = prev j ∨ prev i = next j) ∧
      (next i = prev j ∨ next i = next j)) := by decide

lemma pair_exhausts {α : Type*} {a b c d : α}
    (hc : c = a ∨ c = b) (hd : d = a ∨ d = b) (hcd : c ≠ d)
    {x : α} (hx : x = a ∨ x = b) : x = c ∨ x = d := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact (hcd rfl).elim
  · exact hx
  · exact hx.elim Or.inr Or.inl
  · exact (hcd rfl).elim

/-- There is no circular ordering of all ten nonzero elements of F_11 whose
adjacent products, after adding 2, are primitive elements. Addition of 1 in
`Fin 10` includes the closing edge from position 9 to position 0. -/
theorem no_circular_permutation :
    ¬ ∃ f : Fin 10 ≃ Nonzero,
      ∀ i : Fin 10, IsPrimitiveRoot (2 + (f i).val * (f (i + 1)).val) 10 := by
  rintro ⟨f, hadj⟩
  change ∀ k : Fin 10, IsPrimitiveRoot (2 + (f k).val * (f (next k)).val) 10 at hadj
  let v : Fin 10 → F11 := fun i => (f i).val
  have hinj : Function.Injective v := fun i j h => f.injective (Subtype.ext h)
  let i : Fin 10 := f.symm ⟨2, by decide⟩
  let j : Fin 10 := f.symm ⟨9, by decide⟩
  have hi : v i = 2 := congrArg Subtype.val (f.apply_symm_apply _)
  have hj : v j = 9 := congrArg Subtype.val (f.apply_symm_apply _)
  have hij : i ≠ j := by
    intro h
    have : (2 : F11) = 9 := hi.symm.trans ((congrArg v h).trans hj)
    exact (by decide : (2 : F11) ≠ 9) this
  have hn (k : Fin 10) (hk : v k = 2 ∨ v k = 9) :
      (v (prev k) = 3 ∨ v (prev k) = 8) ∧
        (v (next k) = 3 ∨ v (next k) = 8) := by
    constructor
    · apply neighbours (v k) (v (prev k)) hk (f (prev k)).property
        (fun h => (cycle_facts k).2.2.2.1 (hinj h))
      have h := hadj (prev k)
      rw [(cycle_facts k).1] at h
      simpa only [v, mul_comm] using h
    · exact neighbours (v k) (v (next k)) hk (f (next k)).property
        (fun h => (cycle_facts k).2.2.2.2 (hinj h)) (hadj k)
  have hni := hn i (Or.inl hi)
  have hnj := hn j (Or.inr hj)
  have hjdistinct : v (prev j) ≠ v (next j) :=
    fun h => (cycle_facts j).2.2.1 (hinj h)
  have hleft := pair_exhausts hnj.1 hnj.2 hjdistinct hni.1
  have hright := pair_exhausts hnj.1 hnj.2 hjdistinct hni.2
  exact different_neighbour_pairs i j hij
    ⟨hleft.imp (fun h => hinj h) (fun h => hinj h),
      hright.imp (fun h => hinj h) (fun h => hinj h)⟩

end SunCounterexample

