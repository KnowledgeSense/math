import HankelAutomaticity.Definitions

namespace HankelAutomaticity

 def binaryValue : List Bool → ℕ
  | [] => 0
  | b::w => (if b then 2^w.length else 0)+binaryValue w

 def complement (w : List Bool) : List Bool := w.map Bool.not

@[simp] theorem complement_length (w : List Bool) : (complement w).length=w.length := by
  simp [complement]

@[simp] theorem complement_complement (w : List Bool) : complement (complement w)=w := by
  simp only [complement, List.map_map]
  rw [show Bool.not ∘ Bool.not=id by funext b; cases b <;> rfl, List.map_id]

@[simp] theorem complement_cons (b : Bool) (w : List Bool) :
    complement (b::w)=(!b)::complement w := rfl

 theorem binaryValue_lt (w : List Bool) : binaryValue w<2^w.length := by
  induction w with
  | nil => simp [binaryValue]
  | cons b w ih =>
    cases b <;> simp only [binaryValue, Bool.false_eq_true, ↓reduceIte, zero_add,
      List.length_cons, pow_succ]
    all_goals omega

 theorem binaryValue_complement (w : List Bool) :
    binaryValue w+binaryValue (complement w)+1=2^w.length := by
  induction w with
  | nil => simp [binaryValue, complement]
  | cons b w ih =>
    cases b <;> simp only [binaryValue, complement_cons, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, zero_add, complement_length, List.length_cons, pow_succ]
    all_goals omega

 theorem binaryValue_complement_eq (w : List Bool) :
    binaryValue (complement w)=2^w.length-1-binaryValue w := by
  have h := binaryValue_complement w
  omega

 def twist (o : Bool) (w : List Bool) : List Bool := if o then complement w else w

@[simp] theorem twist_false (w : List Bool) : twist false w=w := rfl
@[simp] theorem twist_true (w : List Bool) : twist true w=complement w := rfl
@[simp] theorem twist_length (o : Bool) (w : List Bool) : (twist o w).length=w.length := by
  cases o <;> simp [twist]

@[simp] theorem twist_cons (o b : Bool) (w : List Bool) :
    twist o (b::w)=(Bool.xor b o)::twist o w := by
  cases o <;> cases b <;> rfl

 theorem complement_twist (o : Bool) (w : List Bool) :
    complement (twist o w)=twist (!o) w := by
  cases o <;> simp

 theorem binaryValue_append (v w : List Bool) :
    binaryValue (v++w)=2^w.length*binaryValue v+binaryValue w := by
  induction v with
  | nil => simp [binaryValue]
  | cons b v ih =>
    cases b <;> simp [binaryValue, ih, pow_add]
    ring

 theorem binaryValue_reverse_bits (n : ℕ) : binaryValue n.bits.reverse=n := by
  induction n using Nat.binaryRec with
  | zero => simp [binaryValue]
  | bit b n ih =>
    by_cases hn : n=0
    · subst n
      cases b <;> simp [Nat.bit, binaryValue]
    · rw [Nat.bits_append_bit n b (fun h => (hn h).elim), List.reverse_cons, binaryValue_append, ih]
      cases b <;> simp [binaryValue, Nat.bit]

end HankelAutomaticity
