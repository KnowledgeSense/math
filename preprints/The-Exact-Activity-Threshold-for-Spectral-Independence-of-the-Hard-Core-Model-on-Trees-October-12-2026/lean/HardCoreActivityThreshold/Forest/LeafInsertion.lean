import HardCoreActivityThreshold.Forest.GraphConstruction

namespace HardCoreActivityThreshold.Forest

 def ForestExpr.insertLeaf : (A : ForestExpr) → A.Vertex → ForestExpr
  | .empty, v => v.elim
  | .union A B, .inl v => .union (A.insertLeaf v) B
  | .union A B, .inr v => .union A (B.insertLeaf v)
  | .root A, none => .root (.union A (.root .empty))
  | .root A, some v => .root (A.insertLeaf v)

 def ForestExpr.leafDecode : (A : ForestExpr) → (v : A.Vertex) → (A.insertLeaf v).Vertex → Option A.Vertex
  | .empty, v, _ => v.elim
  | .union A _, .inl v, .inl w => (A.leafDecode v w).map Sum.inl
  | .union _ _, .inl _, .inr w => some (.inr w)
  | .union _ _, .inr _, .inl w => some (.inl w)
  | .union _ B, .inr v, .inr w => (B.leafDecode v w).map Sum.inr
  | .root _, none, none => some none
  | .root _, none, some (.inl w) => some (some w)
  | .root _, none, some (.inr none) => none
  | .root _, none, some (.inr (some w)) => w.elim
  | .root _, some _, none => some none
  | .root A, some v, some w => (A.leafDecode v w).map Option.some

 def ForestExpr.leafEncode : (A : ForestExpr) → (v : A.Vertex) → Option A.Vertex → (A.insertLeaf v).Vertex
  | .empty, v, _ => v.elim
  | .union A _, .inl v, none => .inl (A.leafEncode v none)
  | .union A _, .inl v, some (.inl w) => .inl (A.leafEncode v (some w))
  | .union _ _, .inl _, some (.inr w) => .inr w
  | .union _ B, .inr v, none => .inr (B.leafEncode v none)
  | .union _ _, .inr _, some (.inl w) => .inl w
  | .union _ B, .inr v, some (.inr w) => .inr (B.leafEncode v (some w))
  | .root _, none, none => some (.inr none)
  | .root _, none, some none => none
  | .root _, none, some (some w) => some (.inl w)
  | .root A, some v, none => some (A.leafEncode v none)
  | .root _, some _, some none => none
  | .root A, some v, some (some w) => some (A.leafEncode v (some w))

 theorem ForestExpr.leafDecode_encode (A : ForestExpr) (v : A.Vertex) (w : Option A.Vertex) :
    A.leafDecode v (A.leafEncode v w)=w := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb =>
    cases v with
    | inl v =>
      cases w with
      | none => simp [leafEncode,leafDecode,ha]
      | some w => cases w <;> simp [leafEncode,leafDecode,ha]
    | inr v =>
      cases w with
      | none => simp [leafEncode,leafDecode,hb]
      | some w => cases w <;> simp [leafEncode,leafDecode,hb]
  | root A ha =>
    cases v with
    | none => cases w with
      | none => rfl
      | some w => cases w <;> rfl
    | some v => cases w with
      | none => simp [leafEncode,leafDecode,ha]
      | some w => cases w <;> simp [leafEncode,leafDecode,ha]

theorem ForestExpr.leafEncode_decode (A : ForestExpr) (v : A.Vertex) (w : (A.insertLeaf v).Vertex) :
    A.leafEncode v (A.leafDecode v w)=w := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb =>
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        have hi := ha v w
        cases he : A.leafDecode v w <;> simp [leafDecode,leafEncode,he] at hi ⊢ <;> simp [hi] <;> rfl
      | inr w => rfl
    | inr v =>
      cases w with
      | inl w => rfl
      | inr w =>
        have hi := hb v w
        cases he : B.leafDecode v w <;> simp [leafDecode,leafEncode,he] at hi ⊢ <;> simp [hi] <;> rfl
  | root A ha =>
    cases v with
    | none =>
      cases w with
      | none => rfl
      | some w =>
        cases w with
        | inl w => rfl
        | inr w => cases w with
          | none => rfl
          | some w => exact w.elim
    | some v =>
      cases w with
      | none => rfl
      | some w =>
        have hi := ha v w
        cases he : A.leafDecode v w <;> simp [leafDecode,leafEncode,he] at hi ⊢ <;> simp [hi] <;> rfl

 def ForestExpr.leafEquiv (A : ForestExpr) (v : A.Vertex) : (A.insertLeaf v).Vertex ≃ Option A.Vertex where
  toFun := A.leafDecode v
  invFun := A.leafEncode v
  left_inv := A.leafEncode_decode v
  right_inv := A.leafDecode_encode v

theorem ForestExpr.leafEncode_root (A : ForestExpr) (v : A.Vertex) (w : Option A.Vertex) :
    (A.insertLeaf v).IsRoot (A.leafEncode v w) ↔ w.elim False A.IsRoot := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb =>
    cases v with
    | inl v =>
      rcases w with _|(_|_) <;> simp [insertLeaf,leafEncode,IsRoot,ha]
    | inr v =>
      rcases w with _|(_|_) <;> simp [insertLeaf,leafEncode,IsRoot,hb]
  | root A ha =>
    cases v with
    | none => rcases w with _|(_|_) <;> simp [insertLeaf,leafEncode,IsRoot]
    | some v => rcases w with _|(_|_) <;> simp [insertLeaf,leafEncode,IsRoot]

 def ForestExpr.leafAdj (A : ForestExpr) (v : A.Vertex) : Option A.Vertex → Option A.Vertex → Prop
  | none,none => False
  | none,some w => v=w
  | some u,none => u=v
  | some u,some w => A.Adj u w

 theorem ForestExpr.leafEncode_adj (A : ForestExpr) (v : A.Vertex) (x y : Option A.Vertex) :
    (A.insertLeaf v).Adj (A.leafEncode v x) (A.leafEncode v y) ↔ A.leafAdj v x y := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb =>
    cases v with
    | inl v =>
      rcases x with _|(_|_) <;> rcases y with _|(_|_) <;>
        simp [insertLeaf,leafEncode,Adj,leafAdj,ha]
    | inr v =>
      rcases x with _|(_|_) <;> rcases y with _|(_|_) <;>
        simp [insertLeaf,leafEncode,Adj,leafAdj,hb]
  | root A ha =>
    cases v with
    | none =>
      rcases x with _|(_|_) <;> rcases y with _|(_|_) <;>
        simp [insertLeaf,leafEncode,Adj,leafAdj,IsRoot]
    | some v =>
      rcases x with _|(_|_) <;> rcases y with _|(_|_) <;>
        simp [insertLeaf,leafEncode,Adj,leafAdj,ha,leafEncode_root]

end HardCoreActivityThreshold.Forest
