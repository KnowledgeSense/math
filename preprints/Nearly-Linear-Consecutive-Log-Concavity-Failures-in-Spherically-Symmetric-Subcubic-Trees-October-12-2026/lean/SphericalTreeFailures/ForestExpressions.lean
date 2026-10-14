namespace SphericalTreeFailures

/-- Finite rooted forests built by disjoint union and adjoining a new root. -/
inductive ForestExpr where
  | empty
  | union (left right : ForestExpr)
  | root (children : ForestExpr)

def flag : ForestExpr → Bool
  | .empty => false
  | .union A B => flag A || flag B
  | .root A => !(flag A)

end SphericalTreeFailures
