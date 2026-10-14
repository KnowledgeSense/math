import MeanMaximumForests.CountingStatistics

namespace MeanMaximumForests.Witness

/-- A one-vertex rooted tree. -/
def leaf : ForestExpr := .root .empty

def copies : ℕ → ForestExpr → ForestExpr
  | 0, _ => .empty
  | n + 1, A => .union A (copies n A)

def extend (Q : ForestExpr) : ForestExpr := .root (.union leaf (.root Q))
def unary (Q : ForestExpr) : ForestExpr := .root Q
def triple (Q : ForestExpr) : ForestExpr := .root (copies 3 (unary Q))
def amplify (Q : ForestExpr) : ForestExpr := .root (.union leaf (.root (copies 7 (triple Q))))

def sequence : ℕ → ForestExpr
  | 0 => extend (.root (copies 2 leaf))
  | n + 1 => extend (amplify (sequence n))

/-- The 71308-vertex tree from equation (5.1) of the release. -/
def tree : ForestExpr := sequence 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem vertex_count : tree.statistics.vertices = 71308 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem independence_number : tree.statistics.alpha = 48619 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem strict_upper_bound :
    1000000 * tree.statistics.sizeSum < 473403 * tree.statistics.alpha * tree.statistics.count := by decide

end MeanMaximumForests.Witness
