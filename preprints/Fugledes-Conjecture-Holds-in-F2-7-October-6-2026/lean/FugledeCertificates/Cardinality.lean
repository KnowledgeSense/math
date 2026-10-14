import Std

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace FugledeCertificates

/-- Smith exponents of the order-128 Walsh matrix, with binomial multiplicities. -/
def smithExponents : List Nat :=
  [0] ++ List.replicate 7 1 ++ List.replicate 21 2 ++ List.replicate 35 3 ++
  List.replicate 35 4 ++ List.replicate 21 5 ++ List.replicate 7 6 ++ [7]

/-- The 2-adic valuation for the positive orders considered below. -/
def valuationTwoUpToSeven (m : Nat) : Nat :=
  ((List.range 8).filter fun k => m % (2 ^ k) == 0).length - 1

def determinantValuation (m : Nat) : Nat := (m / 2) * valuationTwoUpToSeven m

def smithLowerBound (m : Nat) : Nat := (smithExponents.take m).sum

def excludedOrders : List Nat := [12, 20, 24, 28, 36, 40, 44, 48, 52, 56, 60]

theorem smith_exponents_count : smithExponents.length = 128 := by decide

theorem excluded_order_count : excludedOrders.length = 11 := by decide

theorem excluded_order_inequalities :
    ∀ m ∈ excludedOrders, determinantValuation m < smithLowerBound m := by
  decide

theorem excluded_orders_exhaust_multiples :
    ∀ m : Fin 64,
      (4 ≤ m.val ∧ m.val % 4 = 0 ∧
        ¬ (∃ k : Fin 8, m.val = 2 ^ k.val)) ↔ m.val ∈ excludedOrders := by
  decide


end FugledeCertificates
