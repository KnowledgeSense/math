import MeanMaximumForests.GraphSemantics

namespace MeanMaximumForests
open Finset

/-- Exact integer counting data, before centering the cardinality sums. -/
@[ext] structure CountingStatistics where
  count : ℕ
  rootDeletedCount : ℕ
  sizeSum : ℕ
  rootDeletedSizeSum : ℕ
  alpha : ℕ
  vertices : ℕ
  deriving DecidableEq

def ForestExpr.statistics : ForestExpr → CountingStatistics
  | .empty => ⟨1, 1, 0, 0, 0, 0⟩
  | .union A B =>
    let a := A.statistics
    let b := B.statistics
    ⟨a.count * b.count, a.rootDeletedCount * b.rootDeletedCount,
      a.sizeSum * b.count + a.count * b.sizeSum,
      a.rootDeletedSizeSum * b.rootDeletedCount + a.rootDeletedCount * b.rootDeletedSizeSum,
      a.alpha + b.alpha, a.vertices + b.vertices⟩
  | .root A =>
    let a := A.statistics
    ⟨a.count + a.rootDeletedCount, a.count,
      a.sizeSum + a.rootDeletedSizeSum + a.rootDeletedCount, a.sizeSum,
      a.alpha + (if flag A then 0 else 1), a.vertices + 1⟩

theorem ForestExpr.vector_statistics (c : ℝ) (A : ForestExpr) :
    vector c A = ⟨A.statistics.count, A.statistics.rootDeletedCount,
      A.statistics.sizeSum - c * A.statistics.alpha * A.statistics.count,
      A.statistics.rootDeletedSizeSum - c * A.statistics.alpha * A.statistics.rootDeletedCount⟩ := by
  induction A with
  | empty => simp [vector, unitVector, statistics]
  | union A B ha hb =>
    simp only [vector, ha, hb, product, statistics, Nat.cast_add, Nat.cast_mul]
    ext <;> simp only <;> ring
  | root A ha =>
    simp only [vector, ha, plant, statistics]
    cases hf : flag A <;> ext <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_zero, Nat.cast_one] <;> ring

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

theorem ForestRealization.alpha_statistics {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : independenceNumber G s = A.statistics.alpha := by
  induction h with
  | empty => simp [ForestExpr.statistics]
  | union hd he hA hB ihA ihB =>
    rw [independenceNumber_union G hd he, ihA, ihB]
    rfl
  | root r hr he hA ih =>
    rw [hA.root_independenceNumber G hr he, ih]
    rfl

theorem ForestRealization.card_statistics {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : s.card = A.statistics.vertices := by
  induction h with
  | empty => rfl
  | union hd he hA hB ihA ihB =>
    rw [card_union_of_disjoint hd, ihA, ihB]
    rfl
  | root r hr he hA ih =>
    rw [card_insert_of_notMem hr, ih]
    rfl

theorem ForestRealization.count_statistics {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : independentSetCount G s = A.statistics.count := by
  have he := congrArg ConeVector.p ((h.vector_eq G 0).trans (A.vector_statistics 0))
  change (independentSetCount G s : ℝ) = A.statistics.count at he
  exact_mod_cast he

theorem ForestRealization.sizeSum_statistics {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : independentSetSizeSum G s = A.statistics.sizeSum := by
  have he := congrArg ConeVector.x ((h.vector_eq G 0).trans (A.vector_statistics 0))
  simp only [graphVector, zero_mul, sub_zero] at he
  exact_mod_cast he

end MeanMaximumForests
