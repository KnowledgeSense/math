import MeanMaximumForests.GraphConstruction
import MeanMaximumForests.WitnessStatistics

namespace MeanMaximumForests

/-- The uniform independent-set mean computed from a forest expression. -/
noncomputable def ForestExpr.mean (A : ForestExpr) : ℝ :=
  A.statistics.sizeSum / A.statistics.count

/-- The mean after removing the distinguished root of every component. -/
noncomputable def ForestExpr.deletedMean (A : ForestExpr) : ℝ :=
  A.statistics.rootDeletedSizeSum / A.statistics.rootDeletedCount

theorem ForestExpr.count_pos (A : ForestExpr) : 0 < A.statistics.count := by
  induction A with
  | empty => decide
  | union A B hA hB => exact Nat.mul_pos hA hB
  | root A hA => exact Nat.add_pos_left hA _

theorem ForestExpr.deletedCount_pos (A : ForestExpr) : 0 < A.statistics.rootDeletedCount := by
  induction A with
  | empty => decide
  | union A B hA hB => exact Nat.mul_pos hA hB
  | root A _ => exact A.count_pos

theorem ForestExpr.deletedCount_le (A : ForestExpr) :
    A.statistics.rootDeletedCount ≤ A.statistics.count := by
  induction A with
  | empty => exact le_refl _
  | union A B hA hB => exact Nat.mul_le_mul hA hB
  | root A _ => exact Nat.le_add_right _ _

theorem ForestExpr.deletedCount_lt (A : ForestExpr) (hA : 0 < A.statistics.vertices) :
    A.statistics.rootDeletedCount < A.statistics.count := by
  induction A with
  | empty => simp [statistics] at hA
  | union A B ihA ihB =>
    change A.statistics.rootDeletedCount * B.statistics.rootDeletedCount <
      A.statistics.count * B.statistics.count
    by_cases ha : 0 < A.statistics.vertices
    · exact Nat.mul_lt_mul_of_lt_of_le (ihA ha) B.deletedCount_le B.count_pos
    · have hb : 0 < B.statistics.vertices := by
        change 0 < A.statistics.vertices + B.statistics.vertices at hA
        omega
      exact Nat.mul_lt_mul_of_le_of_lt A.deletedCount_le (ihB hb) A.count_pos
  | root A _ =>
    change A.statistics.count < A.statistics.count + A.statistics.rootDeletedCount
    exact Nat.lt_add_of_pos_right A.deletedCount_pos

theorem ForestExpr.mean_union (A B : ForestExpr) :
    (A.union B).mean = A.mean + B.mean := by
  have ha : (A.statistics.count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr A.count_pos)
  have hb : (B.statistics.count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr B.count_pos)
  simp only [mean, statistics, Nat.cast_add, Nat.cast_mul]
  field_simp

theorem ForestExpr.deletedMean_union (A B : ForestExpr) :
    (A.union B).deletedMean = A.deletedMean + B.deletedMean := by
  have ha : (A.statistics.rootDeletedCount : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr A.deletedCount_pos)
  have hb : (B.statistics.rootDeletedCount : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr B.deletedCount_pos)
  simp only [deletedMean, statistics, Nat.cast_add, Nat.cast_mul]
  field_simp

theorem ForestExpr.mean_root (A : ForestExpr) :
    A.root.mean = A.mean +
      (A.statistics.rootDeletedCount : ℝ) / (A.statistics.count + A.statistics.rootDeletedCount) *
        (1 + A.deletedMean - A.mean) := by
  have hp : (A.statistics.count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr A.count_pos)
  have hq : (A.statistics.rootDeletedCount : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr A.deletedCount_pos)
  have hpq : (A.statistics.count + A.statistics.rootDeletedCount : ℝ) ≠ 0 := by positivity
  simp only [mean, deletedMean, statistics, Nat.cast_add]
  field_simp
  ring

namespace HubTrees

/-- `k` disjoint copies, with an empty union when `k = 0`. -/
abbrev copies := Witness.copies

/-- A new hub joins every component root in `k` copies of `A`, plus `r` fresh leaves. -/
def hub (A : ForestExpr) (k r : ℕ) : ForestExpr :=
  .root (.union (copies k A) (copies r Witness.leaf))

theorem copies_count (A : ForestExpr) (k : ℕ) :
    (copies k A).statistics.count = A.statistics.count ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [copies, Witness.copies, ForestExpr.statistics, ih, pow_succ, Nat.mul_comm]

theorem copies_deletedCount (A : ForestExpr) (k : ℕ) :
    (copies k A).statistics.rootDeletedCount = A.statistics.rootDeletedCount ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [copies, Witness.copies, ForestExpr.statistics, ih, pow_succ, Nat.mul_comm]

theorem copies_vertices (A : ForestExpr) (k : ℕ) :
    (copies k A).statistics.vertices = k * A.statistics.vertices := by
  induction k with
  | zero => simp [copies, Witness.copies, ForestExpr.statistics]
  | succ k ih => simp [copies, Witness.copies, ForestExpr.statistics, ih, Nat.succ_mul, Nat.add_comm]

theorem copies_alpha (A : ForestExpr) (k : ℕ) :
    (copies k A).statistics.alpha = k * A.statistics.alpha := by
  induction k with
  | zero => simp [copies, Witness.copies, ForestExpr.statistics]
  | succ k ih => simp [copies, Witness.copies, ForestExpr.statistics, ih, Nat.succ_mul, Nat.add_comm]

theorem copies_mean (A : ForestExpr) (k : ℕ) : (copies k A).mean = k * A.mean := by
  induction k with
  | zero => simp [copies, Witness.copies, ForestExpr.mean, ForestExpr.statistics]
  | succ k ih =>
    change (A.union (copies k A)).mean = _
    rw [ForestExpr.mean_union, ih]
    push_cast
    ring

theorem copies_deletedMean (A : ForestExpr) (k : ℕ) :
    (copies k A).deletedMean = k * A.deletedMean := by
  induction k with
  | zero => simp [copies, Witness.copies, ForestExpr.deletedMean, ForestExpr.statistics]
  | succ k ih =>
    change (A.union (copies k A)).deletedMean = _
    rw [ForestExpr.deletedMean_union, ih]
    push_cast
    ring

theorem hub_isTree (A : ForestExpr) (k r : ℕ) : (hub A k r).graph.IsTree :=
  ForestExpr.root_graph_isTree _

theorem hub_vertices (A : ForestExpr) (k r : ℕ) :
    Fintype.card (hub A k r).Vertex = k * A.statistics.vertices + r + 1 := by
  rw [ForestExpr.graph_card_statistics]
  change (copies k A).statistics.vertices + (copies r Witness.leaf).statistics.vertices + 1 = _
  rw [copies_vertices, copies_vertices]
  simp [Witness.leaf, ForestExpr.statistics]

theorem hub_alpha_bounds (A : ForestExpr) (k r : ℕ) :
    k * A.statistics.alpha + r ≤ (hub A k r).graph.indepNum ∧
      (hub A k r).graph.indepNum ≤ k * A.statistics.alpha + r + 1 := by
  rw [ForestExpr.graph_indepNum_statistics]
  simp only [hub, ForestExpr.statistics, copies_alpha, Witness.leaf, flag,
    Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mul_one]
  all_goals simp_all only [Bool.or_eq_true]
  all_goals split_ifs at * <;> omega

/-- The root-avoiding fraction lies strictly between zero and one for a nonempty forest. -/
noncomputable def rootAvoidance (A : ForestExpr) : ℝ :=
  A.statistics.rootDeletedCount / A.statistics.count

theorem rootAvoidance_pos (A : ForestExpr) : 0 < rootAvoidance A :=
  div_pos (Nat.cast_pos.mpr A.deletedCount_pos) (Nat.cast_pos.mpr A.count_pos)

theorem rootAvoidance_lt_one (A : ForestExpr) (hA : 0 < A.statistics.vertices) :
    rootAvoidance A < 1 := by
  apply (div_lt_one (Nat.cast_pos.mpr A.count_pos)).mpr
  exact_mod_cast A.deletedCount_lt hA

/-- Exact probability that the new hub belongs to the uniformly sampled independent set. -/
noncomputable def hubOccupation (A : ForestExpr) (k r : ℕ) : ℝ :=
  rootAvoidance A ^ k / (2 ^ r + rootAvoidance A ^ k)

theorem hubOccupation_eq (A : ForestExpr) (k r : ℕ) :
    (copies k A |>.union (copies r Witness.leaf)).statistics.rootDeletedCount /
      ((copies k A |>.union (copies r Witness.leaf)).statistics.count +
       (copies k A |>.union (copies r Witness.leaf)).statistics.rootDeletedCount : ℝ) =
    hubOccupation A k r := by
  have hp : (A.statistics.count : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr A.count_pos)
  have hq : (A.statistics.rootDeletedCount : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr A.deletedCount_pos)
  have hp' : (0 : ℝ) < A.statistics.count := Nat.cast_pos.mpr A.count_pos
  have hq' : (0 : ℝ) < A.statistics.rootDeletedCount := Nat.cast_pos.mpr A.deletedCount_pos
  simp only [ForestExpr.statistics, copies_count, copies_deletedCount, Witness.leaf,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, one_pow, mul_one]
  unfold hubOccupation rootAvoidance
  rw [div_pow]
  field_simp
  ring

/-- Exact mean formula for the actual finite hub tree. -/
theorem hub_mean (A : ForestExpr) (k r : ℕ) :
    graphMean (hub A k r).graph = k * A.mean + r / 2 +
      hubOccupation A k r * (1 + k * A.deletedMean - (k * A.mean + r / 2)) := by
  rw [ForestExpr.graphMean_statistics]
  change (hub A k r).mean = _
  unfold hub
  rw [ForestExpr.mean_root, hubOccupation_eq, ForestExpr.mean_union,
    ForestExpr.deletedMean_union, copies_mean, copies_mean, copies_deletedMean, copies_deletedMean]
  norm_num [Witness.leaf, ForestExpr.mean, ForestExpr.deletedMean, ForestExpr.statistics]
  ring

end HubTrees
end MeanMaximumForests
