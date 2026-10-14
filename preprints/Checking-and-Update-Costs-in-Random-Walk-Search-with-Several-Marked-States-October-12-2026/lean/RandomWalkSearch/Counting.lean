import RandomWalkSearch.Infinite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # Uniform-translate counting for arbitrary completed executions -/

namespace RandomWalkSearch.Cycle

variable {k : ℕ}

/-- The exact translates whose sparse progression contains `x`. -/
def progressionStarts (x : Vertex k) : Finset (Vertex k) :=
  (Finset.range (k ^ 6)).image (fun j : ℕ => x - (j * L k : ℕ))

@[simp] theorem mem_progressionStarts (x a : Vertex k) :
    a ∈ progressionStarts x ↔ x ∈ progression a := by
  simp only [progressionStarts, progression, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, sub_add_cancel _ _⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, hj, by rw [← hx]; simp⟩

theorem card_progressionStarts_le (x : Vertex k) :
    (progressionStarts x).card ≤ k ^ 6 :=
  Finset.card_image_le.trans_eq (Finset.card_range _)

def markedStarts (x : Vertex k) : Finset (Vertex k) :=
  intervalStarts (D k) x ∪ progressionStarts x

@[simp] theorem mem_markedStarts (x a : Vertex k) :
    a ∈ markedStarts x ↔ x ∈ marked a := by
  simp [markedStarts, marked, interval]

theorem card_markedStarts_le (x : Vertex k) :
    (markedStarts x).card ≤ D k + k ^ 6 :=
  (Finset.card_union_le ..).trans
    (Nat.add_le_add (card_intervalStarts_le ..) (card_progressionStarts_le ..))

variable [NeZero (N k)]

noncomputable def successfulTranslates (p : Policy (Vertex k))
    (r : Tapes (Vertex k)) : Finset (Vertex k) := by
  classical
  exact Finset.univ.filter (fun a => Succeeds p r (oracle a))

@[simp] theorem mem_successfulTranslates (p : Policy (Vertex k))
    (r : Tapes (Vertex k)) (a : Vertex k) :
    a ∈ successfulTranslates p r ↔ Succeeds p r (oracle a) := by
  classical
  simp [successfulTranslates]

/-- Universal pointwise translate counting. Every source of private randomness
and every setup/update tape is fixed, with no finite-policy enumeration. -/
theorem successfulTranslates_subset (p : Policy (Vertex k)) (r : Tapes (Vertex k)) :
    successfulTranslates p r ⊆
      (checkedEver p r negativeOracle ∪ outputsEver p r negativeOracle).biUnion markedStarts := by
  intro a ha
  obtain ⟨x, hx, hmark⟩ := succeeds_mem_negative p r (oracle a)
    ((mem_successfulTranslates p r a).mp ha)
  exact Finset.mem_biUnion.mpr ⟨x, hx, (mem_markedStarts x a).mpr (by simpa [oracle] using hmark)⟩

/-- The check-only bound permits infinitely many updates. -/
theorem hard_checks_count (Q : ℕ) (p : Policy (Vertex k)) (r : Tapes (Vertex k))
    (hQ : ∀ n, (run p r negativeOracle n).checks ≤ Q) :
    (successfulTranslates p r).card ≤ (Q + 1) * (D k + k ^ 6) := by
  calc
    _ ≤ ((checkedEver p r negativeOracle ∪ outputsEver p r negativeOracle).biUnion markedStarts).card :=
      Finset.card_le_card (successfulTranslates_subset p r)
    _ ≤ (checkedEver p r negativeOracle ∪ outputsEver p r negativeOracle).card * (D k + k ^ 6) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun x _ => card_markedStarts_le x)
    _ ≤ (Q + 1) * (D k + k ^ 6) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_union_le ..).trans
        (Nat.add_le_add (checkedEver_card_le Q p r negativeOracle hQ) (outputsEver_card_le ..))

/-- Separate the dense interval, the sparse progression and the unrestricted
final output in the all-negative transcript. -/
theorem successfulTranslates_local_subset (p : Policy (Vertex k))
    (r : Tapes (Vertex k))
    (hl : ∀ n, (run p r negativeOracle n).halted = false →
      Local (run p r negativeOracle n) (p (run p r negativeOracle n))) :
    successfulTranslates p r ⊆
      exposure (D k) (visitedEver p r negativeOracle) ∪
      (checkedEver p r negativeOracle).biUnion progressionStarts ∪
      (outputsEver p r negativeOracle).biUnion markedStarts := by
  intro a ha
  obtain ⟨x, hx, hmark⟩ := succeeds_mem_negative p r (oracle a)
    ((mem_successfulTranslates p r a).mp ha)
  have hm : x ∈ marked a := by simpa [oracle] using hmark
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hm with hi | hg
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨x, checkedEver_subset_visitedEver p r negativeOracle hl hx,
        (mem_intervalStarts ..).mpr hi⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨x, hx, (mem_progressionStarts ..).mpr hg⟩
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨x, hx, (mem_markedStarts ..).mpr hm⟩

/-- Full-infinite-run hard restoration bound before integrating randomness. -/
theorem hard_restoration_count (b T Q : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hl : ∀ n, (run p (lazyTapes z w) negativeOracle n).halted = false →
      Local (run p (lazyTapes z w) negativeOracle n)
        (p (run p (lazyTapes z w) negativeOracle n)))
    (hb : ∀ n, (run p (lazyTapes z w) negativeOracle n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) negativeOracle n).updates ≤ T)
    (hQ : ∀ n, (run p (lazyTapes z w) negativeOracle n).checks ≤ Q) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (Q + 1) * k ^ 6 + (b + 1) * D k + T := by
  have hI := visitedEver_exposure_le (D k) b T p z w negativeOracle hl hb hT
  have hG := Finset.card_biUnion_le_card_mul (checkedEver p (lazyTapes z w) negativeOracle)
    progressionStarts (k ^ 6) (fun x _ => card_progressionStarts_le x)
  have hO := Finset.card_biUnion_le_card_mul (outputsEver p (lazyTapes z w) negativeOracle)
    markedStarts (D k + k ^ 6) (fun x _ => card_markedStarts_le x)
  have hG' := Nat.mul_le_mul_right (k ^ 6)
    (checkedEver_card_le Q p (lazyTapes z w) negativeOracle hQ)
  have hO' := Nat.mul_le_mul_right (D k + k ^ 6)
    (outputsEver_card_le p (lazyTapes z w) negativeOracle)
  have hu := (Finset.card_le_card (successfulTranslates_local_subset p (lazyTapes z w) hl)).trans
    (Finset.card_union_le ..)
  have hu' := Finset.card_union_le
    (exposure (D k) (visitedEver p (lazyTapes z w) negativeOracle))
    ((checkedEver p (lazyTapes z w) negativeOracle).biUnion progressionStarts)
  nlinarith

/-- The assumptions of the hard-budget theorem refer only to genuine runs.
Consistency completion is proved to transfer them to the fictitious oracle. -/
theorem genuine_hard_restoration_count (b T Q : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hp : Restoration oracle b p (lazyTapes z w))
    (hbud : ∀ a n, Within (T : ℕ∞) (Q : ℕ∞) (run p (lazyTapes z w) (oracle a) n)) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (Q + 1) * k ^ 6 + (b + 1) * D k + T := by
  have heq : successfulTranslates p (lazyTapes z w) =
      successfulTranslates (complete oracle p) (lazyTapes z w) := by
    ext a
    simp only [mem_successfulTranslates, complete_succeeds_iff]
  rw [heq]
  apply hard_restoration_count b T Q (complete oracle p) z w
  · exact complete_local oracle b p (lazyTapes z w) hp negativeOracle
  · exact run_setup_le b _ _ negativeOracle
      (complete_setupBound oracle b p (lazyTapes z w) hp negativeOracle)
  · intro n
    have h := (complete_within oracle T Q p (lazyTapes z w) hbud negativeOracle n).1
    exact_mod_cast h
  · intro n
    have h := (complete_within oracle T Q p (lazyTapes z w) hbud negativeOracle n).2
    exact_mod_cast h

end RandomWalkSearch.Cycle
