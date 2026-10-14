import MainTheorems.PreorderGamma.Macaulay.FiniteCodes
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma.Macaulay

variable {V : Type*} [DecidableEq V]

def ballotPrefix (index : V → ℕ) (U : Finset V) (m : ℕ) : Finset V :=
  U.filter fun v => index v < m

def IsBallotWithin (index : V → ℕ) (U A : Finset V) : Prop :=
  A ⊆ U ∧ ∀ m, 2 * (ballotPrefix index A m).card ≤ (ballotPrefix index U m).card

omit [DecidableEq V] in
theorem prefix_mono (index : V → ℕ) {U W : Finset V} (h : U ⊆ W) (m : ℕ) :
    ballotPrefix index U m ⊆ ballotPrefix index W m := Finset.filter_subset_filter _ h

omit [DecidableEq V] in
theorem IsBallotWithin.subset {index : V → ℕ} {U A B : Finset V}
    (hA : IsBallotWithin index U A) (hBA : B ⊆ A) : IsBallotWithin index U B := by
  refine ⟨hBA.trans hA.1, fun m => ?_⟩
  exact (Nat.mul_le_mul_left 2 (Finset.card_le_card (prefix_mono index hBA m))).trans (hA.2 m)

omit [DecidableEq V] in
theorem IsBallotWithin.enlarge {index : V → ℕ} {U W A : Finset V}
    (hA : IsBallotWithin index U A) (hUW : U ⊆ W) : IsBallotWithin index W A := by
  exact ⟨hA.1.trans hUW, fun m => (hA.2 m).trans
    (Finset.card_le_card (prefix_mono index hUW m))⟩

omit [DecidableEq V] in
theorem prefix_eq_self {index : V → ℕ} {U : Finset V} {m : ℕ}
    (h : ∀ v ∈ U, index v < m) : ballotPrefix index U m = U := Finset.filter_eq_self.mpr h

omit [DecidableEq V] in
theorem IsBallotWithin.card_bound {index : V → ℕ} {U A : Finset V}
    (hA : IsBallotWithin index U A) : 2 * A.card ≤ U.card := by
  have hu : ballotPrefix index U (U.sup index + 1) = U :=
    prefix_eq_self fun v hv => Nat.lt_succ_of_le (Finset.le_sup hv)
  have ha : ballotPrefix index A (U.sup index + 1) = A :=
    prefix_eq_self fun v hv => Nat.lt_succ_of_le (Finset.le_sup (hA.1 hv))
  simpa only [hu, ha] using hA.2 (U.sup index + 1)

omit [DecidableEq V] in
@[simp] theorem isBallotWithin_empty (index : V → ℕ) (U : Finset V) :
    IsBallotWithin index U ∅ := by
  simp [IsBallotWithin, ballotPrefix]

noncomputable def ballotSets (index : V → ℕ) (U : Finset V) (r : ℕ) : Finset (Finset V) := by
  classical
  exact (U.powersetCard r).filter (IsBallotWithin index U)

omit [DecidableEq V] in
@[simp] theorem mem_ballotSets {index : V → ℕ} {U A : Finset V} {r : ℕ} :
    A ∈ ballotSets index U r ↔ IsBallotWithin index U A ∧ A.card = r := by
  classical
  simp only [ballotSets, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hc⟩, hb⟩
    exact ⟨hb, hc⟩
  · rintro ⟨hb, hc⟩
    exact ⟨⟨hb.1, hc⟩, hb⟩

omit [DecidableEq V] in
@[simp] theorem ballotSets_zero (index : V → ℕ) (U : Finset V) :
    ballotSets index U 0 = {∅} := by
  classical
  ext A
  simp only [mem_ballotSets, Finset.mem_singleton, Finset.card_eq_zero]
  constructor
  · exact fun h => h.2
  · intro h
    subst A
    exact ⟨isBallotWithin_empty index U, rfl⟩

omit [DecidableEq V] in
theorem ballotSets_empty_of_large (index : V → ℕ) (U : Finset V) (r : ℕ)
    (h : U.card < 2 * r) : ballotSets index U r = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A ha
  obtain ⟨hb, hc⟩ := mem_ballotSets.mp ha
  have hg := hb.card_bound
  omega

end ResearchMain.PreorderGamma.Macaulay
