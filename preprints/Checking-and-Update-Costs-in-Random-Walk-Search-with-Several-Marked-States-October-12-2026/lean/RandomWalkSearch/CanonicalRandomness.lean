import RandomWalkSearch.TapeLaw
import RandomWalkSearch.LazyExitLaw
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! # A concrete uniform setup and iid infinite lazy-update tape

The endpoint algorithms can run on this probability space without any assumed
cylinder law. The setup vertex is uniform and independent of the full tape;
every update symbol is independently uniform on `Fin 4`.
-/

namespace RandomWalkSearch.LazyWalk

/-- Extend a finite nested-product tape by zeros. -/
def tapeRead : (n : ℕ) → Tape n → ℕ → Fin 4
  | 0, _, _ => 0
  | n+1, t, j => if j = n then t.2 else tapeRead n t.1 j

theorem prefixTape_eq_iff (n : ℕ) (w : ℕ → Fin 4) (t : Tape n) :
    prefixTape n w = t ↔ ∀ j < n, w j = tapeRead n t j := by
  induction n with
  | zero => simp [prefixTape]
  | succ n ih =>
    rcases t with ⟨t, q⟩
    simp only [prefixTape, Prod.mk.injEq, ih]
    constructor
    · rintro ⟨hn, hq⟩ j hj
      by_cases heq : j = n
      · simpa [tapeRead, heq] using hq
      · simpa [tapeRead, heq] using hn j (by omega)
    · intro h
      constructor
      · intro j hj
        simpa [tapeRead, show j ≠ n by omega] using h j (by omega)
      · simpa [tapeRead] using h n (by omega)

@[simp] theorem card_tape (n : ℕ) : Fintype.card (Tape n) = 4^n := by
  induction n with
  | zero => simp [Tape]
  | succ n ih => simp [Tape, Fintype.card_prod, ih, pow_succ]

end RandomWalkSearch.LazyWalk

namespace RandomWalkSearch.Cycle.Canonical
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

abbrev Outcome (k : ℕ) := Vertex k × (ℕ → Fin 4)

noncomputable def symbolMeasure : Measure (Fin 4) :=
  (PMF.uniformOfFintype (Fin 4)).toMeasure

instance symbolMeasure_probability : IsProbabilityMeasure symbolMeasure := by
  unfold symbolMeasure
  infer_instance

@[simp] theorem symbolMeasure_singleton (q : Fin 4) :
    symbolMeasure {q} = (4 : ℝ≥0∞)⁻¹ := by
  simp [symbolMeasure, PMF.uniformOfFintype_apply]

noncomputable def tapeMeasure : Measure (ℕ → Fin 4) :=
  Measure.infinitePi (fun _ : ℕ => symbolMeasure)

instance tapeMeasure_probability : IsProbabilityMeasure tapeMeasure := by
  unfold tapeMeasure
  infer_instance

/-- The full tape really consists of independent symbols, not just a cost law. -/
theorem tape_independent : iIndepFun (fun n (w : ℕ → Fin 4) => w n) tapeMeasure := by
  exact iIndepFun_infinitePi (X := fun (_ : ℕ) (q : Fin 4) => q) (fun _ => measurable_id)

@[simp] theorem tape_symbol_law (n : ℕ) (q : Fin 4) :
    tapeMeasure {w | w n = q} = (4 : ℝ≥0∞)⁻¹ := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => symbolMeasure) n
  have hm := congrArg (fun μ : Measure (Fin 4) => μ {q}) h
  rw [Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton q)] at hm
  simpa [tapeMeasure, Set.preimage] using hm

theorem prefix_event_eq_pi (n : ℕ) (t : LazyWalk.Tape n) :
    {w | LazyWalk.prefixTape n w = t} =
      Set.pi (Finset.range n) (fun j => {LazyWalk.tapeRead n t j}) := by
  ext w
  simp [LazyWalk.prefixTape_eq_iff, Set.mem_pi]

theorem measurable_prefix_event (n : ℕ) (t : LazyWalk.Tape n) :
    MeasurableSet {w | LazyWalk.prefixTape n w = t} := by
  rw [prefix_event_eq_pi]
  exact MeasurableSet.pi (Finset.finite_toSet _).countable (fun _ _ => measurableSet_singleton _)

/-- The uniform prefix law follows from the infinite product measure. -/
theorem tape_prefix_law (n : ℕ) (t : LazyWalk.Tape n) :
    tapeMeasure {w | LazyWalk.prefixTape n w = t} =
      (Fintype.card (LazyWalk.Tape n) : ℝ≥0∞)⁻¹ := by
  rw [prefix_event_eq_pi]
  change Measure.infinitePi (fun _ : ℕ => symbolMeasure)
    (Set.pi (Finset.range n) (fun j => {LazyWalk.tapeRead n t j})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [← ENNReal.inv_pow]

variable (k : ℕ) [NeZero (N k)]

noncomputable def setupMeasure : Measure (Vertex k) :=
  (PMF.uniformOfFintype (Vertex k)).toMeasure

instance setupMeasure_probability : IsProbabilityMeasure (setupMeasure k) := by
  unfold setupMeasure
  infer_instance

@[simp] theorem setupMeasure_singleton (z : Vertex k) :
    setupMeasure k {z} = (N k : ℝ≥0∞)⁻¹ := by
  simp [setupMeasure, PMF.uniformOfFintype_apply, ZMod.card]

/-- A uniform setup, independently paired with a whole infinite iid tape. -/
noncomputable def measure : Measure (Outcome k) := (setupMeasure k).prod tapeMeasure

instance measure_probability : IsProbabilityMeasure (measure k) := by
  unfold measure
  infer_instance

theorem setup_independent_tape :
    IndepFun (fun ω : Outcome k => ω.1) (fun ω : Outcome k => ω.2) (measure k) := by
  exact indepFun_prod measurable_id measurable_id

@[simp] theorem setup_law (z : Vertex k) :
    measure k {ω | ω.1 = z} = (N k : ℝ≥0∞)⁻¹ := by
  have heq : {ω : Outcome k | ω.1 = z} = {z} ×ˢ Set.univ := by ext ω; simp
  rw [heq, measure, Measure.prod_prod]
  simp

omit [NeZero (N k)] in
theorem measurable_outcome_prefix (n : ℕ) (t : LazyWalk.Tape n) :
    MeasurableSet {ω : Outcome k | LazyWalk.prefixTape n ω.2 = t} :=
  (measurable_prefix_event n t).preimage measurable_snd

theorem outcome_prefix_law (n : ℕ) (t : LazyWalk.Tape n) :
    measure k {ω | LazyWalk.prefixTape n ω.2 = t} =
      (Fintype.card (LazyWalk.Tape n) : ℝ≥0∞)⁻¹ := by
  have heq : {ω : Outcome k | LazyWalk.prefixTape n ω.2 = t} =
      Set.univ ×ˢ {w | LazyWalk.prefixTape n w = t} := by ext ω; simp
  rw [heq, measure, Measure.prod_prod]
  simp [tape_prefix_law]

/-- Exact joint cylinder probabilities also exhibit setup/tape independence. -/
theorem setup_prefix_law (z : Vertex k) (n : ℕ) (t : LazyWalk.Tape n) :
    measure k {ω | ω.1 = z ∧ LazyWalk.prefixTape n ω.2 = t} =
      (N k : ℝ≥0∞)⁻¹ * (Fintype.card (LazyWalk.Tape n) : ℝ≥0∞)⁻¹ := by
  have heq : {ω : Outcome k | ω.1 = z ∧ LazyWalk.prefixTape n ω.2 = t} =
      {z} ×ˢ {w | LazyWalk.prefixTape n w = t} := by ext ω; simp
  rw [heq, measure, Measure.prod_prod]
  simp [tape_prefix_law]

def setups (ω : Outcome k) : ℕ → Vertex k := fun _ => ω.1

def increments (ω : Outcome k) : ℕ → ℕ → Fin 4 := fun _ => ω.2

/-- Embed any one-setup, one-stream policy in this concrete probability space.
Unused stream slots may alias stream zero because these policies never use them. -/
def algorithm (p : Policy (Vertex k)) : Randomized k (Outcome k) where
  policy := fun _ => p
  setups := setups k
  increments := increments k

theorem algorithm_lazyLaw (p : Policy (Vertex k)) :
    (algorithm k p).LazyLaw (measure k) := by
  intro i n t
  exact ⟨measurable_outcome_prefix k n t, outcome_prefix_law k n t⟩

theorem increments_iid : LazyWalk.IID (measure k) (fun ω => increments k ω 0) := by
  intro n t
  exact ⟨measurable_outcome_prefix k n t, outcome_prefix_law k n t⟩

end RandomWalkSearch.Cycle.Canonical
