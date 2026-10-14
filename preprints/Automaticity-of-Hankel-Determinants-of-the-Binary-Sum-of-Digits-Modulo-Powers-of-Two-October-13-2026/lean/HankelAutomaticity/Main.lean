import HankelAutomaticity.DigitOrderConversion

noncomputable section
namespace HankelAutomaticity

/-- An ordinary deterministic finite automaton with output, reading binary
digits most significant first. The initial state ignores leading zeroes. -/
 structure BinaryAutomaton (A : Type) where
  State : Type
  finite_state : Finite State
  start : State
  step : State → Bool → State
  output : State → A
  zero_start : step start false=start

 def BinaryAutomaton.eval {A : Type} (M : BinaryAutomaton A) (w : List Bool) : A :=
  M.output (w.foldl M.step M.start)

 def IsTwoAutomatic {A : Type} (f : ℕ → A) : Prop :=
  ∃ M : BinaryAutomaton A, ∀ n : ℕ, M.eval n.bits.reverse=f n

 def hankelBinaryAutomaton (K : ℕ) : BinaryAutomaton (ZMod (2^K)) where
  State := MSBState K
  finite_state := inferInstance
  start := none
  step := msbStep
  output := msbOutput
  zero_start := rfl

 theorem hankel_automaton_correct (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    (hankelBinaryAutomaton K).eval n.bits.reverse=(determinant (n+1) : ZMod (2^K)) :=
  msb_machine_output K hK n

 theorem BinaryAutomaton.eval_leading_zeroes {A : Type} (M : BinaryAutomaton A)
    (r : ℕ) (w : List Bool) : M.eval (List.replicate r false++w)=M.eval w := by
  induction r with
  | zero => simp
  | succ r ih =>
    simpa only [List.replicate_succ, List.cons_append, BinaryAutomaton.eval,
      List.foldl_cons, M.zero_start] using ih

 theorem hankel_automaton_correct_with_leading_zeroes (K : ℕ) (hK : 1 ≤ K) (n r : ℕ) :
    (hankelBinaryAutomaton K).eval (List.replicate r false++n.bits.reverse)=
      (determinant (n+1) : ZMod (2^K)) := by
  rw [BinaryAutomaton.eval_leading_zeroes, hankel_automaton_correct K hK]

/-- For every positive power of two, the original binary digit-sum Hankel
determinants, indexed by `n+1`, form a 2-automatic sequence. -/
 theorem binary_digit_sum_hankel_automaticity (K : ℕ) (hK : 1 ≤ K) :
    IsTwoAutomatic (fun n : ℕ => (determinant (n+1) : ZMod (2^K))) :=
  ⟨hankelBinaryAutomaton K, hankel_automaton_correct K hK⟩

end HankelAutomaticity
