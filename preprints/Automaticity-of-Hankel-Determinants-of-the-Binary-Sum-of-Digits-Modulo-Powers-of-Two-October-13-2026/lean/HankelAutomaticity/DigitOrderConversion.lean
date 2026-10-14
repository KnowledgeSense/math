import HankelAutomaticity.FiniteStateCorrectness
import HankelAutomaticity.OriginalDeterminantBridge

noncomputable section
namespace HankelAutomaticity

 def suffixOutput {K : ℕ} (s : SuffixState K) : ZMod (2^K) :=
  if s.head then (s.answers false 1).1 else 0

 theorem bits_reverse_starts_true (n : ℕ) (hn : n≠0) :
    ∃ v : List Bool, n.bits.reverse=true::v := by
  induction n using Nat.binaryRec with
  | zero => exact (hn rfl).elim
  | bit b n ih =>
    by_cases h : n=0
    · subst n
      cases b
      · simp [Nat.bit] at hn
      · exact ⟨[], by simp [Nat.bit]⟩
    · obtain ⟨v, hv⟩ := ih h
      refine ⟨v++[b], ?_⟩
      rw [Nat.bits_append_bit n b (fun h' => (h h').elim), List.reverse_cons, hv]
      rfl

 theorem determinant_one : determinant 1=0 := by
  unfold determinant
  erw [Matrix.det_unique]
  rfl

 theorem suffix_machine_output (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    suffixOutput (n.bits.foldl suffixStep (suffixStart K))=(determinant (n+1) : ZMod (2^K)) := by
  rw [suffix_run_summary K hK]
  by_cases hn : n=0
  · subst n
    simp [suffixOutput, suffixSummary, determinant_one]
  · obtain ⟨v, hv⟩ := bits_reverse_starts_true n hn
    have hnval : binaryValue (true::v)=n := by rw [← hv, binaryValue_reverse_bits]
    have hd := determinant_eq_polynomialPair v
    rw [hnval] at hd
    rw [hv]
    simp only [suffixOutput, suffixSummary, List.headD_cons, ↓reduceIte, twist_false]
    have hm := polynomialPair_map (Int.castRingHom (ZMod (2^K))) (true::v) 1
    simp only [map_one] at hm
    rw [hm, hd]
    rfl

/-- The MSB machine stores a finite state transformation. Its first state
ignores leading zeroes, including arbitrarily many zeroes before zero. -/
 abbrev MSBState (K : ℕ) := Option (SuffixState K → SuffixState K)

 def msbStep {K : ℕ} : MSBState K → Bool → MSBState K
  | none, false => none
  | none, true => some (fun s => suffixStep s true)
  | some f, b => some (fun s => f (suffixStep s b))

 def msbOutput {K : ℕ} : MSBState K → ZMod (2^K)
  | none => 0
  | some f => suffixOutput (f (suffixStart K))

 theorem msb_fold_some {K : ℕ} (w : List Bool) (f : SuffixState K → SuffixState K) :
    w.foldl msbStep (some f)=some (fun s => f (w.reverse.foldl suffixStep s)) := by
  induction w generalizing f with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons, msbStep, ih, List.reverse_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

 theorem msb_output_true {K : ℕ} (v : List Bool) :
    msbOutput ((true::v).foldl msbStep (none : MSBState K))=
      suffixOutput ((true::v).reverse.foldl suffixStep (suffixStart K)) := by
  simp only [List.foldl_cons, msbStep, msb_fold_some, msbOutput,
    List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

 theorem msb_machine_output (K : ℕ) (hK : 1 ≤ K) (n : ℕ) :
    msbOutput (n.bits.reverse.foldl msbStep (none : MSBState K))=
      (determinant (n+1) : ZMod (2^K)) := by
  by_cases hn : n=0
  · subst n
    simp [msbOutput, determinant_one]
  · obtain ⟨v, hv⟩ := bits_reverse_starts_true n hn
    rw [hv, msb_output_true, ← hv, List.reverse_reverse]
    exact suffix_machine_output K hK n

end HankelAutomaticity
