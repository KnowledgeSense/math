import HankelAutomaticity.FiniteState

noncomputable section
namespace HankelAutomaticity

 theorem suffix_answers_correct (K : ℕ) (hK : 1 ≤ K) (w : List Bool)
    (b o : Bool) (q : ZMod (2^K)) :
    suffixAnswersStep (suffixSummary K w) o q=polynomialPair (twist o (b::w)) q := by
  rcases w with _ | ⟨c, _ | ⟨d, v⟩⟩
  · cases o <;> cases b <;> simp [suffixAnswersStep, suffixSummary, twist, complement, polynomialPair]
  · cases o <;> cases b <;> cases c <;>
      simp [suffixAnswersStep, suffixSummary, twist, complement, polynomialPair]
  · let w := c::d::v
    have hm : min w.length 2=2 := by simp [w]
    have hn : w≠[] := by simp [w]
    have hv := (cast_binaryValue_twist (R:=ZMod (2^K)) o w).symm
    have hp := (parity_twist o w hn).symm
    have hs := (sign_reduce (R:=ZMod (2^K)) (binaryValue (twist o w))).symm
    have h1 := (odd_base_reduce_power K hK q (2*binaryValue (twist o w)+1)).symm
    have h0 := (odd_base_reduce_power K hK q (2*binaryValue (twist o w))).symm
    have hM := (odd_base_reduce_power K hK q (2^w.length)).symm
    have hM' := (odd_base_reduce_power K hK q (2^w.length-1)).symm
    have hpos : (1 : ℕ) ≤ 2^w.length := by
      have h : (0 : ℕ)<2^w.length := by positivity
      omega
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_sub hpos, Nat.cast_one] at h1 h0 hM hM'
    change suffixAnswersStep (suffixSummary K w) o q=polynomialPair (twist o (b::w)) q
    rw [show twist o (b::w)=(Bool.xor b o)::(Bool.xor c o)::(Bool.xor d o)::twist o v by
      simp [w]]
    rw [polynomialPair]
    simp only [suffixAnswersStep, suffixSummary, hm, show ¬(2 : ℕ)=0 by decide,
      show ¬(2 : ℕ)=1 by decide, ↓reduceIte]
    change (if Bool.xor c o then _ else _)=_
    rw [hv, hp, hs, h1, h0, hM, hM']
    have htw : (Bool.xor c o)::(Bool.xor d o)::twist o v=twist o w := by simp [w]
    rw [htw, twist_length, complement_twist]

 theorem suffix_step_summary (K : ℕ) (hK : 1 ≤ K) (w : List Bool) (b : Bool) :
    suffixStep (suffixSummary K w) b=suffixSummary K (b::w) := by
  apply SuffixState.ext
  · cases b <;> simp [suffixStep, suffixSummary, binaryValue]
  · simp [suffixStep, suffixSummary, pow_succ, mul_comm]
  · apply Fin.ext
    simp only [suffixStep, suffixSummary, Fin.val_mk, List.length_cons]
    omega
  · rfl
  · cases w with
    | nil => cases b <;> simp [suffixStep, suffixSummary, binaryValue]
    | cons c w =>
      cases b <;> simp [suffixStep, suffixSummary, binaryValue,
        show (2 : ZMod 2)=0 by decide]
  · funext o q
    exact suffix_answers_correct K hK w b o q

 theorem suffix_run_summary (K : ℕ) (hK : 1 ≤ K) (w : List Bool) :
    w.foldl suffixStep (suffixStart K)=suffixSummary K w.reverse := by
  have h (v w : List Bool) : w.foldl suffixStep (suffixSummary K v)=suffixSummary K (w.reverse++v) := by
    induction w generalizing v with
    | nil => simp
    | cons b w ih =>
      simp only [List.foldl_cons, suffix_step_summary K hK, ih, List.reverse_cons]
      simp
  simpa [suffixStart] using h [] w

end HankelAutomaticity
