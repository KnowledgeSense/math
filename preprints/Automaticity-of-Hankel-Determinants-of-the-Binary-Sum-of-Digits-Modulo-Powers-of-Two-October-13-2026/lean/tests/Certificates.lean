import HankelAutomaticity

open HankelAutomaticity

example (K : ℕ) (hK : 1 ≤ K) :
    IsTwoAutomatic (fun n : ℕ => (determinant (n+1) : ZMod (2^K))) :=
  binary_digit_sum_hankel_automaticity K hK

example (K : ℕ) (hK : 1 ≤ K) (n r : ℕ) :
    (hankelBinaryAutomaton K).eval (List.replicate r false++n.bits.reverse)=
      (determinant (n+1) : ZMod (2^K)) :=
  hankel_automaton_correct_with_leading_zeroes K hK n r

example (n : ℕ) : digitSum n=n.bits.count true := digitSum_eq_count_bits n

example : determinant 1=0 := determinant_one

example : (determinant 2 : ZMod 8)=7 := by
  rw [← hankel_automaton_correct 3 (by decide) 1]
  decide

example : (determinant 3 : ZMod 8)=2 := by
  rw [← hankel_automaton_correct 3 (by decide) 2]
  decide

example : (determinant 4 : ZMod 8)=5 := by
  rw [← hankel_automaton_correct 3 (by decide) 3]
  decide

example : (determinant 5 : ZMod 8)=0 := by
  rw [← hankel_automaton_correct 3 (by decide) 4]
  decide

example : (determinant 8 : ZMod 8)=5 := by
  rw [← hankel_automaton_correct 3 (by decide) 7]
  decide

example : (determinant 9 : ZMod 8)=4 := by
  rw [← hankel_automaton_correct 3 (by decide) 8]
  decide

example : (determinant 32 : ZMod 8)=5 := by
  rw [← hankel_automaton_correct 3 (by decide) 31]
  decide

example : (determinant 33 : ZMod 8)=4 := by
  rw [← hankel_automaton_correct 3 (by decide) 32]
  decide

example : (hankelBinaryAutomaton 1).eval [false,false,true,true]=1 := by decide
example : (hankelBinaryAutomaton 2).eval [false,true,true]=1 := by decide
