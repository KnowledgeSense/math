import TerminalLogConcavity.WeightedPath

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def chainWeights (P d : ℕ[X]) (cs : List ℕ[X]) : List (ℕ[X] × ℕ[X]) :=
  (cs.map (fun c => (P, P + c))).intersperse (1,d)

noncomputable def chainModel (P d : ℕ[X]) (cs : List ℕ[X]) : ℕ[X] × ℕ[X] :=
  weightedPath (chainWeights P d cs)

@[simp] theorem chainModel_single (P d c : ℕ[X]) :
    chainModel P d [c] = (P + (P + c), P) := by
  simp [chainModel, chainWeights, weightedPath, weightedPathFrom]

theorem chainModel_cons_cons (P d c e : ℕ[X]) (cs : List ℕ[X]) :
    chainModel P d (c :: e :: cs) =
      (P * ((chainModel P d (e :: cs)).1 + d * (chainModel P d (e :: cs)).2) +
        (P + c) * (chainModel P d (e :: cs)).1,
       P * ((chainModel P d (e :: cs)).1 + d * (chainModel P d (e :: cs)).2)) := by
  simp [chainModel, chainWeights, weightedPath, weightedPathFrom]

private theorem coeffLE_zero (p : ℕ[X]) : CoeffLE 0 p := by intro n; simp
private theorem coeffLE_left_add (p q : ℕ[X]) : CoeffLE p (q + p) := by
  simpa [add_comm] using CoeffLE.le_add_right p q

/-- The all-site and all-coupler configurations give the two dominant terms. -/
theorem chainModel_two_phases (P d : ℕ[X]) (cs : List ℕ[X]) (hn : cs ≠ []) :
    CoeffLE (cs.prod + d ^ (cs.length - 1) * P ^ cs.length) (chainModel P d cs).1 ∧
    CoeffLE (d ^ (cs.length - 1) * P ^ cs.length) (chainModel P d cs).2 := by
  induction cs with
  | nil => contradiction
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [List.prod_cons, List.prod_nil, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.sub_self, pow_zero, one_mul, pow_one, mul_one, chainModel_single]
      constructor
      · simpa only [add_assoc, add_comm, add_left_comm] using CoeffLE.le_add_right (c + P) P
      · exact CoeffLE.refl _
    | cons e cs =>
      obtain ⟨ht,he⟩ := ih (by simp)
      have hp : CoeffLE (e :: cs).prod (chainModel P d (e :: cs)).1 :=
        (CoeffLE.le_add_right _ _).trans ht
      have hs : CoeffLE (c * (e :: cs).prod)
          ((P + c) * (chainModel P d (e :: cs)).1) :=
        (coeffLE_left_add c P).mul hp
      have hc : CoeffLE (P * (d * (d ^ ((e :: cs).length - 1) * P ^ (e :: cs).length)))
          (P * ((chainModel P d (e :: cs)).1 + d * (chainModel P d (e :: cs)).2)) :=
        (CoeffLE.refl P).mul (((CoeffLE.refl d).mul he).trans (coeffLE_left_add _ _))
      have hlen : (e :: cs).length - 1 + 1 = (e :: cs).length := by simp
      have heq : P * (d * (d ^ ((e :: cs).length - 1) * P ^ (e :: cs).length)) =
          d ^ ((c :: e :: cs).length - 1) * P ^ (c :: e :: cs).length := by
        simp only [List.length_cons, Nat.add_sub_cancel, pow_succ]
        ring
      rw [heq] at hc
      rw [chainModel_cons_cons]
      exact ⟨by simpa only [List.prod_cons, add_comm] using hs.add hc, hc⟩

end TerminalLogConcavity
