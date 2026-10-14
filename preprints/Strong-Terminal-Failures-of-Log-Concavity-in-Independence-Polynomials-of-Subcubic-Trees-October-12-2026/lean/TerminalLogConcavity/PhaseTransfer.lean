import TerminalLogConcavity.ChainModel

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

structure PhaseVector where
  zero : ℕ[X]
  one : ℕ[X]
  two : ℕ[X]

noncomputable def phaseVector (P : ℕ[X]) (z : ℕ) : ℕ → PhaseVector
  | 0 => ⟨P, P, 1⟩
  | n + 1 =>
    let v := phaseVector P z n
    let T := v.zero + v.one + C z * v.two
    ⟨P * (T + C (z ^ 2) * v.zero), P * T, C z * T⟩

noncomputable def interiorConstants (z n : ℕ) : List ℕ[X] :=
  List.replicate n (C (z ^ 2)) ++ [C z]

/-- Transfer vector for a chain with an interior left endpoint. -/
theorem phaseVector_interior (P : ℕ[X]) (z n : ℕ) :
    chainModel P (C (z ^ 2)) (interiorConstants z n) =
      ((phaseVector P z n).zero + (phaseVector P z n).one + C z * (phaseVector P z n).two,
       (phaseVector P z n).zero) := by
  induction n with
  | zero => simp [interiorConstants, phaseVector, add_assoc]
  | succ n ih =>
    have hn : interiorConstants z n ≠ [] := by simp [interiorConstants]
    obtain ⟨c,cs,hcs⟩ := List.exists_cons_of_ne_nil hn
    have hcons : interiorConstants z (n + 1) = C (z ^ 2) :: c :: cs := by
      simp [interiorConstants, List.replicate_succ, ← hcs]
    rw [hcons, chainModel_cons_cons, ← hcs, ih]
    simp only [phaseVector]
    congr 1 ; simp only [C_pow] ; ring

noncomputable def endpointConstants (z u n : ℕ) : List ℕ[X] :=
  C (u * z) :: interiorConstants z n

/-- The first-site constant is separated from the edge contributions. -/
theorem phaseVector_endpoint (P : ℕ[X]) (z u n : ℕ) :
    (chainModel P (C (z ^ 2)) (endpointConstants z u n)).1 =
      (phaseVector P z (n + 1)).zero + (phaseVector P z (n + 1)).one +
        C u * (phaseVector P z (n + 1)).two := by
  have hn : interiorConstants z n ≠ [] := by simp [interiorConstants]
  obtain ⟨c,cs,hcs⟩ := List.exists_cons_of_ne_nil hn
  unfold endpointConstants
  rw [hcs, chainModel_cons_cons, ← hcs, phaseVector_interior]
  simp only [phaseVector, C_mul]
  ring

end TerminalLogConcavity
