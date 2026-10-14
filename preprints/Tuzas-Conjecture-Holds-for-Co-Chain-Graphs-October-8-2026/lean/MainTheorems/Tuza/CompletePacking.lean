import MainTheorems.Tuza.CompleteEvenPacking
import MainTheorems.Tuza.CompleteExceptionalPacking
import Mathlib.Data.Nat.Factorial.Cast

namespace ResearchMain.Tuza

def completeLeave (n : ℕ) : ℕ :=
  if n % 6 = 1 ∨ n % 6 = 3 then 0
  else if n % 6 = 5 then 4
  else if n % 6 = 4 then n / 2 + 1
  else n / 2

def completeCount (n : ℕ) : ℕ := (n.choose 2 - completeLeave n) / 3

theorem exists_complete_packing_count (n : ℕ) :
    ∃ P : Finset (Finset (Fin n)), Packing (⊤ : SimpleGraph (Fin n)) P ∧
      3 * P.card + completeLeave n = n.choose 2 := by
  let m := n / 6
  have hn : n = 6 * m + n % 6 := by omega
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  · have h := complete_packing_zero_residue m
    have he : 6 * m = n := by omega
    rw [he] at h
    obtain ⟨P, hP, hc⟩ := h
    exact ⟨P, hP, by simpa [completeLeave, hr] using hc⟩
  · have h := complete_packing_one m
    have he : 6 * m + 1 = n := by omega
    rw [he] at h
    obtain ⟨P, hP, hc⟩ := h
    exact ⟨P, hP, by simpa [completeLeave, hr] using hc⟩
  · have h := complete_packing_two_residue m
    have he : 6 * m + 2 = n := by omega
    rw [he] at h
    obtain ⟨P, hP, hc⟩ := h
    exact ⟨P, hP, by simpa [completeLeave, hr] using hc⟩
  · have h := complete_packing_three m
    have he : 6 * m + 3 = n := by omega
    rw [he] at h
    obtain ⟨P, hP, hc⟩ := h
    exact ⟨P, hP, by simpa [completeLeave, hr] using hc⟩
  · have h := complete_packing_four_residue m
    have he : 6 * m + 4 = n := by omega
    rw [he] at h
    obtain ⟨P, hP, hc⟩ := h
    exact ⟨P, hP, by simpa [completeLeave, hr, Nat.add_assoc] using hc⟩
  · have h := complete_packing_five_residue m
    have he : 6 * m + 5 = n := by omega
    rw [he] at h
    obtain ⟨P, hP, hc⟩ := h
    exact ⟨P, hP, by simpa [completeLeave, hr] using hc⟩

theorem complete_count_equation (n : ℕ) : 3 * completeCount n + completeLeave n = n.choose 2 := by
  obtain ⟨P, _, hP⟩ := exists_complete_packing_count n
  unfold completeCount
  omega

theorem complete_packing (n : ℕ) :
    ∃ P : Finset (Finset (Fin n)), Packing (⊤ : SimpleGraph (Fin n)) P ∧ P.card = completeCount n := by
  obtain ⟨P, hP, hc⟩ := exists_complete_packing_count n
  exact ⟨P, hP, by have he := complete_count_equation n; omega⟩

theorem complete_leave_bound (n : ℕ) : 2 * completeLeave n ≤ n + 3 := by
  unfold completeLeave
  split_ifs <;> omega

theorem choose_two_integer (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  have hc := congrArg (fun k : ℕ => (k : ℤ)) h
  simp only [Nat.cast_descFactorial_two, Nat.factorial_two, Nat.cast_mul, Nat.cast_ofNat] at hc
  exact hc.symm

theorem complete_count_bound (n : ℕ) :
    (n : ℤ) * ((n : ℤ) - 2) - 3 ≤ 6 * (completeCount n : ℤ) := by
  have hc := complete_count_equation n
  have hl := complete_leave_bound n
  have hc' : 3 * (completeCount n : ℤ) + (completeLeave n : ℤ) = (n.choose 2 : ℤ) := by exact_mod_cast hc
  have hl' : 2 * (completeLeave n : ℤ) ≤ (n : ℤ) + 3 := by exact_mod_cast hl
  have hchoose := choose_two_integer n
  nlinarith

end ResearchMain.Tuza
