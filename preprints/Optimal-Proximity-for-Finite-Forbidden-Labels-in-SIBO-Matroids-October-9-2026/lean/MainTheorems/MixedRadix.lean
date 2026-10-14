import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ResearchMain.SIBO

def radixSize (qs : List ℕ) : ℕ := (qs.map (fun q => q + 1)).prod

def radixPrefix (qs : List ℕ) (t : ℕ) : ℕ := radixSize (qs.take t)

theorem radixSize_pos (qs : List ℕ) : 0 < radixSize qs := by
  induction qs with
  | nil => simp [radixSize]
  | cons q qs _ => simp [radixSize]

@[simp] theorem radixPrefix_zero (qs : List ℕ) : radixPrefix qs 0 = 1 := by
  simp [radixPrefix, radixSize]

@[simp] theorem radixPrefix_cons (q : ℕ) (qs : List ℕ) (t : ℕ) :
    radixPrefix (q :: qs) (t + 1) = (q + 1) * radixPrefix qs t := by
  simp [radixPrefix, radixSize]

theorem predecessor_mod_of_dvd {L N : ℕ} (hL : 0 < L) (hN : 0 < N) (hd : N ∣ L) :
    (L - 1) % N = N - 1 := by
  have hsum : ((L - 1) % N + 1) % N = 0 := by
    rw [Nat.mod_add_mod, Nat.sub_add_cancel hL, Nat.mod_eq_zero_of_dvd hd]
  have hdiv : N ∣ (L - 1) % N + 1 := Nat.dvd_of_mod_eq_zero hsum
  have hlo := Nat.le_of_dvd (Nat.succ_pos _) hdiv
  have hhi := Nat.mod_lt (L - 1) hN
  omega

theorem first_failed_radix {a q ell : ℕ} (ha : 0 < a)
    (hd : a ∣ ell + 1) (hn : ¬ a * (q + 1) ∣ ell + 1) :
    ∃ j < q, ell % (a * (q + 1)) = (j + 1) * a - 1 := by
  obtain ⟨v, hv⟩ := hd
  have hb : 0 < a * (q + 1) := Nat.mul_pos ha (Nat.succ_pos q)
  have hrem : (ell + 1) % (a * (q + 1)) = a * (v % (q + 1)) := by
    rw [hv, Nat.mul_mod_mul_left]
  have hnonzero : v % (q + 1) ≠ 0 := by
    intro hz
    apply hn
    apply Nat.dvd_of_mod_eq_zero
    rw [hrem, hz, Nat.mul_zero]
  let d := v % (q + 1)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hnonzero
  have hdlt : d < q + 1 := Nat.mod_lt _ (Nat.succ_pos q)
  refine ⟨d - 1, by omega, ?_⟩
  have hinc : (ell % (a * (q + 1)) + 1) % (a * (q + 1)) = a * d := by
    rw [Nat.mod_add_mod]
    exact hrem
  have hmlt := Nat.mod_lt ell hb
  have hnot : ell % (a * (q + 1)) + 1 ≠ a * (q + 1) := by
    intro heq
    rw [heq, Nat.mod_self] at hinc
    have : 0 < a * d := Nat.mul_pos ha hdpos
    omega
  have hh : ell % (a * (q + 1)) + 1 < a * (q + 1) := by omega
  rw [Nat.mod_eq_of_lt hh] at hinc
  have hdsub : d - 1 + 1 = d := by omega
  rw [hdsub]
  rw [Nat.mul_comm a d] at hinc
  omega

/-- A first failed divisibility test selects one forbidden residue. -/
theorem exists_forbidden_radix (qs : List ℕ) (a ell : ℕ) (ha : 0 < a)
    (hd : a ∣ ell + 1) (hn : ¬ a * radixSize qs ∣ ell + 1) :
    ∃ t : Fin qs.length, ∃ j < qs[t],
      ell % (a * radixPrefix qs (t.val + 1)) =
        (j + 1) * (a * radixPrefix qs t.val) - 1 := by
  induction qs generalizing a with
  | nil => simp [radixSize] at hn; exact (hn hd).elim
  | cons q qs ih =>
    by_cases hnext : a * (q + 1) ∣ ell + 1
    · have hrest : ¬ (a * (q + 1)) * radixSize qs ∣ ell + 1 := by
        simpa [radixSize, Nat.mul_assoc] using hn
      obtain ⟨t, j, hj, heq⟩ := ih (a * (q + 1)) (Nat.mul_pos ha (Nat.succ_pos q)) hnext hrest
      refine ⟨t.succ, j, ?_, ?_⟩
      · simpa using hj
      · simpa only [Fin.val_succ, radixPrefix_cons, Nat.mul_assoc] using heq
    · obtain ⟨j, hj, heq⟩ := first_failed_radix ha hd hnext
      refine ⟨⟨0, by simp⟩, j, hj, ?_⟩
      simpa using heq

end ResearchMain.SIBO
