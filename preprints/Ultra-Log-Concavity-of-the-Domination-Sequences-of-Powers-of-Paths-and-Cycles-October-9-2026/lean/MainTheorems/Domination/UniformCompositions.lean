import MainTheorems.Domination.PairConditioning

namespace ResearchMain.Domination

open Classical

noncomputable def uniformCount (r m : ℕ) (N : ℤ) : ℤ :=
  compositionCountZ (fun _ : Fin r => m) N

theorem lastCases_const (r m : ℕ) :
    Fin.lastCases m (fun _ : Fin r => m) = (fun _ : Fin (r + 1) => m) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem twoBounds_const (m : ℕ) : twoBounds m m = (fun _ : Fin 2 => m) := by
  funext i
  fin_cases i <;> rfl

theorem uniformPair_denominator (r m : ℕ) (N : ℤ) :
    pairDenominator m m (fun _ : Fin r => m) N = uniformCount (r + 2) m N := by
  rw [pairDenominator_eq, twoBounds_const]
  have hb : Fin.addCases (fun _ : Fin 2 => m) (fun _ : Fin r => m) =
      (fun _ : Fin (2 + r) => m) := by
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  rw [hb]
  change uniformCount (2 + r) m N = uniformCount (r + 2) m N
  congr 1
  omega

noncomputable def uniformMergeCount (r m : ℕ) (N : ℤ) : ℤ :=
  pairNumerator m m (fun _ : Fin r => m) N m

theorem uniformMergeCount_moment (r m : ℕ) (hm : 1 ≤ m) (N : ℤ) :
    uniformMergeCount r m N =
      compositionMoment (fun _ : Fin (r + 1) => m) N (Fin.last r) - uniformCount (r + 1) m N := by
  rw [uniformMergeCount, pairNumerator_low m m hm le_rfl, lastCases_const]
  rfl

theorem uniformMergeCount_identity (r m : ℕ) (hm : 1 ≤ m) (N : ℤ) :
    ((r + 1 : ℕ) : ℤ) * uniformMergeCount r m N =
      (N - (r + 1 : ℕ)) * uniformCount (r + 1) m N := by
  rw [uniformMergeCount_moment r m hm N]
  have h := uniform_compositionMoment m N (Fin.last r)
  change ((r + 1 : ℕ) : ℤ) * compositionMoment (fun _ : Fin (r + 1) => m) N (Fin.last r) =
    N * uniformCount (r + 1) m N at h
  nlinarith only [h]

theorem uniformMergeCount_cross (r m : ℕ) (hm : 1 ≤ m) (N : ℤ) :
    uniformMergeCount r m N * uniformCount (r + 3) m N ≤
      uniformMergeCount (r + 1) m N * uniformCount (r + 2) m N := by
  have h := pairNumerator_append_cross m m (fun _ : Fin r => m) (fun _ => hm) m N m
  rw [lastCases_const, uniformPair_denominator, uniformPair_denominator] at h
  change uniformMergeCount r m N * uniformCount (r + 1 + 2) m N ≤
    uniformMergeCount (r + 1) m N * uniformCount (r + 2) m N at h
  simpa only [Nat.add_assoc] using h

theorem uniformCount_weighted_lc (r m : ℕ) (hm : 1 ≤ m) (N : ℤ) :
    (N - (r + 1 : ℕ)) * ((r + 2 : ℕ) : ℤ) * uniformCount (r + 1) m N *
        uniformCount (r + 3) m N ≤
      (N - (r + 2 : ℕ)) * ((r + 1 : ℕ) : ℤ) * uniformCount (r + 2) m N ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (uniformMergeCount_cross r m hm N)
    (show (0 : ℤ) ≤ ((r + 1 : ℕ) : ℤ) * ((r + 2 : ℕ) : ℤ) by positivity)
  have hfirst := uniformMergeCount_identity r m hm N
  have hnext := uniformMergeCount_identity (r + 1) m hm N
  have hidx : r + 1 + 1 = r + 2 := by omega
  rw [hidx] at hnext
  calc
    (N - (r + 1 : ℕ)) * ((r + 2 : ℕ) : ℤ) * uniformCount (r + 1) m N *
        uniformCount (r + 3) m N =
      (((r + 1 : ℕ) : ℤ) * uniformMergeCount r m N) *
        ((r + 2 : ℕ) : ℤ) * uniformCount (r + 3) m N := by rw [hfirst]; ring
    _ ≤ (((r + 2 : ℕ) : ℤ) * uniformMergeCount (r + 1) m N) *
        ((r + 1 : ℕ) : ℤ) * uniformCount (r + 2) m N := by nlinarith only [h]
    _ = (N - (r + 2 : ℕ)) * ((r + 1 : ℕ) : ℤ) * uniformCount (r + 2) m N ^ 2 := by
      rw [hnext]
      ring

end ResearchMain.Domination
