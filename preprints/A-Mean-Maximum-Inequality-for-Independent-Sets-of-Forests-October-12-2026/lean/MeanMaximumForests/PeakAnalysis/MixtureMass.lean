import MeanMaximumForests.PeakAnalysis.BipartiteMixture
import MeanMaximumForests.PeakAnalysis.BinomialInteger

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem binomialIntegerMass_eq_expectation (n : ℕ) (z : ℝ) (hz : 0 < z) (k : ℤ) :
    binomialIntegerMass n z k = (binomialSizeLaw n z hz).expectation
      (fun j => if (j.val : ℤ) = k then 1 else 0) := by
  by_cases hk0 : 0 ≤ k
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rw [binomialIntegerMass_natCast]
    by_cases hq : q ≤ n
    · let j : Fin (n + 1) := ⟨q, by omega⟩
      unfold FiniteLaw.expectation
      rw [sum_eq_single j]
      · simp [j, binomialSizeLaw]
      · intro i _ hij
        have hne : (i.val : ℤ) ≠ (q : ℤ) := by
          intro he
          apply hij
          apply Fin.ext
          exact Int.ofNat_inj.mp he
        simp only [hne, ↓reduceIte, mul_zero]
      · simp
    · rw [binomialSizeMass_eq_zero z (by omega)]
      unfold FiniteLaw.expectation
      symm
      apply sum_eq_zero
      intro i _
      have hne : (i.val : ℤ) ≠ (q : ℤ) := by have := i.isLt; omega
      simp only [hne, ↓reduceIte, mul_zero]
  · rw [binomialIntegerMass_negative n z (by omega)]
    unfold FiniteLaw.expectation
    symm
    apply sum_eq_zero
    intro i _
    have hne : (i.val : ℤ) ≠ k := by omega
    simp only [hne, ↓reduceIte, mul_zero]

theorem binomialIntegerMass_le_one (n : ℕ) (z : ℝ) (hz : 0 < z) (k : ℤ) :
    binomialIntegerMass n z k ≤ 1 := by
  rw [binomialIntegerMass_eq_expectation n z hz]
  calc
    _ ≤ (binomialSizeLaw n z hz).expectation (fun _ => 1) := by
      apply FiniteLaw.expectation_mono
      intro j
      split_ifs <;> norm_num
    _ = 1 := FiniteLaw.expectation_const _ _

noncomputable def hardCoreIntegerMass (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) (k : ℤ) : ℝ :=
  (hardCoreLaw G (fun _ => z) (fun _ => hz)).expectation (fun I => if (I.card : ℤ) = k then 1 else 0)

omit [DecidableEq V] in
theorem hardCoreIntegerMass_nonneg (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) (k : ℤ) :
    0 ≤ hardCoreIntegerMass G z hz k := by
  apply FiniteLaw.expectation_nonneg
  intro I
  split_ifs <;> norm_num

theorem bipartite_mass_mixture (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z : ℝ) (hz : 0 < z) (k : ℤ) :
    hardCoreIntegerMass G z hz k =
      (bipartiteMixLaw G L R hL hR hd hc z hz).expectation
        (fun r => binomialIntegerMass (availableIn G L r.val).card z (k - r.val.card)) := by
  unfold hardCoreIntegerMass
  rw [bipartite_cardinality_mixture G L R hL hR hd hc z hz (fun j => if (j : ℤ) = k then 1 else 0)]
  congr 1
  funext r
  rw [binomialIntegerMass_eq_expectation _ z hz]
  congr 1
  funext j
  have he : ((r.val.card + j.val : ℕ) : ℤ) = k ↔ (j.val : ℤ) = k - r.val.card := by
    push_cast
    omega
  simp only [he]

end MeanMaximumForests.PeakAnalysis
