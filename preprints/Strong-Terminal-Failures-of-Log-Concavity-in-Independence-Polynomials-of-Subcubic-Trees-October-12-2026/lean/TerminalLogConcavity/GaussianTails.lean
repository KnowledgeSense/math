import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Dist

namespace TerminalLogConcavity
open scoped BigOperators

theorem geometric_initial_identity (t : ℝ) (n : ℕ) :
    (1 - t) * (∑ i ∈ Finset.range n, t ^ (i + 1)) = t * (1 - t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith

theorem geometric_initial_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, t ^ (i + 1)) ≤ t / (1 - t) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - t)).mpr
  have h := geometric_initial_identity t n
  have hp : 0 ≤ t ^ n := pow_nonneg ht n
  nlinarith

theorem gaussian_initial_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2) (n : ℕ) :
    (∑ i ∈ Finset.range n, t ^ ((i + 1) ^ 2)) ≤ 2 * t := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, t ^ (i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_of_le_one ht (by linarith) (by nlinarith : i + 1 ≤ (i + 1) ^ 2)
    _ ≤ t / (1 - t) := geometric_initial_bound ht (by linarith) n
    _ ≤ 2 * t := (div_le_iff₀ (by linarith : 0 < 1 - t)).mpr (by nlinarith)

theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1 + f i)) ≤ Real.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add]
    apply mul_le_mul
    · simpa [add_comm] using Real.add_one_le_exp (f i)
    · exact ih (fun j hj => hf j (by simp [hj]))
    · exact Finset.prod_nonneg (fun j hj => by have := hf j (by simp [hj]); linarith)
    · positivity

theorem gaussian_prefactor_bound {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1 / 256) (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 + t ^ ((i + 1) ^ 2))) ≤ 3 / 2 := by
  have hsum := gaussian_initial_bound ht (by linarith : t ≤ 1 / 2) n
  have he : Real.exp (2 * t) ≤ 3 / 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ 2 * t) (by linarith)
    exact h.trans ((div_le_iff₀ (by linarith : 0 < 1 - 2 * t)).mpr (by linarith))
  exact (prod_one_add_le_exp_sum _ _ (fun i _ => by positivity)).trans
    ((Real.exp_le_exp.mpr hsum).trans he)

theorem finite_positive_gaussian_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (s : Finset ℕ) (hs : ∀ i ∈ s, 1 ≤ i) :
    (∑ i ∈ s, t ^ (i ^ 2)) ≤ 2 * t := by
  calc
    _ ≤ ∑ k ∈ Finset.range (s.sup id + 1), t ^ ((k + 1) ^ 2) := by
      apply Finset.sum_le_sum_of_injOn (fun i => i - 1)
      · intro i hi j hj he
        have := hs i hi
        have := hs j hj
        change i - 1 = j - 1 at he
        omega
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        have hmax : i ≤ s.sup id := Finset.le_sup (f := id) hi
        exact Finset.mem_range.mpr (by omega)
      · intro i hi
        have he : i - 1 + 1 = i := by have := hs i hi; omega
        rw [he]
      · intro i _ _
        positivity
    _ ≤ 2 * t := gaussian_initial_bound ht ht1 _

theorem finite_gaussian_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (s : Finset ℕ) : (∑ i ∈ s, t ^ (i ^ 2)) ≤ 1 + 2 * t := by
  by_cases hz : 0 ∈ s
  · have h := finite_positive_gaussian_bound ht ht1 (s.erase 0) (by
      intro i hi
      have := (Finset.mem_erase.mp hi).1
      omega)
    have he := Finset.sum_erase_add s (fun i => t ^ (i ^ 2)) hz
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_zero] at he
    linarith
  · have h := finite_positive_gaussian_bound ht ht1 s (by
      intro i hi
      have : i ≠ 0 := by intro he; subst i; exact hz hi
      omega)
    linarith

theorem finite_shifted_gaussian_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (s : Finset ℕ) (u : ℕ) :
    (∑ i ∈ s, t ^ ((Nat.dist i u) ^ 2)) ≤ 1 + 4 * t := by
  let L := s.filter (fun i => i ≤ u)
  let R := s.filter (fun i => ¬ i ≤ u)
  have hl : (∑ i ∈ L, t ^ ((Nat.dist i u) ^ 2)) ≤ 1 + 2 * t := by
    have he : (∑ j ∈ L.image (fun i => u - i), t ^ (j ^ 2)) =
        ∑ i ∈ L, t ^ ((Nat.dist i u) ^ 2) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.dist_eq_sub_of_le (Finset.mem_filter.mp hi).2]
      · intro i hi j hj hij
        have := (Finset.mem_filter.mp hi).2
        have := (Finset.mem_filter.mp hj).2
        change u - i = u - j at hij
        omega
    rw [← he]
    exact finite_gaussian_bound ht ht1 _
  have hr : (∑ i ∈ R, t ^ ((Nat.dist i u) ^ 2)) ≤ 2 * t := by
    have he : (∑ j ∈ R.image (fun i => i - u), t ^ (j ^ 2)) =
        ∑ i ∈ R, t ^ ((Nat.dist i u) ^ 2) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.dist_eq_sub_of_le_right (by have := (Finset.mem_filter.mp hi).2; omega)]
      · intro i hi j hj hij
        have := (Finset.mem_filter.mp hi).2
        have := (Finset.mem_filter.mp hj).2
        change i - u = j - u at hij
        omega
    rw [← he]
    apply finite_positive_gaussian_bound ht ht1
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have := (Finset.mem_filter.mp hi).2
    omega
  have he := Finset.sum_filter_add_sum_filter_not s (fun i => i ≤ u)
    (fun i => t ^ ((Nat.dist i u) ^ 2))
  change (∑ i ∈ L, t ^ ((Nat.dist i u) ^ 2)) +
    (∑ i ∈ R, t ^ ((Nat.dist i u) ^ 2)) = _ at he
  linarith

end TerminalLogConcavity
