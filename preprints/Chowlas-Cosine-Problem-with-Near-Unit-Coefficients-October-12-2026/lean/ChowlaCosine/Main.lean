import ChowlaCosine.TranslationBound
import ChowlaCosine.Constants
import ChowlaCosine.CosineBridge
import ChowlaCosine.WeightedRoth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The release's main theorem, assembled from the actual support and analytic estimates. -/
namespace ChowlaCosine

open MeasureTheory AddCircle
open scoped BigOperators

/-- Summing the actual single-translation inequality preserves all support cardinalities. -/
theorem sum_translation_estimates {A : Finset ℤ} {K : ℝ}
    (h : ∀ t ∈ A,
      (5.27*(0.99 : ℝ)^4-4.86*(1.01 : ℝ)^4)*(B A t).card ≤
        12.86*((1.01 : ℝ)^2/100)^2*(C A t).card + 5408*K^8) :
    (5.27*(0.99 : ℝ)^4-4.86*(1.01 : ℝ)^4)*(Btot A : ℝ) ≤
      12.86*((1.01 : ℝ)^2/100)^2*(Ctot A : ℝ) + 5408*(A.card : ℝ)*K^8 := by
  simp only [Btot, Ctot, Nat.cast_sum, Finset.mul_sum]
  calc
    _ ≤ ∑ t ∈ A, (12.86*((1.01 : ℝ)^2/100)^2*(C A t).card + 5408*K^8) :=
      Finset.sum_le_sum h
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The two-size-case argument, before instantiating the proved translation estimate. -/
theorem symmetric_bound_from_translation_estimates
    {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01)
    (hlower : ∀ x, -K ≤ (polynomial A s x).re)
    (hsingle : ∀ t ∈ A,
      (5.27*(0.99 : ℝ)^4-4.86*(1.01 : ℝ)^4)*(B A t).card ≤
        12.86*((1.01 : ℝ)^2/100)^2*(C A t).card + 5408*K^8) :
    (A.card : ℝ) ≤ 100000000*K^9 := by
  obtain ⟨a, ha⟩ := hne
  have hKa := polynomial_coefficient_le h0 hA hs hlower ha
  have hK : (0.99 : ℝ) ≤ K := by
    have hsa := (hcoeff a ha).1
    have has := le_abs_self (s a)
    linarith
  by_cases hlarge : 3*K^2 ≤ (A.card : ℝ)
  · have hsum := sum_translation_estimates hsingle
    have hC : (Ctot A : ℝ) ≤ 2*(Btot A : ℝ) := by
      exact_mod_cast Ctot_le_two_Btot (fun m hm => (hA m).2 hm) h0
    have hupper := summed_error_absorption (Btot A) (Ctot A) A.card K
      (by positivity) hC hsum
    have hlowerB := roth_Btot_lower_bound ⟨a, ha⟩ h0 hA hs (by
      simpa only [show (99/100 : ℝ) = 0.99 by norm_num,
        show (101/100 : ℝ) = 1.01 by norm_num] using hcoeff)
      hlower hlarge
    apply large_support_bound (A.card : ℝ) K (Btot A) _ _ hlowerB hupper
    · exact_mod_cast Finset.card_pos.mpr (show A.Nonempty from ⟨a, ha⟩)
    · linarith
  · exact small_support_bound (A.card : ℝ) K hK (lt_of_not_ge hlarge)

/-- Taking the ninth root of the numeric cosine bound, including zero. -/
theorem ninth_root_le_twenty {N K : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K)
    (h : N ≤ (20 : ℝ)^9*K^9) : N^(1/9 : ℝ) ≤ 20*K := by
  have hroot : (N^(1/9 : ℝ))^9 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
    norm_num
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hN _) (by positivity : 0 ≤ 20*K)
    (by norm_num : (9 : ℕ) ≠ 0)).mp
  rw [hroot, mul_pow]
  exact h

/-- The exact real cosine conclusion obtained from a bound for its symmetric support. -/
theorem cosine_bound_of_symmetric_estimate {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01)
    (hsym : ∀ K : ℝ,
      (∀ z : Circle, -K ≤ (polynomial (symmetricSupport a) (symmetricWeight a s) z).re) →
      ((symmetricSupport a).card : ℝ) ≤ 100000000*K^9) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1,
      cosineSum a s x₀ ≤ -(N : ℝ)^(1/9 : ℝ)/20 ∧
      (∀ x : ℝ, cosineSum a s x₀ ≤ cosineSum a s x) := by
  obtain ⟨x₀, hx₀, K, hKeq, hlower, hmin⟩ := cosine_minimum_bridge s hinj hpos
  have hbound := hsym K hlower
  rw [symmetricSupport_card hinj hpos] at hbound
  have hboundN : 2*(N : ℝ) ≤ 100000000*K^9 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound
  let j : Fin N := ⟨0, by omega⟩
  have hj : a j ∈ symmetricSupport a :=
    (mem_symmetricSupport a _).2 (Or.inl ⟨j, rfl⟩)
  have hKbound := polynomial_coefficient_le (zero_not_mem_symmetricSupport hpos)
    (symmetricSupport_neg a) (fun m hm => symmetricWeight_neg a s m) hlower hj
  rw [symmetricWeight_at_positive s hinj hpos] at hKbound
  have hKpos : 0 < K := by
    have hsj := (hcoeff j).1
    have habs := le_abs_self (s j)
    linarith
  have heq : K = 2*(-cosineSum a s x₀) := by rw [hKeq]; ring
  have hcosK : 0 ≤ -cosineSum a s x₀ := by linarith
  have hnum : 2*(N : ℝ) ≤ 100000000*(2*(-cosineSum a s x₀))^9 := by
    rw [← heq]
    exact hboundN
  have hpower := cosine_power_bound (N : ℝ) (-cosineSum a s x₀) hcosK hnum
  have hroot := ninth_root_le_twenty (by positivity : 0 ≤ (N : ℝ)) hcosK hpower
  refine ⟨x₀, hx₀, ?_, hmin⟩
  linarith

/-- The symmetric main theorem of the 12 October 2026 release. -/
theorem symmetric_chowla_bound {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01)
    (hlower : ∀ x, -K ≤ (polynomial A s x).re) :
    (A.card : ℝ) ≤ 100000000*K^9 := by
  apply symmetric_bound_from_translation_estimates hne h0 hA hs hcoeff hlower
  intro t ht
  exact single_translation_bound t hne h0 hA hs hcoeff hlower

/-- The symmetric main theorem evaluated at an attained circle minimum. -/
theorem symmetric_chowla_minimum_circle {A : Finset ℤ} {s : ℤ → ℝ}
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x₀ : Circle,
      (∀ x : Circle, (polynomial A s x₀).re ≤ (polynomial A s x).re) ∧
      (A.card : ℝ) ≤ 100000000*(-(polynomial A s x₀).re)^9 := by
  obtain ⟨x₀, hmin⟩ := circle_minimum_exists
    (Complex.continuous_re.comp (polynomial A s).continuous)
  refine ⟨x₀, hmin, ?_⟩
  apply symmetric_chowla_bound hne h0 hA hs hcoeff
  intro x
  simpa only [neg_neg, Function.comp_apply] using hmin x

/-- The symmetric release statement at an attained minimum over the original real domain. -/
theorem symmetric_chowla_minimum {A : Finset ℤ} {s : ℤ → ℝ}
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1,
      (∀ x : ℝ, (polynomial A s (x₀ : Circle)).re ≤ (polynomial A s (x : Circle)).re) ∧
      (A.card : ℝ) ≤ 100000000*(-(polynomial A s (x₀ : Circle)).re)^9 := by
  obtain ⟨x₀, hx₀, hmin⟩ := polynomial_minimum_exists A s
  refine ⟨x₀, hx₀, fun x => hmin (x : Circle), ?_⟩
  apply symmetric_chowla_bound hne h0 hA hs hcoeff
  intro x
  simpa only [neg_neg, Function.comp_apply] using hmin x

/-- The original main theorem, at an attained global minimum in the first real period. -/
theorem chowla_cosine_minimum {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x₀ ∈ Set.Ico (0 : ℝ) 1,
      cosineSum a s x₀ ≤ -(N : ℝ)^(1/9 : ℝ)/20 ∧
      (∀ x : ℝ, cosineSum a s x₀ ≤ cosineSum a s x) := by
  apply cosine_bound_of_symmetric_estimate s hN hinj hpos hcoeff
  intro K hlower
  exact symmetric_chowla_bound (symmetricSupport_nonempty a (by omega))
    (zero_not_mem_symmetricSupport hpos) (symmetricSupport_neg a)
    (fun m hm => symmetricWeight_neg a s m)
    (symmetricWeight_mem_Icc hinj hpos hcoeff) hlower

/-- The release's original-domain existence statement for arbitrary positive integer frequencies. -/
theorem chowla_cosine_main {N : ℕ} {a : Fin N → ℤ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x : ℝ, (∑ j, s j * Real.cos (2*Real.pi*(a j : ℝ)*x)) ≤
      -(N : ℝ)^(1/9 : ℝ)/20 := by
  obtain ⟨x, hx, hbound, hmin⟩ := chowla_cosine_minimum s hN hinj hpos hcoeff
  exact ⟨x, hbound⟩

/-- An equivalent natural-frequency interface, with arbitrary distinct positive naturals. -/
theorem chowla_cosine_main_nat {N : ℕ} {a : Fin N → ℕ} (s : Fin N → ℝ)
    (hN : 1 ≤ N) (hinj : Function.Injective a) (hpos : ∀ j, 0 < a j)
    (hcoeff : ∀ j, s j ∈ Set.Icc (0.99 : ℝ) 1.01) :
    ∃ x : ℝ, (∑ j, s j * Real.cos (2*Real.pi*(a j : ℝ)*x)) ≤
      -(N : ℝ)^(1/9 : ℝ)/20 := by
  have hi : Function.Injective (fun j => (a j : ℤ)) := by
    intro i j hij
    apply hinj
    change (a i : ℤ) = (a j : ℤ) at hij
    exact_mod_cast hij
  have hp : ∀ j, (0 : ℤ) < (a j : ℤ) := by
    intro j
    exact_mod_cast hpos j
  obtain ⟨x, hx⟩ := chowla_cosine_main s hN hi hp hcoeff
  refine ⟨x, ?_⟩
  simpa only [Int.cast_natCast] using hx

end ChowlaCosine
