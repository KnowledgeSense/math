import HardCoreActivityThreshold.PositiveThinning
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Polynomial moment identities for positive-coordinate revealing. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thinningMoment (μ : FiniteLaw (Finset V)) (θ : ℝ)
    (r : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ s, μ.mass s * thinningKernel θ s r * f s

noncomputable def insertSum (F : Finset V → ℝ) (r : Finset V) : ℝ :=
  ∑ v, if v ∉ r then F (insert v r) else 0

/-- Counting each subset once for each of its possible last-revealed vertices. -/
theorem sum_insertSum (F : Finset V → ℝ) :
    (∑ r, insertSum F r) = ∑ r, (r.card : ℝ) * F r := by
  have hb (v : V) : (∑ r : Finset V, if v ∉ r then F (insert v r) else 0) =
      ∑ r : Finset V, if v ∈ r then F r else 0 := by
    rw [← sum_filter, ← sum_filter]
    apply sum_bij (fun r _ => insert v r)
    · intro r hr
      simp
    · intro r hr t ht hrt
      have hr' : v ∉ r := (mem_filter.mp hr).2
      have ht' : v ∉ t := (mem_filter.mp ht).2
      have he := congrArg (fun s : Finset V => s.erase v) hrt
      simpa [hr', ht'] using he
    · intro r hr
      refine ⟨r.erase v, by simp, ?_⟩
      exact insert_erase ((mem_filter.mp hr).2)
    · intro r _
      rfl
  unfold insertSum
  rw [sum_comm]
  simp_rw [hb]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  simp

omit [Fintype V] in
theorem thinningKernel_insert {θ : ℝ} (hθ : 0 < θ) (s r : Finset V)
    {v : V} (hv : v ∉ r) :
    thinningKernel θ s (insert v r) =
      ((1 - θ) / θ) * thinningKernel θ s r * occupation v s := by
  rw [thinningKernel_field hθ, thinningKernel_field hθ, card_insert_of_notMem hv, pow_succ]
  simp only [insert_subset_iff, occupation]
  by_cases hrs : r ⊆ s <;> by_cases hvs : v ∈ s <;> simp [hrs, hvs]
  ring

theorem sum_unrevealed_occupation (s r : Finset V) :
    (∑ v, if v ∉ r then occupation v s else 0) = ((s \ r).card : ℝ) := by
  have he (v : V) : (if v ∉ r then occupation v s else 0) =
      if v ∈ s \ r then (1 : ℝ) else 0 := by
    simp only [occupation, mem_sdiff]
    by_cases hvs : v ∈ s <;> by_cases hvr : v ∈ r <;> simp [hvs, hvr]
  simp_rw [he]
  simp only [sum_boole, Nat.cast_inj]
  congr 1
  ext v
  simp

theorem insertSum_thinningKernel {θ : ℝ} (hθ : 0 < θ) (s r : Finset V) :
    insertSum (thinningKernel θ s) r =
      ((1 - θ) / θ) * thinningKernel θ s r * ((s \ r).card : ℝ) := by
  unfold insertSum
  calc
    _ = ∑ v, ((1 - θ) / θ) * thinningKernel θ s r *
        (if v ∉ r then occupation v s else 0) := by
      apply sum_congr rfl
      intro v _
      by_cases hv : v ∉ r
      · rw [ite_eq_left hv, ite_eq_left hv, thinningKernel_insert hθ s r hv]
      · rw [ite_eq_right hv, ite_eq_right hv, mul_zero]
    _ = _ := by rw [← mul_sum, sum_unrevealed_occupation]

private theorem hasDerivAt_pow_quotient {θ : ℝ} (hθ : θ ≠ 0) (n : ℕ) :
    HasDerivAt (fun x : ℝ => x ^ n) ((n : ℝ) / θ * θ ^ n) θ := by
  convert hasDerivAt_pow n θ using 1
  cases n with
  | zero => simp
  | succ n => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]; field_simp

/-- The derivative is a finite transport equation on revealed subsets. -/
theorem hasDerivAt_thinningKernel {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (s r : Finset V) :
    HasDerivAt (fun x => thinningKernel x s r)
      ((insertSum (thinningKernel θ s) r - (r.card : ℝ) * thinningKernel θ s r) /
        (1 - θ)) θ := by
  by_cases hrs : r ⊆ s
  · have hA := (hasDerivAt_pow_quotient (sub_pos.mpr hθ1).ne' r.card).comp θ
      ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_id θ))
    have hB := hasDerivAt_pow_quotient hθ.ne' (s \ r).card
    convert hA.mul hB using 1
    · funext x
      simp [thinningKernel, hrs]
    · rw [insertSum_thinningKernel hθ]
      simp only [thinningKernel, hrs, ite_true]
      simp only [Function.comp_apply]
      field_simp [hθ.ne', (sub_pos.mpr hθ1).ne']
      ring
  · have he : (fun x => thinningKernel x s r) = fun _ => (0 : ℝ) := by
      funext x
      simp [thinningKernel, hrs]
    rw [he, insertSum_thinningKernel hθ]
    simpa only [thinningKernel, hrs, ite_false, mul_zero, zero_mul, sub_zero, zero_div] using
      (hasDerivAt_const θ (0 : ℝ))

theorem hasDerivAt_thinningMoment (μ : FiniteLaw (Finset V))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (r : Finset V) (f : Finset V → ℝ) :
    HasDerivAt (fun x => thinningMoment μ x r f)
      ((insertSum (fun r => thinningMoment μ θ r f) r -
        (r.card : ℝ) * thinningMoment μ θ r f) / (1 - θ)) θ := by
  have hUp : insertSum (fun q => thinningMoment μ θ q f) r =
      ∑ s, μ.mass s * insertSum (thinningKernel θ s) r * f s := by
    unfold insertSum thinningMoment
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∉ r <;> simp [hv]
  have h := HasDerivAt.fun_sum (u := (univ : Finset (Finset V)))
    (fun s _ => ((hasDerivAt_thinningKernel hθ hθ1 s r).const_mul (μ.mass s)).mul_const (f s))
  convert h using 1
  · rfl
  · rw [hUp]
    unfold thinningMoment
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro s _
    ring

end HardCoreActivityThreshold
