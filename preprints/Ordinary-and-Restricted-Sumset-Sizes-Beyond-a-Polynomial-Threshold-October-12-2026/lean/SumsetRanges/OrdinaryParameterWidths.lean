import SumsetRanges.OrdinaryParameterBounds
import SumsetRanges.OrdinaryWidths
import SumsetRanges.ParameterWidths

open Finset
namespace SumsetRanges
open scoped Classical


theorem ordinary_parameter_repetition_width (h c b μ : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ)
    (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 (h-1))
    (hv : InNatBox (ordinaryCaps h c b) v) :
    2*((sharedCap c-1 : ℕ) : ℤ)*ordinaryWeight c b (h-(μ+1))≤
      ordinaryParameterValue h c b (Function.update v (repetitionIndex (h-1) μ hm) 0)-
      ordinaryParameterValue h c b (Function.update v (repetitionIndex (h-1) μ hm) (repetitionCap c)) := by
  apply linear_width_covers_shared (fun j => ordinaryParameterValue h c b (Function.update v (repetitionIndex (h-1) μ hm) j)) (repetitionCap c) (sharedCap c) _
    (ordinaryWeight_nonneg c b (h-(μ+1))) (shared_width_le_repetition (by omega) hc)
  intro j hj
  have hv' : InNatBox (ordinaryCaps h c b) (Function.update v (repetitionIndex (h-1) μ hm) j) :=
    inNatBox_update _ _ hv _ j (by simpa [ordinaryCaps] using Nat.le_of_lt hj)
  have hs := (ordinary_parameter_linear_step_bounds h c b μ (Function.update v (repetitionIndex (h-1) μ hm) j)
    hh hc hb hm hv' (by simpa using hj)).1
  simpa only [Function.update_self,Function.update_idem] using hs

theorem ordinary_parameter_shared_width (h c b μ : ℕ) (v : Fin (parameterDimension (h-1)) → ℕ)
    (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 (h-1))
    (hkc : sparseThreshold (c+b)≤c) (hv : InNatBox (ordinaryCaps h c b) v) :
    2*((2*h*(c+b) : ℕ) : ℤ)*ordinaryWeight c b (h-(μ+1))≤
      ordinaryParameterValue h c b (Function.update v (sharedIndex (h-1) μ hm) 0)-
      ordinaryParameterValue h c b (Function.update v (sharedIndex (h-1) μ hm) (sharedCap c-1)) := by
  have hS := (large_caps_positive (by omega : 1≤h) hc).2
  apply shared_width_covers_linear (fun j => ordinaryParameterValue h c b (Function.update v (sharedIndex (h-1) μ hm) j)) (sharedCap c) (2*h*(c+b)) _
    (ordinaryWeight_nonneg c b (h-(μ+1))) (by omega) (by have hw := ordinary_shared_width hh hc hkc; nlinarith)
  intro j hj
  have hv' : InNatBox (ordinaryCaps h c b) (Function.update v (sharedIndex (h-1) μ hm) j) :=
    inNatBox_update _ _ hv _ j (by simpa [ordinaryCaps] using Nat.le_of_lt hj)
  have hs := (ordinary_parameter_shared_step_bounds h c b μ (Function.update v (sharedIndex (h-1) μ hm) j)
    hh hc hb hm hv' (by simpa using hj)).1
  simpa only [Function.update_self,Function.update_idem] using hs

theorem ordinary_parameter_width_bound (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c)
    (v : Fin (parameterDimension (h-1)) → ℕ) (hv : InNatBox (ordinaryCaps h c b) v)
    (i : Fin (parameterDimension (h-1))) :
    ordinaryParameterWidthBound h c b i≤ordinaryParameterValue h c b (Function.update v i 0)-
      ordinaryParameterValue h c b (Function.update v i (ordinaryCaps h c b i)) := by
  rcases parameterIndex_cases (h-1) (by omega) i with he | ⟨m,hm,he|he⟩
  · subst i
    have hx := inNatBox_update _ _ hv (denseIndex (h-1)) 0 (Nat.zero_le _)
    have hy := inNatBox_update _ _ hv (denseIndex (h-1)) (ordinaryCaps h c b (denseIndex (h-1))) (le_refl _)
    have he := ordinary_parameter_antitone h c b hh hc hb _ _ hx hy (by
      intro j
      by_cases hj : j=denseIndex (h-1)
      · subst j; simp
      · simp only [Function.update_of_ne hj,le_refl])
    simp only [ordinaryParameterWidthBound,ite_true]
    omega
  · subst i
    have he : ordinaryParameterWidthBound h c b (repetitionIndex (h-1) m hm)=
        2*((sharedCap c-1 : ℕ) : ℤ)*ordinaryWeight c b (h-(m+1)) := by
      simp only [ordinaryParameterWidthBound,ite_eq_right (repetitionIndex_ne_dense (h-1) m hm)]
      simp [repetitionIndex,Nat.sub_sub,Nat.add_comm 1]
    rw [he]
    have hn : ordinaryCaps h c b (repetitionIndex (h-1) m hm)=repetitionCap c := by simp [ordinaryCaps]
    rw [hn]
    exact ordinary_parameter_repetition_width h c b m v hh hc hb hm hv
  · subst i
    have he : ordinaryParameterWidthBound h c b (sharedIndex (h-1) m hm)=
        2*((2*h*(c+b) : ℕ) : ℤ)*ordinaryWeight c b (h-(m+1)) := by
      have hmod : (sharedIndex (h-1) m hm).val%2≠0 := by simp [sharedIndex,Nat.add_mod]
      have hdiv : (sharedIndex (h-1) m hm).val/2=h-(m+1) := by simp only [sharedIndex]; omega
      simp only [ordinaryParameterWidthBound,ite_eq_right (sharedIndex_ne_dense (h-1) m hm),ite_eq_right hmod,hdiv]
      push_cast
      ring
    rw [he]
    have hn : ordinaryCaps h c b (sharedIndex (h-1) m hm)=sharedCap c-1 := by simp [ordinaryCaps]
    rw [hn]
    exact ordinary_parameter_shared_width h c b m v hh hc hb hm hkc hv

end SumsetRanges
