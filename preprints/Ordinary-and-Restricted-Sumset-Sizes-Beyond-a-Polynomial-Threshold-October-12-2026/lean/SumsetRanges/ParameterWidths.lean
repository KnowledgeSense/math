import SumsetRanges.ParameterBounds

open Finset
namespace SumsetRanges
open scoped Classical

theorem inNatBox_update {d : ℕ} (n v : Fin d → ℕ) (hv : InNatBox n v)
    (i : Fin d) (a : ℕ) (ha : a≤n i) : InNatBox n (Function.update v i a) := by
  intro j
  by_cases he : j=i
  · subst j; simpa using ha
  · simpa only [Function.update_of_ne he] using hv j

theorem parameter_repetition_width (h c b μ : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 h)
    (hv : InNatBox (admissibleCaps h c b) v) :
    2*((sharedCap c-1 : ℕ) : ℤ)*restrictedWeight c b (h-μ)≤
      parameterValue h c b (Function.update v (repetitionIndex h μ hm) 0)-
      parameterValue h c b (Function.update v (repetitionIndex h μ hm) (repetitionCap c)) := by
  apply linear_width_covers_shared (fun j => parameterValue h c b (Function.update v (repetitionIndex h μ hm) j)) (repetitionCap c) (sharedCap c) _
    (restrictedWeight_nonneg c b (h-μ)) (shared_width_le_repetition (by omega) hc)
  intro j hj
  have hv' : InNatBox (admissibleCaps h c b) (Function.update v (repetitionIndex h μ hm) j) :=
    inNatBox_update _ _ hv _ j (by simpa [admissibleCaps] using Nat.le_of_lt hj)
  have hs := (parameter_linear_step_bounds h c b μ (Function.update v (repetitionIndex h μ hm) j)
    hh hc hb hm hv' (by simpa using hj)).1
  simpa only [Function.update_self,Function.update_idem] using hs

theorem parameter_shared_width (h c b μ : ℕ) (v : Fin (parameterDimension h) → ℕ)
    (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) (hm : μ∈Icc 2 h)
    (hkc : sparseThreshold (c+b)≤c) (hv : InNatBox (admissibleCaps h c b) v) :
    2*((c+b : ℕ) : ℤ)*restrictedWeight c b (h-μ)≤
      parameterValue h c b (Function.update v (sharedIndex h μ hm) 0)-
      parameterValue h c b (Function.update v (sharedIndex h μ hm) (sharedCap c-1)) := by
  have hS := (large_caps_positive (by omega : 1≤h) hc).2
  apply shared_width_covers_linear (fun j => parameterValue h c b (Function.update v (sharedIndex h μ hm) j)) (sharedCap c) (c+b) _
    (restrictedWeight_nonneg c b (h-μ)) (by omega) (shared_width_covers_k (by omega) hc hkc)
  intro j hj
  have hv' : InNatBox (admissibleCaps h c b) (Function.update v (sharedIndex h μ hm) j) :=
    inNatBox_update _ _ hv _ j (by simpa [admissibleCaps] using Nat.le_of_lt hj)
  have hs := (parameter_shared_step_bounds h c b μ (Function.update v (sharedIndex h μ hm) j)
    hh hc hb hm hv' (by simpa using hj)).1
  simpa only [Function.update_self,Function.update_idem] using hs

theorem parameter_width_bound (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c)
    (v : Fin (parameterDimension h) → ℕ) (hv : InNatBox (admissibleCaps h c b) v)
    (i : Fin (parameterDimension h)) :
    parameterWidthBound h c b i≤parameterValue h c b (Function.update v i 0)-
      parameterValue h c b (Function.update v i (admissibleCaps h c b i)) := by
  rcases parameterIndex_cases h hh i with he | ⟨m,hm,he|he⟩
  · subst i
    have hx := inNatBox_update _ _ hv (denseIndex h) 0 (Nat.zero_le _)
    have hy := inNatBox_update _ _ hv (denseIndex h) (admissibleCaps h c b (denseIndex h)) (le_refl _)
    have he := parameter_antitone h c b hh hc hb _ _ hx hy (by
      intro j
      by_cases hj : j=denseIndex h
      · subst j; simp
      · simp only [Function.update_of_ne hj,le_refl])
    simp only [parameterWidthBound,ite_true]
    omega
  · subst i
    have he : parameterWidthBound h c b (repetitionIndex h m hm)=
        2*((sharedCap c-1 : ℕ) : ℤ)*restrictedWeight c b (h-m) := by
      simp only [parameterWidthBound,ite_eq_right (repetitionIndex_ne_dense h m hm)]
      simp [repetitionIndex]
    rw [he]
    have hn : admissibleCaps h c b (repetitionIndex h m hm)=repetitionCap c := by simp [admissibleCaps]
    rw [hn]
    exact parameter_repetition_width h c b m v hh hc hb hm hv
  · subst i
    have he : parameterWidthBound h c b (sharedIndex h m hm)=
        2*((c+b : ℕ) : ℤ)*restrictedWeight c b (h-m) := by
      have hmod : (sharedIndex h m hm).val%2≠0 := by simp [sharedIndex,Nat.add_mod]
      have hdiv : (sharedIndex h m hm).val/2=h-m := by simp only [sharedIndex]; omega
      simp only [parameterWidthBound,ite_eq_right (sharedIndex_ne_dense h m hm),ite_eq_right hmod,hdiv]
    rw [he]
    have hn : admissibleCaps h c b (sharedIndex h m hm)=sharedCap c-1 := by simp [admissibleCaps]
    rw [hn]
    exact parameter_shared_width h c b m v hh hc hb hm hkc hv

end SumsetRanges
