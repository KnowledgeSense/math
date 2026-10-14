import MainTheorems.PreorderGamma.IntegerBasisCoordinates

namespace ResearchMain.PreorderGamma

open Module
open scoped BigOperators Classical

variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T]

theorem integer_independent_combination_integral (V : T → I → ℤ) (S : Set T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hS : LinearIndepOn ℝ (fun t => integerVectorCast (V t)) S)
    (hspan : Submodule.span ℝ (Set.range (fun t => integerVectorCast (V t))) = ⊤)
    (z : I → ℤ) (c : S → ℝ)
    (hz : integerVectorCast z = ∑ s : S, c s • integerVectorCast (V s.val)) :
    ∃ a : S → ℤ, (∀ s, c s = (a s : ℝ)) ∧ (∑ s : S, a s • V s.val) = z := by
  obtain ⟨f, _, hsub, hlin⟩ := integer_column_basis_extension V S hS hspan
  let g : S → I := fun s => Classical.choose (hsub s.property)
  have hg : ∀ s : S, f (g s) = s.val :=
    fun s => Classical.choose_spec (hsub s.property)
  have hginj : Function.Injective g := by
    intro s t hst
    apply Subtype.ext
    calc
      s.val = f (g s) := (hg s).symm
      _ = f (g t) := congrArg f hst
      _ = t.val := hg t
  let b := realColumnBasis V f hlin
  have hvec : ∀ s : S, integerVectorCast (V s.val) = b (g s) := by
    intro s
    dsimp only [b]
    rw [realColumnBasis_apply, hg]
  have hsum : integerVectorCast z = ∑ s : S, c s • b (g s) := by
    simpa only [hvec] using hz
  have hrepr : ∀ s : S, b.repr (integerVectorCast z) (g s) = c s := by
    intro s
    change b.coord (g s) (integerVectorCast z) = c s
    rw [hsum, map_sum]
    simp only [map_smul, smul_eq_mul, Basis.coord_apply,
      Basis.repr_self_apply, hginj.eq_iff, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  let a : S → ℤ := fun s => integerBasisCoordinates V f z (g s)
  have hc : ∀ s : S, c s = (a s : ℝ) := by
    intro s
    exact (hrepr s).symm.trans (integer_basis_repr_eq V f hV hlin z (g s))
  refine ⟨a, hc, ?_⟩
  funext i
  apply Int.cast_injective (α := ℝ)
  simpa only [integerVectorCast, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_sum, Int.cast_mul, hc] using (congrFun hz i).symm

theorem integer_independent_combination_nonnegative (V : T → I → ℤ) (S : Set T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hS : LinearIndepOn ℝ (fun t => integerVectorCast (V t)) S)
    (hspan : Submodule.span ℝ (Set.range (fun t => integerVectorCast (V t))) = ⊤)
    (z : I → ℤ) (c : S → ℝ)
    (hz : integerVectorCast z = ∑ s : S, c s • integerVectorCast (V s.val))
    (hc : ∀ s, 0 ≤ c s) :
    ∃ a : S → ℕ, (∀ s, c s = (a s : ℝ)) ∧
      (∑ s : S, (a s : ℤ) • V s.val) = z := by
  obtain ⟨a, ha, hsum⟩ := integer_independent_combination_integral V S hV hS hspan z c hz
  have hpos : ∀ s, 0 ≤ a s := by
    intro s
    have h : 0 ≤ (a s : ℝ) := by rw [← ha s]; exact hc s
    exact_mod_cast h
  have hnat : ∀ s, ((a s).toNat : ℤ) = a s := fun s => Int.toNat_of_nonneg (hpos s)
  refine ⟨fun s => (a s).toNat, ?_, ?_⟩
  · intro s
    calc
      c s = (a s : ℝ) := ha s
      _ = ((a s).toNat : ℝ) := by exact_mod_cast (hnat s).symm
  · simpa only [hnat] using hsum

theorem integer_independent_combination_positive (V : T → I → ℤ) (S : Set T)
    (hV : (integerConfigurationMatrix V).IsTotallyUnimodular)
    (hS : LinearIndepOn ℝ (fun t => integerVectorCast (V t)) S)
    (hspan : Submodule.span ℝ (Set.range (fun t => integerVectorCast (V t))) = ⊤)
    (z : I → ℤ) (c : S → ℝ)
    (hz : integerVectorCast z = ∑ s : S, c s • integerVectorCast (V s.val))
    (hc : ∀ s, 0 < c s) :
    ∃ a : S → ℕ, (∀ s, 0 < a s ∧ c s = (a s : ℝ)) ∧
      (∑ s : S, (a s : ℤ) • V s.val) = z := by
  obtain ⟨a, ha, hsum⟩ := integer_independent_combination_nonnegative V S hV hS hspan
    z c hz (fun s => (hc s).le)
  refine ⟨a, ?_, hsum⟩
  intro s
  refine ⟨?_, ha s⟩
  have h : 0 < (a s : ℝ) := by rw [← ha s]; exact hc s
  exact_mod_cast h

end ResearchMain.PreorderGamma
