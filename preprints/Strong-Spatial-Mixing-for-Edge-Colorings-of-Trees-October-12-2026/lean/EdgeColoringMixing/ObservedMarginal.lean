import EdgeColoringMixing.BufferNorm
import EdgeColoringMixing.TreeColorings
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
namespace EdgeColoringMixing
open Finset

/-- Total variation is Lipschitz under normalization of nonnegative weights. -/
theorem normalized_weights_tv {q : ℕ} (u v : Fin q → ℝ)
    (_hu : ∀c,0≤u c) (hv : ∀c,0≤v c)
    (hU : 0<∑c,u c) (hV : 0<∑c,v c) :
    totalVariation (fun c => u c/(∑i,u i)) (fun c => v c/(∑i,v i))≤
      (∑c,|u c-v c|)/(∑i,u i) := by
  let U := ∑c,u c
  let V := ∑c,v c
  have hU0 : U≠0 := ne_of_gt hU
  have hV0 : V≠0 := ne_of_gt hV
  have he (c : Fin q) : u c/U-v c/V=(u c-v c)/U+(v c/V)*((V-U)/U) := by
    field_simp
    ring
  have hp (c : Fin q) : |u c/U-v c/V|≤|u c-v c|/U+(v c/V)*(|V-U|/U) := by
    rw [he]
    convert abs_add_le ((u c-v c)/U) ((v c/V)*((V-U)/U)) using 1
    rw [abs_div,abs_of_pos hU,abs_mul,abs_of_nonneg (div_nonneg (hv c) hV.le),abs_div,abs_of_pos hU]
  have hn : ∑c,v c/V=1 := by rw [←sum_div]; exact div_self hV0
  have hz : |V-U|≤∑c,|u c-v c| := by
    calc
      _=|∑c,(v c-u c)| := by rw [sum_sub_distrib]
      _≤∑c,|v c-u c| := abs_sum_le_sum_abs _ _
      _=∑c,|u c-v c| := by simp only [abs_sub_comm]
  have hsum := sum_le_sum (fun c (_ : c∈(univ : Finset (Fin q))) => hp c)
  rw [sum_add_distrib,←sum_div,←sum_mul,hn,one_mul] at hsum
  have hz' := div_le_div_of_nonneg_right hz hU.le
  unfold totalVariation
  change (∑c,|u c/U-v c/V|)/2≤_
  linarith

/-- The two root-message normalizer stays above the original surplus. -/
theorem observed_normalizer_lower {Δ q : ℕ} {A B : Fin q → ℝ}
    (hA : MessageDomain Δ q A) (hB : MessageDomain Δ q B) :
    (q : ℝ)-2*(Δ : ℝ)+2≤∑c,A c*B c := by
  have hsum : (∑c,(A c+B c-1))≤∑c,A c*B c := by
    apply sum_le_sum
    intro c _
    nlinarith [hA.nonneg c,hB.nonneg c,hA.le_one c,hB.le_one c]
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hsum
  linarith [hA.mass,hB.mass]

noncomputable def observedMarginal {q : ℕ} (A B : Fin q → ℝ) (c : Fin q) : ℝ :=
  A c*B c/(∑i,A i*B i)

theorem observed_marginal_tv_bound {Δ q : ℕ} {A B A' B' : Fin q → ℝ}
    (hA : MessageDomain Δ q A) (hB : MessageDomain Δ q B)
    (hA' : MessageDomain Δ q A') (hB' : MessageDomain Δ q B')
    (hs : 0<(q : ℝ)-2*(Δ : ℝ)+2) :
    totalVariation (observedMarginal A B) (observedMarginal A' B')≤
      ((∑c,|A c-A' c|)+(∑c,|B c-B' c|))/((q : ℝ)-2*(Δ : ℝ)+2) := by
  have hZ := observed_normalizer_lower hA hB
  have hZ' := observed_normalizer_lower hA' hB'
  have hpos := hs.trans_le hZ
  have hpos' := hs.trans_le hZ'
  have hw := normalized_weights_tv (fun c => A c*B c) (fun c => A' c*B' c)
    (fun c => mul_nonneg (hA.nonneg c) (hB.nonneg c))
    (fun c => mul_nonneg (hA'.nonneg c) (hB'.nonneg c)) hpos hpos'
  have hdiff : (∑c,|A c*B c-A' c*B' c|)≤(∑c,|A c-A' c|)+(∑c,|B c-B' c|) := by
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro c _
    calc
      _=|(A c-A' c)*B c+A' c*(B c-B' c)| := by congr 1; ring
      _≤|(A c-A' c)*B c|+|A' c*(B c-B' c)| := abs_add_le _ _
      _=|A c-A' c| *B c+A' c* |B c-B' c| := by rw [abs_mul,abs_mul,abs_of_nonneg (hB.nonneg c),abs_of_nonneg (hA'.nonneg c)]
      _≤|A c-A' c|+|B c-B' c| := by nlinarith [hB.le_one c,hA'.le_one c,abs_nonneg (A c-A' c),abs_nonneg (B c-B' c)]
  exact hw.trans ((div_le_div_of_nonneg_right hdiff hpos.le).trans
    (div_le_div_of_nonneg_left (by positivity) hs hZ))

/-- Integrate a joint finite-coordinate speed by one signed scalar mean-value
argument. Continuity is required at the endpoints; derivatives only in the interior. -/
theorem finite_l1_path_endpoint_bound {ι : Type*} [Fintype ι]
    (P V : ℝ → ι → ℝ) {M : ℝ}
    (hcont : ∀ c, ContinuousOn (fun t => P t c) (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ c, HasDerivAt (fun r => P r c) (V t c) t)
    (hspeed : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (∑ c, |V t c|) ≤ M) :
    (∑ c, |P 1 c - P 0 c|) ≤ M := by
  classical
  let ε : ι → ℝ := fun c => if 0 ≤ P 1 c - P 0 c then 1 else -1
  let f := fun t => ∑ c, ε c * P t c
  let f' := fun t => ∑ c, ε c * V t c
  have hε (c : ι) : |ε c| = 1 := by dsimp only [ε]; split_ifs <;> norm_num
  have hεdiff (c : ι) : ε c * (P 1 c - P 0 c) = |P 1 c - P 0 c| := by
    dsimp only [ε]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    continuousOn_finsetSum univ (fun c _ => (hcont c).const_mul (ε c))
  have hfderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    exact HasDerivAt.fun_sum (u := univ) (fun c _ => (hderiv t ht c).const_mul (ε c))
  obtain ⟨t, ht, heq⟩ := exists_hasDerivAt_eq_slope f f' (by norm_num : (0 : ℝ) < 1) hfcont hfderiv
  have hdiff : f 1 - f 0 = ∑ c, |P 1 c - P 0 c| := by
    dsimp only [f]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro c _
    rw [← mul_sub, hεdiff]
  have hbound : f' t ≤ M := by
    calc
      _ ≤ ∑ c, |ε c * V t c| := sum_le_sum (fun c _ => le_abs_self _)
      _ = ∑ c, |V t c| := by simp only [abs_mul, hε, one_mul]
      _ ≤ M := hspeed t ht
  rw [heq] at hbound
  simpa only [sub_zero, div_one, hdiff] using hbound

/-- Uniform arcsine speed controls the actual endpoint message difference. -/
theorem arcsine_path_endpoint_bound {Δ q : ℕ} (A ξ : ℝ → Fin q → ℝ) {M : ℝ}
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, MessageDomain Δ q (A t))
    (hcont : ∀ c, ContinuousOn (fun t => A t c) (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ c, HasDerivAt (fun r => A r c) (ξ t c) t)
    (htan : ∀ t ∈ Set.Ioo (0 : ℝ) 1, EndpointTangent (A t) (ξ t))
    (hspeed : ∀ t ∈ Set.Ioo (0 : ℝ) 1, arcsineNorm (A t) (ξ t) ≤ M) :
    (∑ c, |A 1 c - A 0 c|) ≤ Real.sqrt q / 2 * M := by
  apply finite_l1_path_endpoint_bound A ξ hcont hderiv
  intro t ht
  have hA := hpath t ⟨ht.1.le, ht.2.le⟩
  exact (arcsineNorm.l1_bound hA.nonneg hA.le_one (htan t ht)).trans
    (mul_le_mul_of_nonneg_left (hspeed t ht) (by positivity))

/-- The observed edge estimate using two root paths from the same interpolation.
The finite signed-sum argument preserves the original `sqrt(q)` constant. -/
theorem observed_marginal_path_bound {Δ q : ℕ}
    (A B ξ η : ℝ → Fin q → ℝ) {M : ℝ}
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) 1, MessageDomain Δ q (A t))
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, MessageDomain Δ q (B t))
    (hcA : ∀ c, ContinuousOn (fun t => A t c) (Set.Icc (0 : ℝ) 1))
    (hcB : ∀ c, ContinuousOn (fun t => B t c) (Set.Icc (0 : ℝ) 1))
    (hdA : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ c, HasDerivAt (fun r => A r c) (ξ t c) t)
    (hdB : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ c, HasDerivAt (fun r => B r c) (η t c) t)
    (htA : ∀ t ∈ Set.Ioo (0 : ℝ) 1, EndpointTangent (A t) (ξ t))
    (htB : ∀ t ∈ Set.Ioo (0 : ℝ) 1, EndpointTangent (B t) (η t))
    (hsA : ∀ t ∈ Set.Ioo (0 : ℝ) 1, arcsineNorm (A t) (ξ t) ≤ M)
    (hsB : ∀ t ∈ Set.Ioo (0 : ℝ) 1, arcsineNorm (B t) (η t) ≤ M)
    (hs : 0 < (q : ℝ) - 2 * Δ + 2) :
    totalVariation (observedMarginal (A 0) (B 0)) (observedMarginal (A 1) (B 1)) ≤
      Real.sqrt q * M / ((q : ℝ) - 2 * Δ + 2) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hnorm := observed_marginal_tv_bound (hA 0 h0) (hB 0 h0) (hA 1 h1) (hB 1 h1) hs
  have hPA := arcsine_path_endpoint_bound A ξ hA hcA hdA htA hsA
  have hPB := arcsine_path_endpoint_bound B η hB hcB hdB htB hsB
  simp only [abs_sub_comm] at hPA hPB
  apply hnorm.trans
  apply (div_le_div_of_nonneg_right (add_le_add hPA hPB) hs.le).trans_eq
  congr 1
  ring

/-- The constant `C` in the release, with the two lost boundary levels and
observed-edge normalization absorbed into the same exponential rate. -/
noncomputable def mixingPrefactor (q : ℕ) (s E κ : ℝ) : ℝ :=
  max (1 / κ^2) (Real.sqrt q * E / (s * κ^3))

theorem mixingPrefactor_nonneg (q : ℕ) (s E κ : ℝ) : 0 ≤ mixingPrefactor q s E κ :=
  (div_nonneg zero_le_one (sq_nonneg κ)).trans (le_max_left _ _)

/-- The original prefactor absorbs the `ℓ - 3` exponent and the trivial
short-distance bound without changing the contraction rate. -/
theorem buffer_decay_bound {q ℓ : ℕ} {D s E κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (hκ1 : κ < 1) (htrivial : D ≤ 1)
    (hfar : 3 ≤ ℓ → D ≤ Real.sqrt q * E / s * κ^(ℓ - 3)) :
    D ≤ mixingPrefactor q s E κ * κ^ℓ := by
  by_cases hℓ : 3 ≤ ℓ
  · have hpow : κ^ℓ = κ^(ℓ - 3) * κ^3 := by
      rw [← pow_add, Nat.sub_add_cancel hℓ]
    have hid : Real.sqrt q * E / s * κ^(ℓ - 3) =
        (Real.sqrt q * E / (s * κ^3)) * κ^ℓ := by
      rw [hpow]
      field_simp
    apply (hfar hℓ).trans
    rw [hid]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hκ.le _)
  · have hsmall : ℓ ≤ 2 := by omega
    have hp : κ^2 ≤ κ^ℓ := by
      interval_cases ℓ
      · simp only [pow_zero]
        nlinarith
      · simp only [pow_one]
        nlinarith
      · rfl
    have hκ2 : 0 < κ^2 := sq_pos_of_pos hκ
    have hshort : 1 ≤ (1 / κ^2) * κ^ℓ := by
      have h := (le_div_iff₀ hκ2).mpr (show 1 * κ^2 ≤ κ^ℓ by simpa using hp)
      convert h using 1; ring
    exact htrivial.trans (hshort.trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (pow_nonneg hκ.le _)))

/-- Extended-distance version matching the original strong-spatial-mixing statement.
The infinite case is supplied by equality of the relevant conditioned marginals. -/
theorem buffer_distanceDecay_bound {q : ℕ} {ℓ : ℕ∞} {D s E κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (hκ1 : κ < 1) (htrivial : D ≤ 1)
    (hinfinite : ℓ = ⊤ → D = 0)
    (hfar : ∀ n : ℕ, ℓ = n → 3 ≤ n → D ≤ Real.sqrt q * E / s * κ^(n - 3)) :
    D ≤ mixingPrefactor q s E κ * distanceDecay κ ℓ := by
  by_cases htop : ℓ = ⊤
  · simp [distanceDecay, htop, hinfinite htop]
  · rw [distanceDecay, ite_eq_right htop]
    exact buffer_decay_bound hs hκ hκ1 htrivial
      (hfar ℓ.toNat (ENat.natCast_toNat htop).symm)

end EdgeColoringMixing
