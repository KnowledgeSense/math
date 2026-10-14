import R34.ReducedCore

namespace R34.ReducedCharge

open MvPolynomial ChargeSites
open scoped BigOperators Classical
noncomputable section

def firstZ : (ch : Chain) → (ChargeEdges ch.sizes → ℝ) →
    (Fin (ch.first.size - 1) → ℝ)
  | .last _, z => z
  | .cons _ _ (.last _), z => fun e => z (.inl e)
  | .cons _ _ (.cons _ _ _), z => fun e => z (.inl e)

def tailZ (c : ChargedSite) : (tail : Chain) →
    (ChargeEdges (c.size :: tail.sizes) → ℝ) → (ChargeEdges tail.sizes → ℝ)
  | .last _, z => fun e => z (.inr (.inr e))
  | .cons _ _ _, z => fun e => z (.inr (.inr e))

def junctionZ (c : ChargedSite) : (tail : Chain) →
    (ChargeEdges (c.size :: tail.sizes) → ℝ) → ℝ
  | .last _, z => z (.inr (.inl ()))
  | .cons _ _ _, z => z (.inr (.inl ()))

def cornerFirst (ch : Chain) (z : ChargeEdges ch.sizes → ℝ) : Site :=
  cornerSite ch.first (firstZ ch z)

def cornerEdges : (ch : Chain) → (ChargeEdges ch.sizes → ℝ) → List OptionEdge
  | .last _, _ => []
  | .cons c K tail, z =>
    { target := cornerFirst tail (tailZ c tail z), kernel := K,
      sign := junctionZ c tail z } :: cornerEdges tail (tailZ c tail z)

def cornerFactor : (ch : Chain) → (ChargeEdges ch.sizes → ℝ) → ℝ
  | .last c, z => goodFactor c z
  | .cons c K tail, z =>
    goodFactor c (firstZ (.cons c K tail) z) * cornerFactor tail (tailZ c tail z)

def jointScalar (c d : ChargedSite) (K : Kernel) (ζ : ℝ) : ℝ :=
  if sameKind c d then theta K ζ else thetaPrime K ζ

def beforeTarget (c d : ChargedSite) (K : Kernel) (ζ : ℝ)
    (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.1 * K.d + state.2 * K.q,
    state.1 * K.p + state.2 * jointScalar c d K ζ)

def affineEdgeProduct (ch : Chain) (o : Options ch)
    (z : ChargeEdges ch.sizes → ℝ) : ℝ :=
  Finset.univ.prod (fun e : ChargeEdges ch.sizes =>
    (edgeAffine ch o e).1 + (edgeAffine ch o e).2 * z e)

theorem initialOptions_boundary (c : ChargedSite) (z : Fin (c.size - 1) → ℝ)
    (left : ℝ × ℝ) (o : Bool) :
    optionBoundary (initialOptions (cornerSite c z) left) o =
      optionBoundary left o * siteCoefficient c o *
        (if o then internalEta c z else 1) := by
  cases c <;> cases o <;>
    simp [cornerSite, initialOptions, optionBoundary, siteCoefficient, internalEta, mul_comm]

theorem junctionAffine_value (c d : ChargedSite) (K : Kernel) (o p : Bool) (ζ : ℝ) :
    (junctionAffine c d K o p).1 + (junctionAffine c d K o p).2 * ζ =
      if o then (if p then jointScalar c d K ζ else K.q)
      else (if p then K.p else K.d) := by
  cases o <;> cases p <;>
    simp [junctionAffine, jointScalar, theta, thetaPrime]
  split_ifs <;> simp
  ring

theorem sum_junction (c d : ChargedSite) (K : Kernel) (ζ : ℝ)
    (state : ℝ × ℝ) (p : Bool) :
    (∑ o : Bool, optionBoundary state o *
      ((junctionAffine c d K o p).1 + (junctionAffine c d K o p).2 * ζ)) =
      optionBoundary (beforeTarget c d K ζ state) p := by
  simp only [junctionAffine_value, Fintype.sum_bool]
  cases p <;> simp [optionBoundary, beforeTarget, add_comm]

theorem optionStep_beforeTarget (c d : ChargedSite)
    (zc : Fin (c.size - 1) → ℝ) (zd : Fin (d.size - 1) → ℝ)
    (K : Kernel) (ζ : ℝ) (state : ℝ × ℝ) :
    optionStep (cornerSite c zc) (cornerSite d zd) K ζ state =
      initialOptions (cornerSite d zd) (beforeTarget c d K ζ state) := by
  cases c <;> cases d <;>
    simp [cornerSite, optionStep, initialOptions, beforeTarget, jointScalar, sameKind, junction]

theorem affineEdgeProduct_last (c : ChargedSite) (o : Bool)
    (z : ChargeEdges (Chain.last c).sizes → ℝ) :
    affineEdgeProduct (.last c) o z =
      goodFactor c z * (if o then internalEta c z else 1) :=
  internal_product c o z

theorem affineEdgeProduct_cons (c : ChargedSite) (K : Kernel) (tail : Chain)
    (o : Options (.cons c K tail)) (z : ChargeEdges (Chain.cons c K tail).sizes → ℝ) :
    affineEdgeProduct (.cons c K tail) o z =
      (goodFactor c (firstZ (.cons c K tail) z) *
        (if o.1 then internalEta c (firstZ (.cons c K tail) z) else 1)) *
      ((junctionAffine c tail.first K o.1 (firstOption tail o.2)).1 +
        (junctionAffine c tail.first K o.1 (firstOption tail o.2)).2 *
          junctionZ c tail z) *
      affineEdgeProduct tail o.2 (tailZ c tail z) := by
  cases tail with
  | last d =>
    dsimp only [Chain.sizes, Chain.first] at *
    unfold affineEdgeProduct
    rw [chargeEdges_prod_join]
    simp only [edgeAffine, Chain.first, firstOption, firstZ, tailZ, junctionZ]
    rw [internal_product]
  | cons d L tail =>
    dsimp only [Chain.sizes, Chain.first] at *
    unfold affineEdgeProduct
    rw [chargeEdges_prod_join]
    simp only [edgeAffine, Chain.first, firstOption, firstZ, tailZ, junctionZ]
    rw [internal_product]

theorem affineModel_last (c : ChargedSite) (left right : ℝ × ℝ)
    (z : ChargeEdges (Chain.last c).sizes → ℝ) :
    affineModel (.last c) left right z = goodFactor c z *
      ((initialOptions (cornerSite c z) left).1 * right.1 +
        (initialOptions (cornerSite c z) left).2 * right.2) := by
  change (∑ o : Bool, optionCoefficient (.last c) left right o *
    affineEdgeProduct (.last c) o z) = _
  simp only [affineEdgeProduct_last, optionCoefficient, firstOption, lastOption,
    siteCoefficients, Fintype.sum_bool]
  cases c with
  | point => simp [siteCoefficient, optionBoundary, cornerSite, initialOptions, goodFactor,
      internalEta]
  | group a => simp [siteCoefficient, optionBoundary, cornerSite, initialOptions]; ring

theorem affineModel_cons (c : ChargedSite) (K : Kernel) (tail : Chain)
    (left right : ℝ × ℝ) (z : ChargeEdges (Chain.cons c K tail).sizes → ℝ) :
    affineModel (.cons c K tail) left right z =
      goodFactor c (firstZ (.cons c K tail) z) *
        affineModel tail
          (beforeTarget c tail.first K (junctionZ c tail z)
            (initialOptions (cornerFirst (.cons c K tail) z) left))
          right (tailZ c tail z) := by
  let head := firstZ (.cons c K tail) z
  let rest := tailZ c tail z
  let ζ := junctionZ c tail z
  let state := initialOptions (cornerSite c head) left
  let J : Bool → Bool → ℝ := fun o p =>
    (junctionAffine c tail.first K o p).1 + (junctionAffine c tail.first K o p).2 * ζ
  let W : Options tail → ℝ := fun p => siteCoefficients tail p *
    optionBoundary right (lastOption tail p) * affineEdgeProduct tail p rest
  have ht : ∀ o : Options (.cons c K tail),
      optionCoefficient (.cons c K tail) left right o *
        affineEdgeProduct (.cons c K tail) o z =
      goodFactor c head *
        (optionBoundary state o.1 * J o.1 (firstOption tail o.2) * W o.2) := by
    intro o
    rw [affineEdgeProduct_cons]
    dsimp only [optionCoefficient, firstOption, siteCoefficients, lastOption,
      state, J, W, head, rest, ζ]
    rw [initialOptions_boundary]
    ring
  calc
    _ = ∑ o : Bool × Options tail, goodFactor c head *
        (optionBoundary state o.1 * J o.1 (firstOption tail o.2) * W o.2) := by
      change (∑ o : Options (.cons c K tail),
        optionCoefficient (.cons c K tail) left right o *
          affineEdgeProduct (.cons c K tail) o z) = _
      simp_rw [ht]
    _ = goodFactor c head * ∑ p : Options tail,
        optionBoundary (beforeTarget c tail.first K ζ state) (firstOption tail p) * W p := by
      rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [Prod.fst, Prod.snd]
      rw [← Finset.sum_mul]
      congr 1
      exact sum_junction c tail.first K ζ state (firstOption tail p)
    _ = _ := by
      congr 1
      change (∑ p : Options tail,
        optionBoundary (beforeTarget c tail.first K ζ state) (firstOption tail p) * W p) =
        ∑ p : Options tail,
          optionCoefficient tail (beforeTarget c tail.first K ζ state) right p *
            affineEdgeProduct tail p rest
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [W, optionCoefficient]
      ring

theorem affineModel_eq_corner (ch : Chain) (left right : ℝ × ℝ)
    (z : ChargeEdges ch.sizes → ℝ) :
    affineModel ch left right z = cornerFactor ch z *
      optionValue (cornerFirst ch z) left right (cornerEdges ch z) := by
  induction ch generalizing left with
  | last c =>
    simpa [cornerFactor, cornerFirst, cornerEdges, optionValue, optionFold, firstZ]
      using affineModel_last c left right z
  | cons c K tail ih =>
    rw [affineModel_cons, ih]
    simp only [cornerFactor, cornerEdges, optionValue, optionFold]
    have hstep := optionStep_beforeTarget c tail.first
      (firstZ (.cons c K tail) z) (firstZ tail (tailZ c tail z))
      K (junctionZ c tail z) (initialOptions (cornerFirst (.cons c K tail) z) left)
    change _ = goodFactor c (firstZ (.cons c K tail) z) * cornerFactor tail (tailZ c tail z) *
      ((optionFold (cornerFirst tail (tailZ c tail z))
        (optionStep (cornerFirst (.cons c K tail) z) (cornerFirst tail (tailZ c tail z))
          K (junctionZ c tail z) (initialOptions (cornerFirst (.cons c K tail) z) left))
        (cornerEdges tail (tailZ c tail z))).2.1 * right.1 +
       (optionFold (cornerFirst tail (tailZ c tail z))
        (optionStep (cornerFirst (.cons c K tail) z) (cornerFirst tail (tailZ c tail z))
          K (junctionZ c tail z) (initialOptions (cornerFirst (.cons c K tail) z) left))
        (cornerEdges tail (tailZ c tail z))).2.2 * right.2)
    change optionStep (cornerFirst (.cons c K tail) z)
        (cornerFirst tail (tailZ c tail z)) K (junctionZ c tail z)
        (initialOptions (cornerFirst (.cons c K tail) z) left) =
      initialOptions (cornerFirst tail (tailZ c tail z))
        (beforeTarget c tail.first K (junctionZ c tail z)
          (initialOptions (cornerFirst (.cons c K tail) z) left)) at hstep
    rw [hstep]
    ring

theorem firstZ_isSign (ch : Chain) (z : ChargeEdges ch.sizes → ℝ)
    (hz : ∀ e, IsSign (z e)) : ∀ e, IsSign (firstZ ch z e) := by
  cases ch with
  | last c => exact hz
  | cons c K tail => cases tail <;> exact fun e => hz (.inl e)

theorem tailZ_isSign (c : ChargedSite) (tail : Chain)
    (z : ChargeEdges (c.size :: tail.sizes) → ℝ) (hz : ∀ e, IsSign (z e)) :
    ∀ e, IsSign (tailZ c tail z e) := by
  cases tail <;> exact fun e => hz (.inr (.inr e))

theorem junctionZ_isSign (c : ChargedSite) (tail : Chain)
    (z : ChargeEdges (c.size :: tail.sizes) → ℝ) (hz : ∀ e, IsSign (z e)) :
    IsSign (junctionZ c tail z) := by
  cases tail <;> exact hz (.inr (.inl ()))

theorem cornerEdges_admissible (ch : Chain) (hc : ch.Admissible)
    (z : ChargeEdges ch.sizes → ℝ) (hz : ∀ e, IsSign (z e)) :
    ∀ e ∈ cornerEdges ch z, e.Admissible := by
  induction ch with
  | last c => simp [cornerEdges]
  | cons c K tail ih =>
    rcases hc with ⟨hK, ht⟩
    intro e he
    simp only [cornerEdges, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨cornerSite_admissible tail.first (firstZ tail (tailZ c tail z))
        (firstZ_isSign tail _ (tailZ_isSign c tail z hz)), hK,
        junctionZ_isSign c tail z hz⟩
    · exact ih ht (tailZ c tail z) (tailZ_isSign c tail z hz) e he

theorem cornerFactor_nonnegative (ch : Chain) (z : ChargeEdges ch.sizes → ℝ)
    (hz : ∀ e, IsSign (z e)) : 0 ≤ cornerFactor ch z := by
  induction ch with
  | last c => exact goodFactor_nonnegative c z hz
  | cons c K tail ih =>
    exact mul_nonneg (goodFactor_nonnegative c _ (firstZ_isSign (.cons c K tail) z hz))
      (ih (tailZ c tail z) (tailZ_isSign c tail z hz))

theorem affineModel_corner_nonnegative (ch : Chain) (left right : ℝ × ℝ)
    (hl : Free left) (hr : Free right) (hc : ch.Admissible)
    (ε : ChargeEdges ch.sizes → Bool) :
    0 ≤ affineModel ch left right (fun e => SignExpansion.sign (ε e)) := by
  let z : ChargeEdges ch.sizes → ℝ := fun e => SignExpansion.sign (ε e)
  have hz : ∀ e, IsSign (z e) := fun e => sign_isSign (ε e)
  rw [affineModel_eq_corner]
  exact mul_nonneg (cornerFactor_nonnegative ch z hz)
    (options_nonnegative (cornerFirst ch z)
      (cornerSite_admissible ch.first (firstZ ch z) (firstZ_isSign ch z hz))
      left right hl hr (cornerEdges ch z) (cornerEdges_admissible ch hc z hz))

end
end R34.ReducedCharge
