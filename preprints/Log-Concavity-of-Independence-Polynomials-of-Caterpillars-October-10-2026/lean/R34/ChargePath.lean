import R34.SchurChainEquiv
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace R34

open MvPolynomial
open scoped BigOperators

@[reducible] def ChargeColorings : List ℕ → Type
  | [] => PUnit
  | a :: as => (Fin a → Bool) × ChargeColorings as

@[reducible] def ChargeEdges : List ℕ → Type
  | [] => Empty
  | [a] => Fin (a-1)
  | a :: b :: as => Fin (a-1) ⊕ (Unit ⊕ ChargeEdges (b :: as))

instance chargeColoringsFintype (sizes : List ℕ) : Fintype (ChargeColorings sizes) := by
  induction sizes with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons a as ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Fin a → Bool) × ChargeColorings as))

instance chargeEdgesFintype (sizes : List ℕ) : Fintype (ChargeEdges sizes) := by
  induction sizes with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons a as ih =>
    cases as with
    | nil => exact inferInstanceAs (Fintype (Fin (a-1)))
    | cons b as =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin (a-1) ⊕ (Unit ⊕ ChargeEdges (b :: as))))

def internalChargeEndpoints (a : ℕ) (χ : Fin a → Bool) (e : Fin (a-1)) : Bool × Bool :=
  (χ ⟨e.val, by omega⟩, χ ⟨e.val+1, by omega⟩)

def chargeFirst : (sizes : List ℕ) → (∀ a ∈ sizes, 0 < a) → ChargeColorings sizes → Bool
  | [], _, _ => false
  | a :: as, hs, χ => χ.1 ⟨0, hs a (by simp)⟩

def chargeLast : (sizes : List ℕ) → (∀ a ∈ sizes, 0 < a) → ChargeColorings sizes → Bool
  | [], _, _ => false
  | [a], hs, χ => χ.1 ⟨a-1, by have ha := hs a (by simp); omega⟩
  | a :: b :: as, hs, χ => chargeLast (b :: as) (fun x hx => hs x (by simp [hx])) χ.2

def chargeEndpoints : (sizes : List ℕ) → (∀ a ∈ sizes, 0 < a) →
    ChargeColorings sizes → ChargeEdges sizes → Bool × Bool
  | [], _, _, e => Empty.elim e
  | [a], _, χ, e => internalChargeEndpoints a χ.1 e
  | a :: b :: as, hs, χ, e =>
    match e with
    | Sum.inl i => internalChargeEndpoints a χ.1 i
    | Sum.inr (Sum.inl _) =>
      (χ.1 ⟨a-1, by have ha := hs a (by simp); omega⟩,
        chargeFirst (b :: as) (fun x hx => hs x (by simp [hx])) χ.2)
    | Sum.inr (Sum.inr e) =>
      chargeEndpoints (b :: as) (fun x hx => hs x (by simp [hx])) χ.2 e

def chargeWeight : (sizes : List ℕ) → ChargeColorings sizes → Poly
  | [], _ => 1
  | a :: as, χ => (∏ i : Fin a, color (χ.1 i)) * chargeWeight as χ.2

def chargeTerm (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) (χ : ChargeColorings sizes) : Poly :=
  chargeWeight sizes χ * C (∏ e : ChargeEdges sizes,
    edgeWeight (coupling e) (chargeEndpoints sizes hs χ e).1
      (chargeEndpoints sizes hs χ e).2)

def blockChainSum (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) : Poly := ∑ χ : ChargeColorings sizes,
  chargeTerm sizes hs coupling χ

def chargeCouplingList : (sizes : List ℕ) → (ChargeEdges sizes → ℝ) → List ℝ
  | [], _ => []
  | [_a], coupling => List.ofFn coupling
  | a :: b :: as, coupling =>
    List.ofFn (fun e : Fin (a-1) => coupling (Sum.inl e)) ++
      coupling (Sum.inr (Sum.inl ())) ::
        chargeCouplingList (b :: as) (fun e => coupling (Sum.inr (Sum.inr e)))

def singleChargeTerm (a : ℕ) (coupling : Fin (a-1) → ℝ) (χ : Fin a → Bool) : Poly :=
  (∏ i : Fin a, color (χ i)) * C (∏ e : Fin (a-1),
    edgeWeight (coupling e) (internalChargeEndpoints a χ e).1
      (internalChargeEndpoints a χ e).2)

def pathTensor {ι : Type} [Fintype ι] (first last : ι → Bool) (weight : ι → Poly) :
    ColorMatrix := fun a b => ∑ χ : ι,
      if first χ = a then if last χ = b then weight χ else 0 else 0

def singleChargeTensor (a : ℕ) (ha : 0 < a) (coupling : Fin (a-1) → ℝ) : ColorMatrix :=
  pathTensor (fun χ : Fin a → Bool => χ ⟨0, ha⟩)
    (fun χ => χ ⟨a-1, by omega⟩) (singleChargeTerm a coupling)

def chargeTensor (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) : ColorMatrix :=
  pathTensor (chargeFirst sizes hs) (chargeLast sizes hs) (chargeTerm sizes hs coupling)

theorem pathTensor_total {ι : Type} [Fintype ι] (first last : ι → Bool)
    (weight : ι → Poly) : matrixTotal (pathTensor first last weight) = ∑ χ : ι, weight χ := by
  classical
  unfold matrixTotal pathTensor
  calc
    _ = ∑ a : Bool, ∑ χ : ι, ∑ b : Bool,
        if first χ = a then if last χ = b then weight χ else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ χ : ι, ∑ a : Bool, ∑ b : Bool,
        if first χ = a then if last χ = b then weight χ else 0 else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      simp

theorem pathTensor_mul_apply {ι : Type} [Fintype ι] (first last : ι → Bool)
    (weight : ι → Poly) (A : ColorMatrix) (a b : Bool) :
    (pathTensor first last weight * A) a b =
      ∑ χ : ι, if first χ = a then weight χ * A (last χ) b else 0 := by
  classical
  simp only [Matrix.mul_apply, pathTensor, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases h : first χ = a <;> simp [h, ite_mul]

theorem mul_pathTensor_apply {ι : Type} [Fintype ι] (first last : ι → Bool)
    (weight : ι → Poly) (A : ColorMatrix) (a b : Bool) :
    (A * pathTensor first last weight) a b =
      ∑ χ : ι, if last χ = b then A a (first χ) * weight χ else 0 := by
  classical
  simp only [Matrix.mul_apply, pathTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases h : last χ = b <;> simp [h, mul_ite]

theorem pathTensor_join {ι κ : Type} [Fintype ι] [Fintype κ]
    (first last : ι → Bool) (first' last' : κ → Bool)
    (weight : ι → Poly) (weight' : κ → Poly) (A : ColorMatrix) :
    pathTensor first last weight * A * pathTensor first' last' weight' =
      pathTensor (fun χ : ι × κ => first χ.1) (fun χ => last' χ.2)
        (fun χ => weight χ.1 * A (last χ.1) (first' χ.2) * weight' χ.2) := by
  classical
  funext a b
  rw [mul_pathTensor_apply]
  simp only [pathTensor_mul_apply, pathTensor, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ' hχ'
  by_cases h : last' χ' = b
  · simp only [h, ite_true, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    by_cases hh : first χ = a <;> simp [hh]
  · simp [h]

theorem chargeEdges_prod_join {R : Type} [CommMonoid R] (a b : ℕ) (as : List ℕ)
    (f : ChargeEdges (a :: b :: as) → R) :
    (∏ e, f e) = (∏ e : Fin (a-1), f (Sum.inl e)) *
      f (Sum.inr (Sum.inl ())) *
        (∏ e : ChargeEdges (b :: as), f (Sum.inr (Sum.inr e))) := by
  change (∏ e : Fin (a-1) ⊕ (Unit ⊕ ChargeEdges (b :: as)), f e) = _
  simp [Fintype.prod_sum_type, mul_assoc]

theorem chargeColorings_sum_cons {R : Type} [AddCommMonoid R] (a : ℕ) (as : List ℕ)
    (f : ChargeColorings (a :: as) → R) :
    (∑ χ, f χ) = ∑ χ : Fin a → Bool, ∑ ψ : ChargeColorings as, f (χ, ψ) := by
  change (∑ χ : (Fin a → Bool) × ChargeColorings as, f χ) = _
  exact Fintype.sum_prod_type _

theorem chargeColorings_sum_nil {R : Type} [AddCommMonoid R]
    (f : ChargeColorings [] → R) : (∑ χ, f χ) = f PUnit.unit := by
  change (∑ χ : PUnit, f χ) = _
  exact Fintype.sum_unique _

theorem chargeTerm_join (a b : ℕ) (as : List ℕ) (hs : ∀ x ∈ a :: b :: as, 0 < x)
    (coupling : ChargeEdges (a :: b :: as) → ℝ)
    (χ : ChargeColorings (a :: b :: as)) :
    chargeTerm (a :: b :: as) hs coupling χ =
      singleChargeTerm a (fun e => coupling (Sum.inl e)) χ.1 *
        C (edgeWeight (coupling (Sum.inr (Sum.inl ())))
          (χ.1 ⟨a-1, by have ha := hs a (by simp); omega⟩)
          (chargeFirst (b :: as) (fun x hx => hs x (by simp [hx])) χ.2)) *
        chargeTerm (b :: as) (fun x hx => hs x (by simp [hx]))
          (fun e => coupling (Sum.inr (Sum.inr e))) χ.2 := by
  classical
  unfold chargeTerm singleChargeTerm
  rw [chargeEdges_prod_join]
  simp only [chargeWeight, chargeEndpoints, C_mul]
  ring

theorem chargeTensor_join (a b : ℕ) (as : List ℕ) (hs : ∀ x ∈ a :: b :: as, 0 < x)
    (coupling : ChargeEdges (a :: b :: as) → ℝ) :
    chargeTensor (a :: b :: as) hs coupling =
      singleChargeTensor a (hs a (by simp)) (fun e => coupling (Sum.inl e)) *
        interaction (coupling (Sum.inr (Sum.inl ()))) *
          chargeTensor (b :: as) (fun x hx => hs x (by simp [hx]))
            (fun e => coupling (Sum.inr (Sum.inr e))) := by
  classical
  unfold chargeTensor singleChargeTensor
  rw [pathTensor_join]
  funext u v
  unfold pathTensor
  apply Finset.sum_congr rfl
  intro χ hχ
  simp only [chargeFirst, chargeLast, chargeTerm_join, interaction]

theorem chargeTensor_singleton (a : ℕ) (hs : ∀ x ∈ [a], 0 < x)
    (coupling : ChargeEdges [a] → ℝ) :
    chargeTensor [a] hs coupling = singleChargeTensor a (hs a (by simp)) coupling := by
  classical
  funext u v
  unfold chargeTensor singleChargeTensor pathTensor
  rw [chargeColorings_sum_cons]
  simp [ChargeColorings,
    chargeFirst, chargeLast, chargeTerm, chargeWeight, singleChargeTerm,
    chargeEndpoints]

theorem blockChainSum_eq_tensorTotal (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) :
    blockChainSum sizes hs coupling = matrixTotal (chargeTensor sizes hs coupling) := by
  exact (pathTensor_total _ _ _).symm

theorem chargeCouplingList_bounds (sizes : List ℕ) (coupling : ChargeEdges sizes → ℝ)
    (hc : ∀ e, 0 ≤ coupling e ∧ coupling e ≤ 2) :
    ∀ x ∈ chargeCouplingList sizes coupling, 0 ≤ x ∧ x ≤ 2 := by
  induction sizes with
  | nil => simp [chargeCouplingList]
  | cons a as ih =>
    cases as with
    | nil =>
      intro x hx
      obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hx
      exact hc e
    | cons b as =>
      intro x hx
      simp only [chargeCouplingList, List.mem_append, List.mem_cons, List.mem_ofFn] at hx
      rcases hx with ⟨e, rfl⟩ | rfl | hx
      · exact hc (Sum.inl e)
      · exact hc (Sum.inr (Sum.inl ()))
      · exact ih (fun e => coupling (Sum.inr (Sum.inr e)))
          (fun e => hc (Sum.inr (Sum.inr e))) x hx

theorem singleChargeTerm_succ (n : ℕ) (coupling : Fin n → ℝ)
    (χ : Fin (n+1) → Bool) :
    singleChargeTerm (n+1) coupling χ = chainWeight n coupling χ := by
  rfl

theorem singleChargeTensor_eq_chainMatrix (a : ℕ) (ha : 0 < a)
    (coupling : Fin (a-1) → ℝ) :
    singleChargeTensor a ha coupling = chainMatrix (List.ofFn coupling) := by
  classical
  cases a with
  | zero => omega
  | succ n =>
    funext u v
    rw [chainMatrix_endpointSum]
    unfold singleChargeTensor pathTensor
    rw [sum_colors_succ]
    cases u <;>
      simp [Fin.cons_zero, singleChargeTerm_succ, endpointChainSum, mul_ite] <;> rfl

theorem chargeTensor_eq_chainMatrix (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) (hne : sizes ≠ []) :
    chargeTensor sizes hs coupling = chainMatrix (chargeCouplingList sizes coupling) := by
  induction sizes with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
    cases as with
    | nil =>
      rw [chargeTensor_singleton, singleChargeTensor_eq_chainMatrix]
      rfl
    | cons b as =>
      rw [chargeTensor_join, singleChargeTensor_eq_chainMatrix,
        ih (fun x hx => hs x (by simp [hx]))
          (fun e => coupling (Sum.inr (Sum.inr e))) (by simp)]
      exact (chainMatrix_append_edge _ _ _).symm

theorem blockChainSum_nil (hs : ∀ a ∈ ([] : List ℕ), 0 < a)
    (coupling : ChargeEdges [] → ℝ) : blockChainSum [] hs coupling = 1 := by
  classical
  unfold blockChainSum
  rw [chargeColorings_sum_nil]
  simp [chargeTerm, chargeWeight]

theorem blockChainSum_eq_listChain (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) (hne : sizes ≠ []) :
    blockChainSum sizes hs coupling = listChain (chargeCouplingList sizes coupling) := by
  rw [blockChainSum_eq_tensorTotal, chargeTensor_eq_chainMatrix sizes hs coupling hne]
  rfl

/-- Positive charge blocks give a Schur-positive colored path for every coupling in `[0,2]`. -/
theorem blockChainSum_schurPositive (sizes : List ℕ) (hs : ∀ a ∈ sizes, 0 < a)
    (coupling : ChargeEdges sizes → ℝ) (hc : ∀ e, 0 ≤ coupling e ∧ coupling e ≤ 2) :
    SchurPositive (blockChainSum sizes hs coupling) := by
  by_cases hne : sizes = []
  · subst sizes
    rw [blockChainSum_nil]
    exact schurPositive_one
  · rw [blockChainSum_eq_listChain sizes hs coupling hne]
    exact listChain_schurPositive_of_uniform uniform_chain_schurPositive
      _ (chargeCouplingList_bounds sizes coupling hc)

end R34
