import GenericValueSemigroups.WeightCounting
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- Stars and bars for the actual strict monomial counting function. -/
theorem unit_weightCount (d n : ℕ) :
    weightCount (fun _ : Fin d => 1) (n+1) = (n+d).choose d := by
  let f : (Fin d → ℕ) → (Fin (d+1) →₀ ℕ) := fun α =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (n-∑ i, α i) α)
  have hf : (weightSet (fun _ : Fin d => 1) (n+1)).card =
      ((Finset.univ : Finset (Fin (d+1))).finsuppAntidiag n).card := by
    apply Finset.card_bij (fun α _ => f α)
    · intro α hα
      have ha : (∑ i, α i) ≤ n := by
        have := (mem_weightSet (fun _ : Fin d => 1) (by simp) (n+1) α).mp hα
        simpa [weight, Nat.lt_succ_iff] using this
      simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
      simp [f, Fin.sum_univ_succ, Nat.sub_add_cancel ha]
    · intro α hα β hβ he
      funext i
      have := DFunLike.congr_fun he i.succ
      simpa [f] using this
    · intro β hβ
      have hb := (Finset.mem_finsuppAntidiag.mp hβ).1
      rw [Fin.sum_univ_succ] at hb
      let α : Fin d → ℕ := fun i => β i.succ
      have ha : α ∈ weightSet (fun _ : Fin d => 1) (n+1) := by
        rw [mem_weightSet _ (by simp)]
        simp only [weight, mul_one]
        dsimp [α]
        omega
      refine ⟨α,ha,?_⟩
      apply Finsupp.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [f, Finsupp.equivFunOnFinite_symm_apply_apply, Fin.cons_zero]
        dsimp [α]
        omega
      · simp [f,α]
  change (weightSet (fun _ : Fin d => 1) (n+1)).card = _
  rw [hf, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have he : d+1+n-1=d+n := by omega
  rw [he, Nat.add_comm d n, Nat.choose_symm_add]

/-- The finite residue box for the coordinatewise Euclidean division map. -/
noncomputable def residueBox {d : ℕ} (r : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (r i))

@[simp] theorem mem_residueBox {d : ℕ} (r β : Fin d → ℕ) :
    β ∈ residueBox r ↔ ∀ i, β i < r i := by
  simp [residueBox, Fintype.mem_piFinset]

@[simp] theorem card_residueBox {d : ℕ} (r : Fin d → ℕ) :
    (residueBox r).card = ∏ i, r i := by
  simp [residueBox, Fintype.card_piFinset]

/-- Replace each weighted lattice point by its full integral residue box. -/
noncomputable def expandedWeightSet {d : ℕ} (r : Fin d → ℕ) (n : ℕ) :
    Finset (Fin d → ℕ) :=
  ((weightSet r n).product (residueBox r)).image (fun p i => p.1 i*r i+p.2 i)

theorem card_expandedWeightSet {d : ℕ} (r : Fin d → ℕ) (n : ℕ) :
    (expandedWeightSet r n).card = weightCount r n * ∏ i, r i := by
  unfold expandedWeightSet
  rw [Finset.card_image_of_injOn, Finset.product_eq_sprod, Finset.card_product, card_residueBox]
  rfl
  intro a ha b hb he
  have ha' := (mem_residueBox r a.2).mp (Finset.mem_product.mp ha).2
  have hb' := (mem_residueBox r b.2).mp (Finset.mem_product.mp hb).2
  have hdiv : a.1=b.1 := by
    funext i
    have hp : 0<r i := lt_of_le_of_lt (Nat.zero_le _) (ha' i)
    have hi := congrFun he i
    change a.1 i*r i+a.2 i=b.1 i*r i+b.2 i at hi
    have hh := congrArg (fun x => x/(r i)) hi
    simpa [Nat.mul_comm, Nat.mul_add_div hp, Nat.div_eq_of_lt (ha' i),
      Nat.div_eq_of_lt (hb' i)] using hh
  have hmod : a.2=b.2 := by
    funext i
    have hi := congrFun he i
    change a.1 i*r i+a.2 i=b.1 i*r i+b.2 i at hi
    rw [hdiv] at hi
    omega
  exact Prod.ext hdiv hmod

theorem unit_weightSet_subset_expanded {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (n : ℕ) :
    weightSet (fun _ : Fin d => 1) n ⊆ expandedWeightSet r n := by
  intro x hx
  have hx' : (∑ i, x i)<n := by
    simpa [weight] using (mem_weightSet (fun _ : Fin d => 1) (by simp) n x).mp hx
  let α : Fin d → ℕ := fun i => x i/r i
  let β : Fin d → ℕ := fun i => x i%r i
  have ha : α ∈ weightSet r n := by
    rw [mem_weightSet r hr]
    apply lt_of_le_of_lt _ hx'
    exact Finset.sum_le_sum (fun i _ => Nat.div_mul_le_self (x i) (r i))
  have hb : β ∈ residueBox r := by
    rw [mem_residueBox]
    exact fun i => Nat.mod_lt _ (hr i)
  apply Finset.mem_image.mpr
  refine ⟨(α,β),Finset.mem_product.mpr ⟨ha,hb⟩,?_⟩
  funext i
  exact Nat.div_add_mod' (x i) (r i)

theorem expanded_subset_unit_weightSet {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (n : ℕ) :
    expandedWeightSet r n ⊆ weightSet (fun _ : Fin d => 1) (n+∑ i, (r i-1)) := by
  intro x hx
  obtain ⟨⟨α,β⟩,hαβ,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hα,hβ⟩ := Finset.mem_product.mp hαβ
  have ha := (mem_weightSet r hr n α).mp hα
  have hb := (mem_residueBox r β).mp hβ
  rw [mem_weightSet _ (by simp)]
  simp only [weight, mul_one, Finset.sum_add_distrib]
  have hs : (∑ i, β i) ≤ ∑ i, (r i-1) :=
    Finset.sum_le_sum (fun i _ => by have := hb i; omega)
  change (∑ i, α i*r i)<n at ha
  omega

/-- Exact finite-count form of the lower simplex volume bound. -/
theorem weightCount_lower_factorial {d : ℕ} (hd : 0<d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (n : ℕ) :
    n^d ≤ d.factorial * (∏ i, r i) * weightCount r n := by
  cases n with
  | zero => simp [Nat.ne_of_gt hd]
  | succ n =>
    have hc := Finset.card_le_card (unit_weightSet_subset_expanded r hr (n+1))
    change weightCount (fun _ : Fin d => 1) (n+1) ≤ _ at hc
    rw [unit_weightCount, card_expandedWeightSet] at hc
    have hp := (n+d).pow_sub_le_descFactorial d
    have he : n+d+1-d=n+1 := by omega
    rw [he,Nat.descFactorial_eq_factorial_mul_choose] at hp
    calc
      (n+1)^d ≤ d.factorial * (n+d).choose d := hp
      _ ≤ d.factorial * (weightCount r (n+1) * ∏ i, r i) := Nat.mul_le_mul_left _ hc
      _ = _ := by ring

/-- Exact finite-count form of the upper simplex volume bound. -/
theorem weightCount_upper_factorial {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (n : ℕ) :
    d.factorial * (∏ i, r i) * weightCount r n ≤ (n+∑ i, r i)^d := by
  cases n with
  | zero => simp
  | succ n =>
    have hs : (∑ i, (r i-1))+d=∑ i, r i := by
      have hp : ∀ i, (r i-1)+1=r i := fun i => by have := hr i; omega
      have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin d))) rfl
        (fun i _ => hp i)
      simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] using he
    have hc := Finset.card_le_card (expanded_subset_unit_weightSet r hr (n+1))
    change _ ≤ weightCount (fun _ : Fin d => 1) ((n+1)+∑ i, (r i-1)) at hc
    rw [show (n+1)+(∑ i, (r i-1)) = (n+∑ i, (r i-1))+1 by omega,
      unit_weightCount, card_expandedWeightSet] at hc
    have he : n+(∑ i, (r i-1))+d=n+∑ i, r i := by omega
    rw [he] at hc
    calc
      d.factorial * (∏ i, r i) * weightCount r (n+1) =
          d.factorial * (weightCount r (n+1) * ∏ i, r i) := by ring
      _ ≤ d.factorial * (n+∑ i, r i).choose d := Nat.mul_le_mul_left _ hc
      _ = (n+∑ i, r i).descFactorial d := (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ (n+∑ i, r i)^d := Nat.descFactorial_le_pow _ _
      _ ≤ ((n+1)+∑ i, r i)^d := Nat.pow_le_pow_left (by omega) d

end GenericValueSemigroups
