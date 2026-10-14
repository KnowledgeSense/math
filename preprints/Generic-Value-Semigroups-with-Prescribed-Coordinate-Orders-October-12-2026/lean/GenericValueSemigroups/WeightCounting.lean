import GenericValueSemigroups.WeightEnumeration
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- Number of nonnegative multiples of a below half the weight bound. -/
def halfCount (n a : ℕ) : ℕ := (n-1)/(2*a)+1

theorem halfCount_multiple_lt {n a k : ℕ} (hn : 0 < n) (ha : 0 < a)
    (hk : k < halfCount n a) : 2*(k*a) < n := by
  have hh : k ≤ (n-1)/(2*a) := by unfold halfCount at hk; omega
  have hp := (Nat.le_div_iff_mul_le (by omega : 0 < 2*a)).mp hh
  have hs : n-1 < n := Nat.sub_lt hn (by decide)
  nlinarith

theorem le_twice_mul_halfCount {n a : ℕ} (hn : 0 < n) (ha : 0 < a) :
    n ≤ 2*a*halfCount n a := by
  have hh := Nat.lt_mul_div_succ (n-1) (by omega : 0 < 2*a)
  change n ≤ 2*a*((n-1)/(2*a)+1)
  omega

theorem weight_pair {d : ℕ} (r : Fin d → ℕ) (i j : Fin d) (hij : i ≠ j)
    (u v : ℕ) :
    weight r (Function.update (Function.update (fun _ => 0) i u) j v) = u*r i+v*r j := by
  have hf : ∀ x : Fin d,
      Function.update (Function.update (fun _ => 0) i u) j v x * r x =
        (if x=i then u*r i else 0) + (if x=j then v*r j else 0) := by
    intro x
    by_cases hxi : x=i
    · subst x
      simp [hij]
    · by_cases hxj : x=j
      · subst x
        simp [hxi]
      · simp [hxi, hxj]
  unfold weight
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp

/-- A rectangular family of two-coordinate monomials gives the quadratic lower bound. -/
theorem rectangle_le_weightCount {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (i j : Fin d) (hij : i ≠ j) {n : ℕ} (hn : 0 < n) :
    halfCount n (r i) * halfCount n (r j) ≤ weightCount r n := by
  let f : ℕ × ℕ → (Fin d → ℕ) := fun p =>
    Function.update (Function.update (fun _ => 0) i p.1) j p.2
  have hf : Function.Injective f := by
    intro a b hab
    have hi := congrFun hab i
    have hj := congrFun hab j
    apply Prod.ext
    · simpa [f, Function.update_of_ne hij] using hi
    · simpa [f] using hj
  have hsub : ((Finset.range (halfCount n (r i))).product
      (Finset.range (halfCount n (r j)))).image f ⊆ weightSet r n := by
    intro α hα
    obtain ⟨⟨u,v⟩, hp, rfl⟩ := Finset.mem_image.mp hα
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
    rw [mem_weightSet r hr]
    change weight r (Function.update (Function.update (fun _ => 0) i u) j v) < n
    rw [weight_pair r i j hij]
    have hb1 := halfCount_multiple_lt hn (hr i) (Finset.mem_range.mp hu)
    have hb2 := halfCount_multiple_lt hn (hr j) (Finset.mem_range.mp hv)
    change 2*(u*r i) < n at hb1
    change 2*(v*r j) < n at hb2
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_range, Finset.card_range] at hc
  exact hc

theorem quadratic_weightCount_bound {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (i j : Fin d) (hij : i ≠ j) (n : ℕ) :
    n*n ≤ 4*r i*r j*weightCount r n := by
  by_cases hn : n=0
  · simp [hn]
  have hnp : 0<n := by omega
  have h1 := le_twice_mul_halfCount hnp (hr i)
  have h2 := le_twice_mul_halfCount hnp (hr j)
  have hmul := Nat.mul_le_mul h1 h2
  have hrct := rectangle_le_weightCount r hr i j hij hnp
  have hscale := Nat.mul_le_mul_left (4*r i*r j) hrct
  nlinarith

theorem weightCount_ge_above_cutoff {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (i j : Fin d) (hij : i ≠ j) {n : ℕ} (hn : 4*r i*r j ≤ n) :
    n ≤ weightCount r n := by
  have hc := quadratic_weightCount_bound r hr i j hij n
  have hp : 0 < 4*r i*r j := Nat.mul_pos (Nat.mul_pos (by decide) (hr i)) (hr j)
  nlinarith

end GenericValueSemigroups
