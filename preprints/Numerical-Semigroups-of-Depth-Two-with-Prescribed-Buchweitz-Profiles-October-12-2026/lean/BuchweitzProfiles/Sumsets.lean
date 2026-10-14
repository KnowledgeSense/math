import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

open scoped Pointwise

namespace BuchweitzProfiles

/-- The genuine iterated sumset, with repetitions allowed. -/
def sumset (C : Finset Nat) : Nat → Finset Nat
  | 0 => {0}
  | n + 1 => sumset C n + C

@[simp] theorem sumset_zero (C : Finset Nat) : sumset C 0 = {0} := rfl
@[simp] theorem sumset_succ (C : Finset Nat) (n : Nat) :
    sumset C (n + 1) = sumset C n + C := rfl
@[simp] theorem sumset_one (C : Finset Nat) : sumset C 1 = C := by
  ext x
  simp [sumset, Finset.mem_add]

/-- The count of actual sums strictly below the multiplicity. -/
def truncatedCount (C : Finset Nat) (m n : Nat) : Nat :=
  ((sumset C n).filter (· < m)).card

lemma mem_sumset_succ {C : Finset Nat} {n x : Nat} :
    x ∈ sumset C (n + 1) ↔ ∃ a ∈ sumset C n, ∃ b ∈ C, a + b = x := by
  exact Finset.mem_add

lemma sumset_mono {C D : Finset Nat} (h : C ⊆ D) (n : Nat) :
    sumset C n ⊆ sumset D n := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sumset_succ.mp hx
    exact mem_sumset_succ.mpr ⟨a, ih ha, b, h hb, rfl⟩

lemma sumset_bound {C : Finset Nat} {b : Nat} (h : ∀ c ∈ C, c ≤ b)
    (n : Nat) {x : Nat} (hx : x ∈ sumset C n) : x ≤ n * b := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sumset_succ.mp hx
    have ha' := ih ha
    have hc' := h c hc
    rw [Nat.succ_mul]
    omega

lemma zero_mem_sumset {C : Finset Nat} (hz : 0 ∈ C) (n : Nat) :
    0 ∈ sumset C n := by
  induction n with
  | zero => simp
  | succ n ih => exact mem_sumset_succ.mpr ⟨0, ih, 0, hz, rfl⟩

/-- The interval-filling identity of Lemma 2.2, proved for all orders. -/
theorem sumset_with_interval (C : Finset Nat) (m : Nat) (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) (hz : 0 ∈ C)
    (hpos : ∃ γ ∈ C, 0 < γ) (n : Nat) (hn : 1 ≤ n) :
    sumset (C ∪ Finset.Icc m (2 * m - 2)) n =
      sumset C n ∪ Finset.Icc m (2 * n * (m - 1)) := by
  obtain ⟨γ, hγ, hγpos⟩ := hpos
  have hγbound := hC γ hγ
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [sumset_one]
    congr 2
    omega
  | succ n hn ih =>
    apply Finset.ext
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sumset_succ.mp hx
      rw [ih] at ha
      simp only [Finset.mem_union, Finset.mem_Icc] at ha hb ⊢
      have hupper : 2 * (n + 1) * (m - 1) = 2 * n * (m - 1) + 2 * m - 2 := by
        calc
          _ = 2 * n * (m - 1) + 2 * (m - 1) := by ring
          _ = _ := by omega
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (mem_sumset_succ.mpr ⟨a, ha, b, hb, rfl⟩)
      · right
        have habound := sumset_bound hC n ha
        have hsmall : n * (m - 2) ≤ 2 * n * (m - 1) := by
          apply Nat.mul_le_mul
          · omega
          · omega
        omega
      · right
        have hb' := hC b hb
        omega
      · right; omega
    · intro hx
      simp only [Finset.mem_union, Finset.mem_Icc] at hx
      rcases hx with hx | ⟨hxm, hxmax⟩
      · exact sumset_mono Finset.subset_union_left (n + 1) hx
      · have hupper : 2 * (n + 1) * (m - 1) = 2 * n * (m - 1) + 2 * m - 2 := by
          calc
            _ = 2 * n * (m - 1) + 2 * (m - 1) := by ring
            _ = _ := by omega
        have hbase : 2 * m - 2 ≤ 2 * n * (m - 1) := by
          have hh := Nat.mul_le_mul_right (2 * (m - 1)) hn
          have he : n * (2 * (m - 1)) = 2 * n * (m - 1) := by ring
          omega
        have build (a b : Nat) (ha : m ≤ a ∧ a ≤ 2 * n * (m - 1))
            (hb : b ∈ C ∪ Finset.Icc m (2 * m - 2)) (hab : a + b = x) :
            x ∈ sumset (C ∪ Finset.Icc m (2 * m - 2)) (n + 1) := by
          apply mem_sumset_succ.mpr
          refine ⟨a, ?_, b, hb, hab⟩
          rw [ih]
          exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ha)
        by_cases hlow : x ≤ 2 * n * (m - 1)
        · exact build x 0 ⟨hxm, hlow⟩ (Finset.mem_union_left _ hz) (by omega)
        by_cases htwo : x < 2 * m
        · exact build (x - γ) γ (by omega) (Finset.mem_union_left _ hγ) (by omega)
        by_cases hmid : x - m ≤ 2 * n * (m - 1)
        · exact build (x - m) m (by omega)
            (Finset.mem_union_right _ (Finset.mem_Icc.mpr (by omega))) (by omega)
        · exact build (2 * n * (m - 1)) (x - 2 * n * (m - 1)) (by omega)
            (Finset.mem_union_right _ (Finset.mem_Icc.mpr (by omega))) (by omega)

end BuchweitzProfiles
