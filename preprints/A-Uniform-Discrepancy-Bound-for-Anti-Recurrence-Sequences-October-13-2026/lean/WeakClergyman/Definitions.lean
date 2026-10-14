import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace WeakClergyman

/-- The original complementary positive integer sequences, indexed from zero. -/
structure AntiRecurrence (k : ℕ) (a : Fin k → ℕ) where
  A : ℕ → ℕ
  B : ℕ → ℕ
  A_pos : ∀ n, 0 < A n
  B_pos : ∀ n, 0 < B n
  A_strictMono : StrictMono A
  B_strictMono : StrictMono B
  complementary : ∀ t, 0 < t → ((∃ n, A n = t) ↔ ¬ ∃ n, B n = t)
  recurrence : ∀ n, A n = ∑ j : Fin k, a j * B (k * n + j.val)

/-- Values of a sequence strictly below a natural threshold. -/
noncomputable def valuesBelow (f : ℕ → ℕ) (b : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range b).filter fun x => ∃ i, f i = x

@[simp] theorem mem_valuesBelow (f : ℕ → ℕ) (b x : ℕ) :
    x ∈ valuesBelow f b ↔ x < b ∧ ∃ i, f i = x := by
  classical
  simp [valuesBelow]

 theorem index_le_value {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : n ≤ f n :=
  hf.id_le n

 theorem valuesBelow_at {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) :
    valuesBelow f (f n) = (Finset.range n).image f := by
  classical
  ext x
  simp only [mem_valuesBelow, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hx, i, rfl⟩
    exact ⟨i, hf.lt_iff_lt.mp hx, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hf hi, i, rfl⟩

 theorem card_valuesBelow_at {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) :
    (valuesBelow f (f n)).card = n := by
  classical
  rw [valuesBelow_at hf, Finset.card_image_of_injective _ hf.injective,
    Finset.card_range]

 theorem valuesBelow_mono (f : ℕ → ℕ) {b c : ℕ} (h : b ≤ c) :
    valuesBelow f b ⊆ valuesBelow f c := by
  intro x hx
  obtain ⟨hx, hi⟩ := mem_valuesBelow _ _ _ |>.mp hx
  exact (mem_valuesBelow _ _ _).mpr ⟨lt_of_lt_of_le hx h, hi⟩

 theorem card_valuesBelow_le {f : ℕ → ℕ} (hf : StrictMono f)
    {b n : ℕ} (h : b ≤ f n) : (valuesBelow f b).card ≤ n := by
  rw [← card_valuesBelow_at hf n]
  exact Finset.card_le_card (valuesBelow_mono f h)

 theorem card_valuesBelow_gt {f : ℕ → ℕ} (hf : StrictMono f)
    {b n : ℕ} (h : f n < b) : n < (valuesBelow f b).card := by
  classical
  have hs : (Finset.range (n+1)).image f ⊆ valuesBelow f b := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_valuesBelow _ _ _).mpr
    exact ⟨lt_of_le_of_lt (hf.monotone (by have := Finset.mem_range.mp hi; omega)) h, i, rfl⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hf.injective, Finset.card_range] at hc
  omega

 theorem rank_bracket {f : ℕ → ℕ} (hf : StrictMono f) (b : ℕ) :
    b ≤ f (valuesBelow f b).card ∧
      (∀ i, i < (valuesBelow f b).card → f i < b) := by
  constructor
  · by_contra h
    have := card_valuesBelow_gt hf (Nat.lt_of_not_ge h)
    omega
  · intro i hi
    by_contra h
    have := card_valuesBelow_le hf (Nat.le_of_not_gt h)
    omega

end WeakClergyman
