import BuchweitzProfiles.Sumsets
import BuchweitzProfiles.DepthTwo
import Mathlib.Data.Finset.Card

open scoped Pointwise

namespace BuchweitzProfiles

/-- Reflection about an integer endpoint. All applications prove the required bounds. -/
def reflect (f : Nat) (C : Finset Nat) : Finset Nat := C.image (f - ·)

/-- The finite gapset of the constructed depth-two numerical semigroup. -/
def gapset (m : Nat) (C : Finset Nat) : Finset Nat :=
  Finset.Icc 1 (m - 1) ∪ reflect (2 * m - 1) C

/-- Buchweitz's profile of an actual finite set, with integer subtraction. -/
def beta (G : Finset Nat) (n : Nat) : Int :=
  ((sumset G n).card : Int) - (2 * (n : Int) - 1) * ((G.card : Int) - 1)

lemma reflect_card {f : Nat} {C : Finset Nat} (hC : ∀ c ∈ C, c ≤ f) :
    (reflect f C).card = C.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  dsimp at he
  have := hC a ha
  have := hC b hb
  omega

lemma reflect_bound {f : Nat} {C : Finset Nat} {x : Nat}
    (hx : x ∈ reflect f C) : x ≤ f := by
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
  omega

lemma reflect_reflect {f : Nat} {C : Finset Nat} (hC : ∀ c ∈ C, c ≤ f) :
    reflect f (reflect f C) = C := by
  ext x
  simp only [reflect, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have := hC z hz
    simpa [Nat.sub_sub_self this] using hz
  · intro hx
    exact ⟨f - x, ⟨x, hx, rfl⟩, by have := hC x hx; omega⟩

/-- Reflection commutes with the genuine n-fold sumset. -/
theorem sumset_reflect {f : Nat} {C : Finset Nat} (hC : ∀ c ∈ C, c ≤ f)
    (n : Nat) : sumset (reflect f C) n = reflect (n * f) (sumset C n) := by
  induction n with
  | zero => simp [reflect]
  | succ n ih =>
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sumset_succ.mp hx
      rw [ih] at ha
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      apply Finset.mem_image.mpr
      refine ⟨u + v, mem_sumset_succ.mpr ⟨u, hu, v, hv, rfl⟩, ?_⟩
      have := sumset_bound hC n hu
      have := hC v hv
      rw [Nat.succ_mul]
      omega
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_sumset_succ.mp hy
      apply mem_sumset_succ.mpr
      refine ⟨n * f - u, ?_, f - v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
      · rw [ih]
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      · have := sumset_bound hC n hu
        have := hC v hv
        rw [Nat.succ_mul]
        omega

theorem beta_reflect {f : Nat} {C : Finset Nat} (hC : ∀ c ∈ C, c ≤ f)
    (n : Nat) : beta (reflect f C) n = beta C n := by
  unfold beta
  rw [sumset_reflect hC n, reflect_card (fun _ hx => sumset_bound hC n hx),
    reflect_card hC]

lemma mem_gapset_iff {m : Nat} {C : Finset Nat} (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) (n : Nat) :
    n ∈ gapset m C ↔ ReflectedGap m (· ∈ C) n := by
  simp only [gapset, reflect, Finset.mem_union, Finset.mem_Icc, Finset.mem_image,
    ReflectedGap]
  constructor
  · rintro (h | ⟨c, hc, rfl⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨c, hc, by have := hC c hc; omega⟩
  · rintro (h | ⟨c, hc, he⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨c, hc, by omega⟩

lemma gapset_bound {m : Nat} {C : Finset Nat} (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) {x : Nat} (hx : x ∈ gapset m C) :
    x ≤ 2 * m - 1 := by
  have := gap_lt_twice hm hC ((mem_gapset_iff hm hC x).mp hx)
  omega

theorem gapset_card {m : Nat} {C : Finset Nat} (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) : (gapset m C).card = m - 1 + C.card := by
  unfold gapset
  rw [Finset.card_union_of_disjoint]
  · rw [reflect_card (by intro c hc; have := hC c hc; omega), Nat.card_Icc]
    omega
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := Finset.mem_Icc.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    have := hC c hc
    omega

theorem reflect_gapset {m : Nat} {C : Finset Nat} (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) :
    reflect (2 * m - 1) (gapset m C) = C ∪ Finset.Icc m (2 * m - 2) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyb := gapset_bound hm hC hy
    have hyg := (mem_gapset_iff hm hC y).mp hy
    have hh := (reflected_gap_iff hm hC (n := 2 * m - 1 - y) (by omega))
    have he : 2 * m - 1 - (2 * m - 1 - y) = y := by omega
    rw [he] at hh
    simpa only [Finset.mem_union, Finset.mem_Icc] using hh.mp hyg
  · intro hx
    have hx' : x ∈ C ∨ m ≤ x ∧ x ≤ 2 * m - 2 := by simpa using hx
    have hxb : x ≤ 2 * m - 1 := by
      rcases hx' with hx' | hx'
      · have := hC x hx'; omega
      · omega
    apply Finset.mem_image.mpr
    refine ⟨2 * m - 1 - x, ?_, by omega⟩
    exact (mem_gapset_iff hm hC _).mpr ((reflected_gap_iff hm hC hxb).mpr hx')

lemma interval_sumset_decomposition (C : Finset Nat) (m : Nat) (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) (hz : 0 ∈ C) (hpos : ∃ c ∈ C, 0 < c)
    (n : Nat) (hn : 1 ≤ n) :
    sumset (C ∪ Finset.Icc m (2 * m - 2)) n =
      (sumset C n).filter (· < m) ∪ Finset.Icc m (2 * n * (m - 1)) := by
  rw [sumset_with_interval C m hm hC hz hpos n hn]
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  have hbound (hx : x ∈ sumset C n) : x ≤ 2 * n * (m - 1) := by
    have hx' := sumset_bound hC n hx
    have hh : n * (m - 2) ≤ 2 * n * (m - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  constructor
  · rintro (hx | hx)
    · by_cases h : x < m
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨by omega, hbound hx⟩
    · exact Or.inr hx
  · rintro (⟨hx, _⟩ | hx)
    · exact Or.inl hx
    · exact Or.inr hx

theorem interval_sumset_card (C : Finset Nat) (m : Nat) (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) (hz : 0 ∈ C) (hpos : ∃ c ∈ C, 0 < c)
    (n : Nat) (hn : 1 ≤ n) :
    (sumset (C ∪ Finset.Icc m (2 * m - 2)) n).card =
      truncatedCount C m n + (2 * n - 1) * (m - 1) := by
  rw [interval_sumset_decomposition C m hm hC hz hpos n hn]
  rw [Finset.card_union_of_disjoint]
  · rw [Nat.card_Icc]
    change truncatedCount C m n + (2 * n * (m - 1) + 1 - m) = _
    have hh : 2 * n * (m - 1) = (2 * n - 1) * (m - 1) + (m - 1) := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    omega
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have := (Finset.mem_filter.mp hx).2
    have := (Finset.mem_Icc.mp hy).1
    omega

/-- The full reflection formula of Proposition 2.3, for every positive order.
The left side counts sums in the actual semigroup gapset. -/
theorem beta_gapset (C : Finset Nat) (m : Nat) (hm : 3 ≤ m)
    (hC : ∀ c ∈ C, c ≤ m - 2) (hz : 0 ∈ C) (hpos : ∃ c ∈ C, 0 < c)
    (n : Nat) (hn : 1 ≤ n) :
    beta (gapset m C) n = (truncatedCount C m n : Int) -
      (2 * (n : Int) - 1) * ((C.card : Int) - 1) := by
  have hreflect := beta_reflect (fun _ hx => gapset_bound hm hC hx) n
  rw [reflect_gapset hm hC] at hreflect
  have hc := interval_sumset_card C m hm hC hz hpos n hn
  have hc1 := interval_sumset_card C m hm hC hz hpos 1 (by omega)
  have htrunc : truncatedCount C m 1 = C.card := by
    unfold truncatedCount
    rw [sumset_one]
    congr 1
    apply Finset.filter_true_of_mem
    intro c hc
    have := hC c hc
    omega
  simp only [sumset_one, htrunc] at hc1
  rw [← hreflect]
  unfold beta
  rw [hc, hc1]
  have hn' : 1 ≤ 2 * n := by omega
  have hm' : 1 ≤ m := by omega
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn', Nat.cast_sub hm',
    Nat.cast_ofNat, Nat.cast_one]
  ring

@[simp] theorem beta_one (G : Finset Nat) : beta G 1 = 1 := by
  simp [beta]

end BuchweitzProfiles
