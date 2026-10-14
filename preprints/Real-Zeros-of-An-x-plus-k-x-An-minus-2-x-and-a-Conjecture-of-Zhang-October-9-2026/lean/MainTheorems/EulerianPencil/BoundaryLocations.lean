import MainTheorems.EulerianPencil.InterlacingPairs

namespace ResearchMain.EulerianPencil

open Polynomial

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem root_equation {b x : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b)
    (hx : b ≤ x) (k : ℝ) :
    (f + C k * g).eval x = 0 ↔ f.eval x / g.eval x + k = 0 := by
  have hg := h.denominator_positive hb hx
  simp only [eval_add, eval_mul, eval_C]
  constructor <;> intro he
  · field_simp
    linear_combination he
  · field_simp at he
    linear_combination he

theorem unique_root_above {b x y : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b)
    (hx : b ≤ x) (hy : b ≤ y) (k : ℝ)
    (hqx : (f + C k * g).eval x = 0) (hqy : (f + C k * g).eval y = 0) : x = y := by
  have hxe := (h.root_equation hb hx k).mp hqx
  have hye := (h.root_equation hb hy k).mp hqy
  apply (h.ratio_strictMonoOn hb).injOn hx hy
  linarith

theorem exists_root_above {b : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b) (k : ℝ)
    (hk : f.eval b / g.eval b + k < 0) : ∃ x : ℝ, b < x ∧ (f + C k * g).eval x = 0 := by
  have hn : ¬∀ x : ℝ, (f + C k * g).eval x = 0 → x ≤ b := by
    intro hr
    have := (h.root_bound_iff hb k).mp hr
    linarith
  push Not at hn
  obtain ⟨x, hx, hxb⟩ := hn
  exact ⟨x, hxb, hx⟩

theorem root_at_boundary {b : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b) :
    (f + C (-(f.eval b / g.eval b)) * g).eval b = 0 :=
  (h.root_equation hb (le_refl b) _).mpr (by ring)

theorem remaining_roots_below {b t : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b)
    (ht : b ≤ t) (k : ℝ) (hqt : (f + C k * g).eval t = 0) {x : ℝ}
    (hx : (f + C k * g).eval x = 0) (hxt : x ≠ t) : x < b := by
  by_contra hxb
  exact hxt (h.unique_root_above hb (not_lt.mp hxb) ht k hx hqt)

theorem middle_root {b c : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b) (hbc : b < c)
    (k : ℝ) (hklo : 0 < f.eval c / g.eval c + k) (hkhi : f.eval b / g.eval b + k < 0) :
    ∃ x : ℝ, b < x ∧ x < c ∧ (f + C k * g).eval x = 0 := by
  obtain ⟨x, hxb, hx⟩ := h.exists_root_above hb k hkhi
  have hc := (h.strict_root_bound_iff (fun r hr => (hb r hr).trans hbc) k).mpr hklo x hx
  exact ⟨x, hxb, hc, hx⟩

theorem two_ray_root_classification {b c : ℝ}
    (hb : ∀ r : ℝ, g.eval r = 0 → r < b) (hbc : b < c) (k : ℝ) :
    (∀ x : ℝ, (f + C k * g).eval x = 0 → x ≤ b ∨ c ≤ x) ↔
      k ≤ -(f.eval c / g.eval c) ∨ -(f.eval b / g.eval b) ≤ k := by
  constructor
  · intro hroots
    by_contra hkr
    push Not at hkr
    obtain ⟨x, hxb, hxc, hx⟩ := h.middle_root hb hbc k (by linarith) (by linarith)
    rcases hroots x hx with h | h <;> linarith
  · rintro (hk | hk)
    · have hc := fun r hr => (hb r hr).trans hbc
      have ht : ∃ t : ℝ, c ≤ t ∧ (f + C k * g).eval t = 0 := by
        by_cases hke : k = -(f.eval c / g.eval c)
        · exact ⟨c, le_refl c, hke ▸ h.root_at_boundary hc⟩
        · have hklt := lt_of_le_of_ne hk hke
          obtain ⟨t, ht, hqt⟩ := h.exists_root_above hc k (by linarith)
          exact ⟨t, ht.le, hqt⟩
      obtain ⟨t, ht, hqt⟩ := ht
      intro x hx
      by_cases he : x = t
      · exact Or.inr (he ▸ ht)
      · exact Or.inl (h.remaining_roots_below hb (hbc.le.trans ht) k hqt hx he).le
    · intro x hx
      exact Or.inl ((h.root_bound_iff hb k).mpr (by linarith) x hx)

theorem strict_two_ray_root_classification {b c : ℝ}
    (hb : ∀ r : ℝ, g.eval r = 0 → r < b) (hbc : b < c) (k : ℝ) :
    (∀ x : ℝ, (f + C k * g).eval x = 0 → x < b ∨ c < x) ↔
      k < -(f.eval c / g.eval c) ∨ -(f.eval b / g.eval b) < k := by
  constructor
  · intro hroots
    have hclosed := (h.two_ray_root_classification hb hbc k).mp
      (fun x hx => (hroots x hx).imp le_of_lt le_of_lt)
    rcases hclosed with hk | hk
    · left
      apply lt_of_le_of_ne hk
      intro he
      have hq := h.root_at_boundary (fun r hr => (hb r hr).trans hbc)
      rw [← he] at hq
      rcases hroots c hq with hc | hc <;> linarith
    · right
      apply lt_of_le_of_ne hk
      intro he
      have hq := h.root_at_boundary hb
      rw [he] at hq
      rcases hroots b hq with hb' | hb' <;> linarith
  · rintro (hk | hk)
    · obtain ⟨t, ht, hqt⟩ := h.exists_root_above (fun r hr => (hb r hr).trans hbc) k (by linarith)
      intro x hx
      by_cases he : x = t
      · exact Or.inr (he ▸ ht)
      · exact Or.inl (h.remaining_roots_below hb (hbc.trans ht).le k hqt hx he)
    · intro x hx
      exact Or.inl ((h.strict_root_bound_iff hb k).mpr (by linarith) x hx)

end InterlacingPair

end ResearchMain.EulerianPencil
