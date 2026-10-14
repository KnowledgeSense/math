import MainTheorems.Tuza.RectanglePacking
import MainTheorems.Tuza.CoChain
import Mathlib.Order.Interval.Finset.Fin

namespace ResearchMain.Tuza

def prefixEmbedding (n p : ℕ) (h : p ≤ n) : Fin p ↪ Fin n where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  inj' := by intro i j hij; exact Fin.ext (congrArg (fun z : Fin n => z.val) hij)

def suffixEmbedding (n p : ℕ) (h : p ≤ n) : Fin (n - p) ↪ Fin n where
  toFun i := ⟨p + i.val, by have := i.isLt; omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; omega

@[simp]
theorem prefixEmbedding_val (n p : ℕ) (h : p ≤ n) (i : Fin p) :
    (prefixEmbedding n p h i).val = i.val := rfl

@[simp]
theorem suffixEmbedding_val (n p : ℕ) (h : p ≤ n) (i : Fin (n - p)) :
    (suffixEmbedding n p h i).val = p + i.val := rfl

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

def height (k : ℕ) : ℕ := (Finset.univ.filter (fun i => k ≤ d.degree i)).card

theorem height_le (k : ℕ) : d.height k ≤ a := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin a)

theorem height_antitone : Antitone d.height := by
  intro k l hkl
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl.trans (Finset.mem_filter.mp hi).2⟩

theorem lt_height_iff (k : ℕ) (i : Fin a) : i.val < d.height k ↔ k ≤ d.degree i := by
  constructor
  · intro hi
    by_contra h
    have hs : Finset.univ.filter (fun j => k ≤ d.degree j) ⊆ Finset.Iio i := by
      intro j hj
      have hdj := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact h (hdj.trans (d.antitone (le_of_not_gt hji)))
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    exact Nat.not_lt_of_ge hc hi
  · intro h
    have hs : Finset.Iic i ⊆ Finset.univ.filter (fun j => k ≤ d.degree j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (d.antitone (Finset.mem_Iic.mp hj))⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

def rectangle (p k : ℕ) (hp : p ≤ a) (hk : k ≤ b)
    (hc : ∀ i : Fin p, k ≤ d.degree (prefixEmbedding a p hp i)) :
    CliqueRectangle d.graph p (a - p) k (b - k) where
  leftTop := (prefixEmbedding a p hp).trans Function.Embedding.inl
  leftBottom := (suffixEmbedding a p hp).trans Function.Embedding.inl
  rightTop := (prefixEmbedding b k hk).trans Function.Embedding.inr
  rightBottom := (suffixEmbedding b k hk).trans Function.Embedding.inr
  color := Sum.elim (fun i => if i.val < p then 0 else 1)
    (fun j => if j.val < k then 2 else 3)
  color_leftTop i := by
    change (if (prefixEmbedding a p hp i).val < p then (0 : Fin 4) else 1) = 0
    rw [prefixEmbedding_val, ite_eq_left i.isLt]
  color_leftBottom i := by
    change (if (suffixEmbedding a p hp i).val < p then (0 : Fin 4) else 1) = 1
    rw [suffixEmbedding_val, ite_eq_right (by omega)]
  color_rightTop i := by
    change (if (prefixEmbedding b k hk i).val < k then (2 : Fin 4) else 3) = 2
    rw [prefixEmbedding_val, ite_eq_left i.isLt]
  color_rightBottom i := by
    change (if (suffixEmbedding b k hk i).val < k then (2 : Fin 4) else 3) = 3
    rw [suffixEmbedding_val, ite_eq_right (by omega)]
  clique_leftTop i j hij := by
    exact fun hh => hij ((prefixEmbedding a p hp).injective hh)
  clique_leftBottom i j hij := by
    exact fun hh => hij ((suffixEmbedding a p hp).injective hh)
  clique_rightTop i j hij := by
    exact fun hh => hij ((prefixEmbedding b k hk).injective hh)
  clique_rightBottom i j hij := by
    exact fun hh => hij ((suffixEmbedding b k hk).injective hh)
  cross_left i j := by
    intro hij
    have hv := congrArg Fin.val hij
    simp only [prefixEmbedding_val, suffixEmbedding_val] at hv
    have := i.isLt
    omega
  cross_right i j := by
    intro hij
    have hv := congrArg Fin.val hij
    simp only [prefixEmbedding_val, suffixEmbedding_val] at hv
    have := i.isLt
    omega
  cross_top i j := by
    exact lt_of_lt_of_le j.isLt (hc i)

def heightRectangle (k : ℕ) (hk : k ≤ b) :
    CliqueRectangle d.graph (d.height k) (a - d.height k) k (b - k) :=
  d.rectangle (d.height k) k (d.height_le k) hk
    (fun i => (d.lt_height_iff k _).mp i.isLt)

theorem rectangle_left_bound (k : ℕ) (hk : k ≤ b) :
    completeCount a + fanCount (d.height k) k + fanCount k (b - k) ≤ packingNumber d.graph := by
  obtain ⟨P, hP, hc⟩ := (d.heightRectangle k hk).packing_left_fans
  rw [Nat.add_sub_of_le (d.height_le k)] at hc
  exact hc ▸ packing_le_number hP

theorem rectangle_top_bound (k : ℕ) (hk : k ≤ b) :
    completeCount (d.height k + k) + fanCount (d.height k) (a - d.height k) +
      fanCount k (b - k) ≤ packingNumber d.graph := by
  obtain ⟨P, hP, hc⟩ := (d.heightRectangle k hk).packing_top_fans
  exact hc ▸ packing_le_number hP

def transpose : FerrersProfile b a where
  degree j := d.height (j.val + 1)
  bound _ := d.height_le _
  antitone := fun _ _ hij => d.height_antitone (Nat.add_le_add_right hij 1)

theorem transpose_adj (i : Fin a) (j : Fin b) :
    d.transpose.graph.Adj (.inl j) (.inr i) ↔ d.graph.Adj (.inl i) (.inr j) := by
  exact (d.lt_height_iff (j.val + 1) i).trans Nat.succ_le_iff

def transposeIso : d.transpose.graph ≃g d.graph where
  toEquiv := Equiv.sumComm _ _
  map_rel_iff' := by
    intro x y
    cases x with
    | inl j =>
      cases y with
      | inl k => rfl
      | inr i => exact (d.transpose_adj i j).symm
    | inr i =>
      cases y with
      | inl j => exact (d.transpose_adj i j).symm
      | inr l => rfl

end FerrersProfile

end ResearchMain.Tuza
