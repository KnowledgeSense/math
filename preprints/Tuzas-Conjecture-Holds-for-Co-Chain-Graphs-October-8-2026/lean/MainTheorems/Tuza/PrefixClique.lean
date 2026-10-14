import MainTheorems.Tuza.RectangleDefect
import MainTheorems.Tuza.NearCliquePacking

namespace ResearchMain.Tuza

theorem image_top_eq_within {V I : Type*} (a : I ↪ V) (p : V → Prop)
    (h : ∀ v, p v ↔ ∃ i, a i = v) :
    imageGraph (⊤ : SimpleGraph I) a = withinGraph p := by
  ext x y
  constructor
  · rintro ⟨i, j, rfl, rfl, hij⟩
    exact ⟨a.injective.ne hij, (h _).mpr ⟨i, rfl⟩, (h _).mpr ⟨j, rfl⟩⟩
  · rintro ⟨hxy, hx, hy⟩
    obtain ⟨i, rfl⟩ := (h x).mp hx
    obtain ⟨j, rfl⟩ := (h y).mp hy
    exact ⟨i, j, rfl, rfl, fun hij => hxy (congrArg a hij)⟩

theorem unionEmbedding_range {V : Type*} {n q : ℕ} (a : Fin n ↪ V) (b : Fin q ↪ V)
    (h : ∀ i j, a i ≠ b j) (v : V) :
    (∃ k, unionEmbedding a b h k = v) ↔ (∃ i, a i = v) ∨ ∃ j, b j = v := by
  constructor
  · rintro ⟨k, hk⟩
    change sumEmbedding a b h (finSumFinEquiv.symm k) = v at hk
    cases he : finSumFinEquiv.symm k with
    | inl i => exact Or.inl ⟨i, by simpa only [he, sumEmbedding_inl] using hk⟩
    | inr j => exact Or.inr ⟨j, by simpa only [he, sumEmbedding_inr] using hk⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · refine ⟨finSumFinEquiv (.inl i), ?_⟩
      change sumEmbedding a b h (finSumFinEquiv.symm (finSumFinEquiv (.inl i))) = v
      simpa only [Equiv.symm_apply_apply, sumEmbedding_inl] using hi
    · refine ⟨finSumFinEquiv (.inr j), ?_⟩
      change sumEmbedding a b h (finSumFinEquiv.symm (finSumFinEquiv (.inr j))) = v
      simpa only [Equiv.symm_apply_apply, sumEmbedding_inr] using hj

theorem prefixEmbedding_range (n p : ℕ) (hp : p ≤ n) (i : Fin n) :
    (∃ j, prefixEmbedding n p hp j = i) ↔ i.val < p := by
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

namespace FerrersProfile

def prefixUnionEmbedding {a b : ℕ} (x y : ℕ) (hxa : x ≤ a) (hyb : y ≤ b) :
    Fin (x + y) ↪ Fin a ⊕ Fin b :=
  unionEmbedding ((prefixEmbedding a x hxa).trans Function.Embedding.inl)
    ((prefixEmbedding b y hyb).trans Function.Embedding.inr) (fun _ _ => Sum.inl_ne_inr)

theorem prefixUnionEmbedding_range {a b : ℕ} (x y : ℕ) (hxa : x ≤ a) (hyb : y ≤ b)
    (v : Fin a ⊕ Fin b) :
    prefixUnion x y v ↔ ∃ k, prefixUnionEmbedding x y hxa hyb k = v := by
  refine Iff.trans ?_ (unionEmbedding_range
    ((prefixEmbedding a x hxa).trans Function.Embedding.inl)
    ((prefixEmbedding b y hyb).trans Function.Embedding.inr)
    (fun _ _ => Sum.inl_ne_inr) v).symm
  cases v with
  | inl i =>
    change i.val < x ↔ (∃ k, Sum.inl (prefixEmbedding a x hxa k) = Sum.inl i) ∨
      ∃ k, Sum.inr (prefixEmbedding b y hyb k) = Sum.inl i
    simp only [Sum.inl.injEq, Sum.inr_ne_inl, exists_false, or_false,
      prefixEmbedding_range]
  | inr j =>
    change j.val < y ↔ (∃ k, Sum.inl (prefixEmbedding a x hxa k) = Sum.inr j) ∨
      ∃ k, Sum.inr (prefixEmbedding b y hyb k) = Sum.inr j
    simp only [Sum.inr.injEq, Sum.inl_ne_inr, exists_false, false_or,
      prefixEmbedding_range]

theorem prefixClique_eq_image {a b : ℕ} (x y : ℕ) (hxa : x ≤ a) (hyb : y ≤ b) :
    prefixClique (a := a) (b := b) x y =
      imageGraph (⊤ : SimpleGraph (Fin (x + y))) (prefixUnionEmbedding x y hxa hyb) :=
  (image_top_eq_within _ _ (prefixUnionEmbedding_range x y hxa hyb)).symm

end FerrersProfile

end ResearchMain.Tuza
