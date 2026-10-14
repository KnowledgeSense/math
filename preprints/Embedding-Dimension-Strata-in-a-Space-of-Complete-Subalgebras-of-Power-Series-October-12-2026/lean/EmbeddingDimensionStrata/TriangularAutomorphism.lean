import EmbeddingDimensionStrata.CotangentCoordinates

/-! # Polynomial triangular automorphisms with proved inverses -/
noncomputable section
namespace EmbeddingDimensionStrata.PolynomialTriangular

structure Data (σ : Type*) (m : ℕ) where
  pivot : Fin m → σ
  injective : Function.Injective pivot
  remainder : Fin m → MvPolynomial σ ℤ
  triangular : ∀ i j : Fin m, i ≤ j → pivot j ∉ (remainder i).vars

variable {σ : Type*} [DecidableEq σ] {m : ℕ} (D : Data σ m)
variable {A : Type*} [CommRing A]

def ev (p : σ → A) : MvPolynomial σ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) p

def forward (p : σ → A) (j : σ) : A :=
  if h : ∃ i, D.pivot i = j then p j - ev p (D.remainder (Classical.choose h)) else p j

def stage (q : σ → A) : ℕ → σ → A
  | 0 => q
  | n+1 => if hn : n < m then
      Function.update (stage q n) (D.pivot ⟨n,hn⟩)
        (q (D.pivot ⟨n,hn⟩) + ev (stage q n) (D.remainder ⟨n,hn⟩))
    else stage q n

theorem forward_pivot (p : σ → A) (i : Fin m) :
    forward D p (D.pivot i) = p (D.pivot i) - ev p (D.remainder i) := by
  rw [forward, dite_eq_left ⟨i,rfl⟩]
  have heq := D.injective (Classical.choose_spec (show ∃ j, D.pivot j = D.pivot i from ⟨i,rfl⟩))
  rw [heq]

theorem forward_free (p : σ → A) (j : σ) (hj : ¬∃ i, D.pivot i = j) :
    forward D p j = p j := by rw [forward, dite_eq_right hj]

theorem ev_update (p : σ → A) (i j : Fin m) (hij : i ≤ j) (a : A) :
    ev (Function.update p (D.pivot j) a) (D.remainder i) = ev p (D.remainder i) := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro k hk _
  apply Function.update_of_ne
  intro h
  subst k
  exact D.triangular i j hij hk

theorem stage_free (q : σ → A) (N : ℕ) (j : σ) (hj : ¬∃ i, D.pivot i = j) :
    stage D q N j = q j := by
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [stage]
    split_ifs with hn
    · rw [Function.update_of_ne (by intro h; exact hj ⟨⟨n,hn⟩,h.symm⟩)]
      exact ih
    · exact ih

theorem stage_equations (q : σ → A) (N : ℕ) (i : Fin m) (hiN : i.val < N) :
    stage D q N (D.pivot i) = q (D.pivot i) + ev (stage D q N) (D.remainder i) := by
  induction N with
  | zero => omega
  | succ n ih =>
    rw [stage]
    split_ifs with hn
    · have hin : i ≤ (⟨n,hn⟩ : Fin m) := by change i.val ≤ n; omega
      rw [ev_update D _ i ⟨n,hn⟩ hin]
      by_cases heq : i = (⟨n,hn⟩ : Fin m)
      · subst i
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne (fun h => heq (D.injective h))]
        apply ih
        have hv : i.val ≠ n := by intro h; exact heq (Fin.ext h)
        omega
    · apply ih
      have hi := i.isLt
      omega

theorem ev_eq_of_earlier (p r : σ → A) (i : Fin m)
    (hfree : ∀ j, (¬∃ k, D.pivot k = j) → p j = r j)
    (hearlier : ∀ j : Fin m, j < i → p (D.pivot j) = r (D.pivot j)) :
    ev p (D.remainder i) = ev r (D.remainder i) := by
  classical
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro k hk _
  by_cases hfreeK : ¬∃ j, D.pivot j = k
  · exact hfree k hfreeK
  · obtain ⟨j,rfl⟩ := not_not.mp hfreeK
    apply hearlier j
    by_contra hji
    exact D.triangular i j (le_of_not_gt hji) hk

theorem stage_unique (q p : σ → A)
    (hfree : ∀ j, (¬∃ i, D.pivot i = j) → q j = p j)
    (hp : ∀ i : Fin m, p (D.pivot i) = q (D.pivot i) + ev p (D.remainder i)) :
    stage D q m = p := by
  have hagree : ∀ N : ℕ, ∀ i : Fin m, i.val < N → stage D q N (D.pivot i) = p (D.pivot i) := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hin
      rw [stage]
      split_ifs with hn
      · by_cases heq : i = (⟨n,hn⟩ : Fin m)
        · subst i
          rw [Function.update_self, hp]
          congr 1
          apply ev_eq_of_earlier
          · intro j hj
            exact (stage_free D q n j hj).trans (hfree j hj)
          · intro j hj
            exact ih j hj
        · rw [Function.update_of_ne (fun h => heq (D.injective h))]
          apply ih
          have hv : i.val ≠ n := by intro h; exact heq (Fin.ext h)
          omega
      · apply ih
        have hi := i.isLt
        omega
  funext j
  by_cases hj : ¬∃ i, D.pivot i = j
  · exact (stage_free D q m j hj).trans (hfree j hj)
  · obtain ⟨i,rfl⟩ := not_not.mp hj
    exact hagree m i i.isLt

def equiv : (σ → A) ≃ (σ → A) where
  toFun := forward D
  invFun := fun q => stage D q m
  left_inv p := by
    apply stage_unique
    · exact forward_free D p
    · intro i
      rw [forward_pivot]
      ring
  right_inv q := by
    funext j
    change forward D (stage D q m) j = q j
    by_cases hj : ∃ i, D.pivot i = j
    · obtain ⟨i,rfl⟩ := hj
      rw [forward_pivot, stage_equations D q m i i.isLt, add_sub_cancel_right]
    · rw [forward_free D _ j hj, stage_free D q m j hj]

/-- Each forward coordinate is an integral polynomial. -/
def forwardPolynomial (j : σ) : MvPolynomial σ ℤ :=
  if h : ∃ i, D.pivot i = j then MvPolynomial.X j - D.remainder (Classical.choose h) else MvPolynomial.X j

theorem eval_forwardPolynomial (p : σ → A) (j : σ) :
    ev p (forwardPolynomial D j) = forward D p j := by
  simp only [forwardPolynomial, forward]
  split_ifs <;> simp only [map_sub, ev, MvPolynomial.eval₂Hom_X']

omit [DecidableEq σ] in
theorem map_ev {B : Type*} [CommRing B] (φ : A →+* B) (p : σ → A) (Q : MvPolynomial σ ℤ) :
    φ (ev p Q) = ev (fun j => φ (p j)) Q := by
  have hh := MvPolynomial.map_eval₂Hom (Int.castRingHom A) p φ Q
  have hc : φ.comp (Int.castRingHom A) = Int.castRingHom B := by ext z; simp
  rw [hc] at hh
  exact hh

theorem map_stage {B : Type*} [CommRing B] (φ : A →+* B) (q : σ → A) (N : ℕ) :
    (fun j => φ (stage D q N j)) = stage D (fun j => φ (q j)) N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [stage]
    split_ifs with hn
    · by_cases hj : j = D.pivot ⟨n,hn⟩
      · subst j
        rw [Function.update_self, Function.update_self, map_add, map_ev, ih]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact congrFun ih j
    · exact congrFun ih j

/-- The inverse is a polynomial tuple too, with no divisions or case-dependent
rational functions. -/
def inversePolynomial (j : σ) : MvPolynomial σ ℤ := stage D MvPolynomial.X m j

theorem eval_inversePolynomial (p : σ → A) (j : σ) :
    ev p (inversePolynomial D j) = stage D p m j := by
  have h := map_stage D (ev p) (MvPolynomial.X : σ → MvPolynomial σ ℤ) m
  have hx : (fun k : σ => ev p (MvPolynomial.X k)) = p := by
    funext k
    exact MvPolynomial.eval₂_X _ _ k
  rw [hx] at h
  exact congrFun h j

end EmbeddingDimensionStrata.PolynomialTriangular
