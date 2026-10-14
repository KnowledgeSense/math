import MainTheorems.PathCycleTuza.SkolemOdd
import MainTheorems.PathCycleTuza.HookedEven
import MainTheorems.PathCycleTuza.HookedOdd

namespace ResearchMain.PathCycleTuza

structure SkolemData (m δ : ℕ) where
  lower : Fin m → ℕ
  delta_le : δ ≤ 1
  positive : ∀ i, 1 ≤ lower i
  bounded : ∀ i (slot : Bool), lower i + (if slot then i.val + 1 else 0) ≤ 2 * m + δ
  unique : ∀ i j (u v : Bool),
    lower i + (if u then i.val + 1 else 0) = lower j + (if v then j.val + 1 else 0) →
    i = j ∧ u = v
  omits : ∀ i (slot : Bool), δ = 1 → lower i + (if slot then i.val + 1 else 0) ≠ 2 * m

def SkolemData.endpoint {m δ : ℕ} (D : SkolemData m δ) (p : Fin m × Bool) : ℕ :=
  D.lower p.1 + if p.2 then p.1.val + 1 else 0

theorem SkolemData.endpoint_injective {m δ : ℕ} (D : SkolemData m δ) :
    Function.Injective D.endpoint := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  obtain ⟨hij, huv⟩ := D.unique i j u v h
  exact Prod.ext hij huv

def SkolemData.ofRecipe (m δ : ℕ) (lower : ℕ → ℕ) (hδ : δ ≤ 1)
    (hp : ∀ i, 1 ≤ i → i ≤ m → 1 ≤ lower i)
    (hb : ∀ i (slot : Bool), 1 ≤ i → i ≤ m → skolemEndpoint lower i slot ≤ 2 * m + δ)
    (hu : ∀ i j (u v : Bool), 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m →
      skolemEndpoint lower i u = skolemEndpoint lower j v → i = j ∧ u = v)
    (ho : ∀ i (slot : Bool), 1 ≤ i → i ≤ m → δ = 1 → skolemEndpoint lower i slot ≠ 2 * m) :
    SkolemData m δ where
  lower i := lower (i.val + 1)
  delta_le := hδ
  positive i := hp _ (by omega) (by omega)
  bounded i slot := hb _ slot (by omega) (by omega)
  unique i j u v h := by
    obtain ⟨hij, huv⟩ := hu _ _ u v (by omega) (by omega) (by omega) (by omega) h
    exact ⟨Fin.ext (by omega), huv⟩
  omits i slot h := ho _ slot (by omega) (by omega) h

def ordinaryFourData (t : ℕ) (ht : 2 ≤ t) : SkolemData (4 * t) 0 :=
  SkolemData.ofRecipe _ _ (ordinaryFourLower t) (by decide)
    (ordinaryFour_positive t · ht)
    (by intro i slot hi hib; have h := ordinaryFour_bounded t i slot ht hi hib; omega)
    (ordinaryFour_injective t · · · · ht)
    (by intro i slot hi hib h; omega)

def ordinaryOddData (t : ℕ) (ht : 2 ≤ t) : SkolemData (4 * t + 1) 0 :=
  SkolemData.ofRecipe _ _ (ordinaryOddLower t) (by decide)
    (ordinaryOdd_positive t · ht)
    (by intro i slot hi hib; have h := ordinaryOdd_bounded t i slot ht hi hib; omega)
    (ordinaryOdd_injective t · · · · ht)
    (by intro i slot hi hib h; omega)

def hookedEvenData (t : ℕ) (ht : 2 ≤ t) : SkolemData (4 * t + 2) 1 :=
  SkolemData.ofRecipe _ _ (hookedEvenLower t) (by decide)
    (hookedEven_positive t · ht)
    (by intro i slot hi hib; have h := hookedEven_bounded t i slot ht hi hib; omega)
    (hookedEven_injective t · · · · ht)
    (by intro i slot hi hib h; have ho := hookedEven_omits t i slot ht hi hib; omega)

def hookedOddData (t : ℕ) (ht : 1 ≤ t) : SkolemData (4 * t + 3) 1 :=
  SkolemData.ofRecipe _ _ (hookedOddLower t) (by decide)
    (hookedOdd_positive t · ht)
    (by intro i slot hi hib; have h := hookedOdd_bounded t i slot ht hi hib; omega)
    (hookedOdd_injective t · · · · ht)
    (by intro i slot hi hib h; have ho := hookedOdd_omits t i slot ht hi hib; omega)

end ResearchMain.PathCycleTuza
