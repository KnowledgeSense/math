import MainTheorems.PathCycleTuza.SkolemMass

namespace ResearchMain.PathCycleTuza

structure DifferenceFamily (m k : ℕ) where
  first : Fin m → ℕ
  second : Fin m → ℕ
  positive : ∀ i, 0 < first i
  ordered : ∀ i, first i < second i
  bounded : ∀ i, first i + second i ≤ k
  disjoint : ∀ i j, i ≠ j → Disjoint
    ({first i, second i, first i + second i} : Finset ℕ)
    {first j, second j, first j + second j}

def DifferenceFamily.span {m k : ℕ} (F : DifferenceFamily m k) (i : Fin m) : ℕ :=
  F.first i + F.second i

def SkolemData.differenceFamily {m : ℕ} (D : SkolemData m (hookFlag m)) :
    DifferenceFamily m (3 * m + hookFlag m) where
  first i := i.val + 1
  second i := m + D.lower i
  positive i := by omega
  ordered i := by have h := D.positive i; omega
  bounded i := by
    have h := D.bounded i true
    simp at h
    omega
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hi := i.isLt
    have hj := j.isLt
    have hpi := D.positive i
    have hpj := D.positive j
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxi hxj
    rcases hxi with hxi | hxi | hxi <;> rcases hxj with hxj | hxj | hxj
    all_goals first
      | exact hij (Fin.ext (by omega))
      | omega
      | exact hij (D.unique i j false false (by simp; omega)).1
      | exact hij (D.unique i j false true (by simp; omega)).1
      | exact hij (D.unique i j true false (by simp; omega)).1
      | exact hij (D.unique i j true true (by simp; omega)).1

theorem SkolemData.difference_span {m : ℕ} (D : SkolemData m (hookFlag m)) (i : Fin m) :
    D.differenceFamily.span i = D.maxDifference i := by
  simp only [differenceFamily, DifferenceFamily.span, maxDifference]
  omega

theorem SkolemData.differenceFamily_mass {m : ℕ} (D : SkolemData m (hookFlag m)) :
    4 * (∑ i : Fin m, (D.differenceFamily.span i : ℤ)) =
      9 * (m : ℤ) ^ 2 + 3 * m + 2 * hookFlag m := by
  simp only [D.difference_span]
  exact D.difference_mass

end ResearchMain.PathCycleTuza
