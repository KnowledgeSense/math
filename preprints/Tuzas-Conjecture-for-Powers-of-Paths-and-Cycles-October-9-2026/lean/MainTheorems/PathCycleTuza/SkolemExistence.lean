import MainTheorems.PathCycleTuza.SkolemData

namespace ResearchMain.PathCycleTuza

def hookFlag (m : ℕ) : ℕ := if m % 4 < 2 then 0 else 1

def zeroSkolem : SkolemData 0 0 where
  lower := Fin.elim0
  delta_le := by decide
  positive i := Fin.elim0 i
  bounded i := Fin.elim0 i
  unique i := Fin.elim0 i
  omits i := Fin.elim0 i

def oneSkolem : SkolemData 1 0 where
  lower := ![1]
  delta_le := by decide
  positive := by decide
  bounded := by decide
  unique := by decide
  omits := by intro i slot h; omega

def twoSkolem : SkolemData 2 1 where
  lower := ![1, 3]
  delta_le := by decide
  positive := by decide
  bounded := by decide
  unique := by decide
  omits := by decide

def threeSkolem : SkolemData 3 1 where
  lower := ![2, 5, 1]
  delta_le := by decide
  positive := by decide
  bounded := by decide
  unique := by decide
  omits := by decide

def fourSkolem : SkolemData 4 0 where
  lower := ![7, 2, 3, 1]
  delta_le := by decide
  positive := by decide
  bounded := by decide
  unique := by decide
  omits := by intro i slot h; omega

def fiveSkolem : SkolemData 5 0 where
  lower := ![1, 7, 3, 4, 5]
  delta_le := by decide
  positive := by decide
  bounded := by decide
  unique := by decide
  omits := by intro i slot h; omega

def sixSkolem : SkolemData 6 1 where
  lower := ![10, 2, 6, 1, 3, 7]
  delta_le := by decide
  positive := by decide
  bounded := by decide
  unique := by decide
  omits := by decide

theorem exists_skolem (m : ℕ) : Nonempty (SkolemData m (hookFlag m)) := by
  by_cases hm : m ≤ 6
  · interval_cases m
    · exact ⟨zeroSkolem⟩
    · exact ⟨oneSkolem⟩
    · exact ⟨twoSkolem⟩
    · exact ⟨threeSkolem⟩
    · exact ⟨fourSkolem⟩
    · exact ⟨fiveSkolem⟩
    · exact ⟨sixSkolem⟩
  · have hrest : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hrest with hr | hr | hr | hr
    · have he : m = 4 * (m / 4) := by omega
      have ht : 2 ≤ m / 4 := by omega
      have hδ : hookFlag m = 0 := by simp [hookFlag, hr]
      rw [hδ, he]
      exact ⟨ordinaryFourData _ ht⟩
    · have he : m = 4 * (m / 4) + 1 := by omega
      have ht : 2 ≤ m / 4 := by omega
      have hδ : hookFlag m = 0 := by simp [hookFlag, hr]
      rw [hδ, he]
      exact ⟨ordinaryOddData _ ht⟩
    · have he : m = 4 * (m / 4) + 2 := by omega
      have ht : 2 ≤ m / 4 := by omega
      have hδ : hookFlag m = 1 := by simp [hookFlag, hr]
      rw [hδ, he]
      exact ⟨hookedEvenData _ ht⟩
    · have he : m = 4 * (m / 4) + 3 := by omega
      have ht : 1 ≤ m / 4 := by omega
      have hδ : hookFlag m = 1 := by simp [hookFlag, hr]
      rw [hδ, he]
      exact ⟨hookedOddData _ ht⟩

end ResearchMain.PathCycleTuza
