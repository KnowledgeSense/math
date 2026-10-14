import MainTheorems.PathCycleTuza.PathPacking

namespace ResearchMain.PathCycleTuza

open Tuza

theorem skolem_path_bound (n m : ℕ) (hn : 3 * m + hookFlag m ≤ n) :
    4 * (packingNumber (pathPower n (3 * m + hookFlag m)) : ℤ) ≥
      4 * (m : ℤ) * n - 9 * (m : ℤ) ^ 2 - 3 * m - 2 * hookFlag m := by
  obtain ⟨D⟩ := exists_skolem m
  have hp := pathPacking_bound n D.differenceFamily
  have hm := D.differenceFamily_mass
  have hs : (∑ i : Fin m, ((n - D.differenceFamily.span i : ℕ) : ℤ)) =
      (m : ℤ) * n - ∑ i : Fin m, (D.differenceFamily.span i : ℤ) := by
    calc
      _ = ∑ i : Fin m, ((n : ℤ) - D.differenceFamily.span i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hb : D.differenceFamily.span i ≤ n := (D.differenceFamily.bounded i).trans hn
        exact Nat.cast_sub hb
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hp' : (∑ i : Fin m, ((n - D.differenceFamily.span i : ℕ) : ℤ)) ≤
      (packingNumber (pathPower n (3 * m + hookFlag m)) : ℤ) := by exact_mod_cast hp
  nlinarith

theorem pathPower_mono (n : ℕ) {k ℓ : ℕ} (hk : k ≤ ℓ) : pathPower n k ≤ pathPower n ℓ :=
  fun _ _ h => ⟨h.1, h.2.trans hk⟩

theorem skolem_path_bound_of_le (n k m : ℕ) (hm : 3 * m + hookFlag m ≤ k) (hn : k ≤ n) :
    4 * (packingNumber (pathPower n k) : ℤ) ≥
      4 * (m : ℤ) * n - 9 * (m : ℤ) ^ 2 - 3 * m - 2 * hookFlag m := by
  have hb := skolem_path_bound n m (hm.trans hn)
  have hp := packingNumber_mono (pathPower_mono n hm)
  have hp' : (packingNumber (pathPower n (3 * m + hookFlag m)) : ℤ) ≤
      packingNumber (pathPower n k) := by exact_mod_cast hp
  linarith

end ResearchMain.PathCycleTuza
