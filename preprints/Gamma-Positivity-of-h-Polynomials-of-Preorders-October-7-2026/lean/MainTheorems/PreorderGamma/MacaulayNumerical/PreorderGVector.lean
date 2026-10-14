import MainTheorems.PreorderGamma.MacaulayNumerical.DownsetInequalities
import MainTheorems.PreorderGamma.MacaulayNumerical.BinomialCascade
import MainTheorems.PreorderGamma.Macaulay.SquarefreeDownset
import MainTheorems.PreorderGamma.RootHStar

namespace ResearchMain.PreorderGamma.MacaulayNumerical

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem preorder_g_macaulay_inequality {d : ℕ} (hd : 0 < d) :
    supportGVector (E := E) (d + 1) ≤ macaulayRaise d (supportGVector (E := E) d) := by
  obtain ⟨F, _, hdown, hcount⟩ := Macaulay.preorder_g_squarefree_downset (E := E)
  have h := squarefree_downset_macaulay F hdown hd
  simpa only [degreeFamily, hcount] using h

theorem preorder_g_strict_cascade_bound {d : ℕ} (hd : 0 < d) :
    ∃ l : List (ℕ × ℕ), IsStrictCascade d l ∧
      cascadeValue l = supportGVector (E := E) d ∧
      supportGVector (E := E) (d + 1) ≤ cascadeRaiseValue l := by
  obtain ⟨l, hl, hvalue, hraise⟩ := strictCascade_exists hd (supportGVector (E := E) d)
  refine ⟨l, hl, hvalue, ?_⟩
  rw [hraise]
  exact preorder_g_macaulay_inequality (E := E) hd

theorem preorder_g_macaulay_conditions :
    supportGVector (E := E) 0 = 1 ∧
      ∀ d : ℕ, 0 < d →
        supportGVector (E := E) (d + 1) ≤ macaulayRaise d (supportGVector (E := E) d) :=
  ⟨supportGVector_zero, fun _ hd => preorder_g_macaulay_inequality hd⟩

theorem root_truncated_g_macaulay_inequality {d : ℕ} (hd : 0 < d) :
    ∃ m : ℕ, rootTruncatedGVector (E := E) d = (m : ℚ) ∧
      rootTruncatedGVector (E := E) (d + 1) ≤ (macaulayRaise d m : ℚ) := by
  refine ⟨supportGVector (E := E) d, rootTruncatedGVector_eq_support d, ?_⟩
  rw [rootTruncatedGVector_eq_support]
  exact_mod_cast preorder_g_macaulay_inequality (E := E) hd

end ResearchMain.PreorderGamma.MacaulayNumerical
