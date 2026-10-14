import BoseBurton.BoseZ
import BoseBurton.RankEnumeratorCoefficients

noncomputable section
namespace BoseBurton
open Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

omit [Module.Finite K V] [Finite V] in
theorem span_bot_ne_top (W : Submodule K V) (hW : W ≠ ⊤) :
    (⊥ : FlatSpan W) ≠ spanTop W hW := by
  intro h
  have hh : (⊥ : Submodule K V) = ⊤ := congrArg Subtype.val h
  apply hW
  apply top_le_iff.mp
  rw [← hh]
  exact bot_le

omit [Module.Finite K V] in
theorem spanP_high_coeff (W : Submodule K V) (hW : W ≠ ⊤) (k : ℕ)
    (hk : finrank K V ≤ 2*k) : (spanP W hW).coeff k = 0 := by
  apply kl_high_coeff (spanRank W) ⊥ (spanTop W hW) (span_bot_ne_top W hW)
  simpa only [spanRank_top, spanRank_bot, Nat.sub_zero] using hk

theorem spanZ_coeff_symm (W : Submodule K V) (hW : W ≠ ⊤) (k : ℕ)
    (hk : k ≤ finrank K V) :
    (spanZ W hW).coeff k = (spanZ W hW).coeff (finrank K V-k) := by
  simpa only [spanZ, spanRank_top, spanRank_bot, Nat.sub_zero] using
    zKernel_coeff_symm (spanRank W) (spanRank_strictMono W).monotone
      ⊥ (spanTop W hW) k (by simpa using hk)

theorem spanZ_coeff_upper (W : Submodule K V) (hW : W ≠ ⊤) (k : ℕ)
    (hk : finrank K V ≤ 2*k) :
    (spanZ W hW).coeff k = (projectiveRankEnumerator K V).coeff k -
      (projectiveRankEnumerator K W).coeff k := by
  rw [spanZ_decomposition, coeff_sub, coeff_add, spanP_high_coeff W hW k hk, zero_add]

/-- The exact full restricted-Z row, with the even center counted once. -/
theorem spanZ_coeff (W : Submodule K V) (hW : W ≠ ⊤) (k : ℕ)
    (hk : k ≤ finrank K V) :
    (spanZ W hW).coeff k = (projectiveRankEnumerator K V).coeff k -
      (projectiveRankEnumerator K W).coeff (max k (finrank K V-k)) := by
  by_cases h : finrank K V-k ≤ k
  · rw [max_eq_left h]
    exact spanZ_coeff_upper W hW k (by omega)
  · have hh : k ≤ finrank K V-k := by omega
    rw [max_eq_right hh, spanZ_coeff_symm W hW k hk,
      spanZ_coeff_upper W hW (finrank K V-k) (by omega),
      ← projectiveRankEnumerator_coeff_symm k hk]

theorem spanZ_coeff_above (W : Submodule K V) (hW : W ≠ ⊤) (k : ℕ)
    (hk : finrank K V < k) : (spanZ W hW).coeff k = 0 := by
  rw [spanZ_coeff_upper W hW k (by omega), projectiveRankEnumerator_coeff_above k hk,
    projectiveRankEnumerator_coeff_above k (lt_of_le_of_lt (Submodule.finrank_le W) hk), sub_self]

end BoseBurton
