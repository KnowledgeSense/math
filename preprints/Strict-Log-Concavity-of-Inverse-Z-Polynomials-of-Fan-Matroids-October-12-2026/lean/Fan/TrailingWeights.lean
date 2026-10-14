import Fan.BoundaryWeights
import Fan.HubSuffixIntervals

namespace Fan
open Finset Polynomial
open scoped Classical

theorem flatWeight_joined_top {m : ℕ} (p : Configuration m) (hp : EndsNonhub p) (r : ℕ) :
    flatWeight (joinedConfiguration p (⊤ : Configuration r) (hp.compatible _))=flatWeight p*Q r := by
  unfold flatWeight
  have hr := joinPair_rank p (⊤ : Configuration r) (hp.compatible _)
  change configurationRank (joinedConfiguration p (⊤ : Configuration r) (hp.compatible _))=_ at hr
  rw [hr,configuration_top_rank,upperMu_joined_top p hp r,lowerQ_join]
  have he : m+r-(configurationRank p+r)=m-configurationRank p := by omega
  rw [he]
  change _ = _ * lowerQ (⊤ : Configuration r)
  ring

theorem flatWeight_trailingAssemble (n : ℕ) (x : Trailing n) :
    flatWeight (trailingAssemble n x)=flatWeight x.2.val*Q (n-x.1.val) := by
  unfold trailingAssemble
  rw [configurationCast_weight,flatWeight_joined_top x.2.val x.2.property]

theorem inverseZ_convolution (n : ℕ) :
    inverseZ n=∑ m : Fin (n+1), prefixWeightSum m.val * Q (n-m.val) := by
  rw [inverseZ_sum_weights,sum_trailing]
  apply sum_congr rfl
  intro m _
  simp only [flatWeight_trailingAssemble]
  rw [← sum_mul]
  rfl

end Fan
