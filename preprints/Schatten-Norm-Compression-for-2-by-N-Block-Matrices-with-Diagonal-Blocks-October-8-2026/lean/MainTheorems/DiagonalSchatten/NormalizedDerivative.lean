import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped Topology

theorem normalized_rpow_quotient_deriv {s n d : ℝ → ℝ} {x s' n' d' q : ℝ}
    (hs : HasDerivAt s s' x) (hn : HasDerivAt n n' x) (hd : HasDerivAt d d' x)
    (hpos : 0 < d x) :
    ∃ v : ℝ, HasDerivAt (fun y => s y * n y / d y ^ q) v x ∧
      v * d x ^ (q + 1) = s' * n x * d x + s x * n' * d x - q * s x * n x * d' := by
  let v := (s' * n x + s x * n') * d x ^ (-q) +
    s x * n x * (-q * d x ^ (-q - 1) * d')
  have hpow := hd.rpow_const (p := -q) (Or.inl hpos.ne')
  have hprod : HasDerivAt (fun y => s y * n y * d y ^ (-q)) v x := by
    convert! (hs.mul hn).mul hpow using 1
    dsimp [v]
    ring
  have heq : (fun y => s y * n y / d y ^ q) =ᶠ[𝓝 x]
      (fun y => s y * n y * d y ^ (-q)) := by
    filter_upwards [hd.continuousAt.eventually (eventually_gt_nhds hpos)] with y hy
    rw [Real.rpow_neg hy.le, div_eq_mul_inv]
  refine ⟨v, hprod.congr_of_eventuallyEq heq, ?_⟩
  have h1 : d x ^ (-q) * d x ^ (q + 1) = d x := by
    rw [← Real.rpow_add hpos, show -q + (q + 1) = 1 by ring, Real.rpow_one]
  have h2 : d x ^ (-q - 1) * d x ^ (q + 1) = 1 := by
    rw [← Real.rpow_add hpos, show -q - 1 + (q + 1) = 0 by ring, Real.rpow_zero]
  calc
    v * d x ^ (q + 1) =
        (s' * n x + s x * n') * (d x ^ (-q) * d x ^ (q + 1)) -
          q * s x * n x * d' * (d x ^ (-q - 1) * d x ^ (q + 1)) := by
      dsimp [v]
      ring
    _ = _ := by rw [h1, h2]; ring

end

end ResearchMain.DiagonalSchatten
