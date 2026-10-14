import Dowling.DowlingApexTransfer
import Dowling.DowlingApexClosedCurvature
import Dowling.ActualApexWeightsSingleClosed
import Dowling.DowlingWeightedMixtureStrict

noncomputable section
namespace Dowling

theorem apexNormalizedWeight_budget (n k j : ℕ) (hk : 1≤k) (hkn : k≤n)
    (hj : 1≤j) (hjn : 2*(j+1)≤n) :
    apexNormalizedWeight n k (j-1)+apexNormalizedWeight n k (j+1)-
      2*apexNormalizedWeight n k j≤
      (1/((j:ℝ)+1)+1/(((n:ℝ)+1)/2-j)^2)*apexNormalizedWeight n k j := by
  apply apexNormalizedWeight_budget_transfer n k j _ (by positivity) hk hkn hj hjn
  rw [apexNormalizedWeight_one_closed n (j-1) (by omega) (by omega),
    apexNormalizedWeight_one_closed n (j+1) (by omega) hjn,
    apexNormalizedWeight_one_closed n j (by omega) (by omega)]
  exact (apexClosedNormalizedWeight_budget n j hj hjn).le

theorem apexRaisedWeight_pos (n k j : ℕ) (hn : 2≤n) (hk : 1≤k)
    (hkn : k≤n) (hj : 2*j≤n) : 0<apexRaisedWeight n k j :=
  mul_pos (dowlingBaseWeight_pos (by norm_num) n j hj)
    (apexNormalizedWeight_pos n k j hn hk hkn hj)

theorem apexRaisedWeight_strict (n k j : ℕ) (hk : 1≤k) (hkn : k≤n)
    (hj : 1≤j) (hjn : 2*(j+1)≤n) :
    apexRaisedWeight n k (j-1)*apexRaisedWeight n k (j+1)<(apexRaisedWeight n k j)^2 := by
  have hjR : (1:ℝ)≤j := by exact_mod_cast hj
  have hnR : (2*(j+1):ℝ)≤n := by exact_mod_cast hjn
  have hr : 1<((n:ℝ)+1)/2-j := by linarith
  have hA0 : (0:ℝ)<1/((j:ℝ)+1) := by positivity
  have hA1 : 1/((j:ℝ)+1)<(1:ℝ) := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hB0 : (0:ℝ)<1/(((n:ℝ)+1)/2-j)^2 := by positivity
  have hB1 : 1/(((n:ℝ)+1)/2-j)^2<(1:ℝ) := by
    apply (div_lt_one (sq_pos_of_pos (by linarith))).mpr
    nlinarith
  exact dowling_curvature_payment hA0 hA1 hB0 hB1
    (dowlingBaseWeight_pos (by norm_num) n (j-1) (by omega))
    (dowlingBaseWeight_pos (by norm_num) n j (by omega))
    (dowlingBaseWeight_pos (by norm_num) n (j+1) hjn)
    (apexNormalizedWeight_pos n k (j-1) (by omega) hk hkn (by omega)).le
    (apexNormalizedWeight_pos n k j (by omega) hk hkn (by omega))
    (apexNormalizedWeight_pos n k (j+1) (by omega) hk hkn hjn).le
    (dowlingBaseWeight_curvature (a:=1) (by norm_num) n j hj hjn)
    (apexNormalizedWeight_budget n k j hk hkn hj hjn)

def apexScalar (n k b : ℕ) : ℝ := weightedMixtureCoefficient (apexRaisedWeight n k) 2 n b

theorem apexScalar_pos (n k b : ℕ) (hn : 2≤n) (hk : 1≤k) (hkn : k≤n)
    (hb : b≤n) : 0<apexScalar n k b := by
  rw [apexScalar,← weightedMixtureFunction_sum]
  exact weightedMixtureFunction_sum_pos n b
    (fun j hj=>apexRaisedWeight_pos n k j hn hk hkn hj) (by norm_num) hb

theorem apexScalar_strict_log_concave (n k b : ℕ) (hn : 2≤n) (hk : 1≤k) (hkn : k≤n)
    (hb : 1≤b) (hbn : b<n) :
    apexScalar n k (b-1)*apexScalar n k (b+1)<(apexScalar n k b)^2 := by
  exact weightedMixtureCoefficient_strict_of_log_concave n b
    (fun j hj=>apexRaisedWeight_pos n k j hn hk hkn hj)
    (fun j hj hjn=>(apexRaisedWeight_strict n k j hk hkn hj hjn).le)
    (by norm_num) hb hbn

end Dowling
