import TerminalLogConcavity.Parameters
import TerminalLogConcavity.BlockEntropy

namespace TerminalLogConcavity

def baseCoupling (q : ℕ) : ℕ := 2 * q ^ 2
def massParameter (q : ℕ) : ℕ := 4 * q ^ 2
def endpointWeight (q k : ℕ) : ℕ := if k = 1 ∨ k = q then 1 else 2
def siteParameter (q i k : ℕ) : ℕ := baseCoupling q * endpointWeight q k + if k = 1 then i ^ 2 else 0
def interfaceParameter (q i : ℕ) : ℕ := massParameter q + i

theorem siteParameter_le {q i k : ℕ} (hi : i ≤ q) : siteParameter q i k ≤ massParameter q := by
  have hisq := Nat.pow_le_pow_left hi 2
  unfold siteParameter endpointWeight baseCoupling massParameter
  by_cases hk : k = 1
  · simp [hk]; nlinarith
  · simp only [ite_eq_right hk, add_zero]
    split <;> omega

theorem siteParameter_pos {q i k : ℕ} (hq : 1 ≤ q) : 0 < siteParameter q i k := by
  unfold siteParameter endpointWeight baseCoupling
  split <;> split <;> have : 0 < q ^ 2 := by positivity
  all_goals omega

theorem interfaceParameter_le {q i : ℕ} (hi : i ≤ q) :
    interfaceParameter q i ≤ massParameter q + q := by
  unfold interfaceParameter
  omega

theorem selectedAmplifier_ge_128 {q H : ℕ} (hq : 1 ≤ q) (hH : 1 ≤ H) :
    128 * q ^ 4 ≤ selectedAmplifier q H := by
  have hpow : 128 ≤ 2 ^ (q + 10) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ q + 10 by omega)
    norm_num at h
    exact h
  have hbase := Nat.mul_le_mul_right (q ^ 4) hpow
  have hm : 2 ^ (q + 10) * q ^ 4 ≤ target q H := by
    unfold target
    simpa using Nat.mul_le_mul_left (2 ^ (q + 10) * q ^ 4) hH
  exact hbase.trans (hm.trans (selectedAmplifier_bounds hq hH).1)

theorem occurring_parameter_small {q H p : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hp : p ≤ massParameter q + q) : 4 * p ≤ selectedAmplifier q H := by
  have ha := selectedAmplifier_ge_128 (by omega : 1 ≤ q) hH
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith
  unfold massParameter at hp
  nlinarith

theorem occurring_block_d_bound {q H p : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hp : 1 ≤ p) (hpmax : p ≤ massParameter q + q) :
    ((Block.scaled (thresholdIndex (target q H)) p).d : ℝ) ≤
      2 * (selectedAmplifier q H : ℝ) ^ p :=
  Block.scaled_d_le_twice_power _ hp (occurring_parameter_small hq hH hpmax)

end TerminalLogConcavity
