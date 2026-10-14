import TerminalLogConcavity.ReleaseTree
import TerminalLogConcavity.WeightedPath
import TerminalLogConcavity.BlockEnvelope

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

private theorem constant_mono {a b : ℕ} (h : a ≤ b) : CoeffLE (C a) (C b) := by
  intro n
  by_cases hn : n = 0 <;> simp [hn, h]

theorem Block.scaled_constant_le_B (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    CoeffLE (C (amplifier t ^ p)) (Block.scaled t p).B :=
  (constant_mono (Block.scaled_d_lower t hp)).trans (Block.scaled t p).d_le_B

noncomputable def lowerSiteP (q t i : ℕ) : ℕ[X] :=
  1 + C (amplifier t ^ (2 * interfaceParameter q i)) * X

noncomputable def lowerSiteWeight (q t i k : ℕ) : ℕ[X] × ℕ[X] :=
  (lowerSiteP q t i, lowerSiteP q t i + C (amplifier t ^ siteParameter q i k))
noncomputable def lowerCouplerWeight (q t : ℕ) : ℕ[X] × ℕ[X] :=
  (1, C (amplifier t ^ (2 * baseCoupling q)))

theorem site_lower_weights {q : ℕ} (hq : 1 ≤ q) (t i k : ℕ) :
    CoeffLE (lowerSiteWeight q t i k).1 (siteDecoration q t i k).A ∧
    CoeffLE (lowerSiteWeight q t i k).2 (siteDecoration q t i k).B := by
  let p := Block.scaled t (siteParameter q i k)
  let m := Block.scaled t (interfaceParameter q i)
  have hp := Block.scaled_constant_le_B t (show 1 ≤ siteParameter q i k by have := siteParameter_pos (i := i) (k := k) hq; omega)
  have hmpos : 1 ≤ interfaceParameter q i := by
    unfold interfaceParameter massParameter
    have : 0 < q ^ 2 := by positivity
    omega
  have hm := Block.scaled_constant_le_B t hmpos
  have hE : CoeffLE (lowerSiteP q t i) (interfaceE p m) := by
    have h := p.one_le_A.mul ((m.one_le_A.pow 2).add ((CoeffLE.refl X).mul (hm.pow 2)))
    have hpow : (C (amplifier t ^ interfaceParameter q i) : ℕ[X]) ^ 2 =
        C (amplifier t ^ (2 * interfaceParameter q i)) := by
      rw [← C_pow, ← pow_mul, Nat.mul_comm (interfaceParameter q i) 2]
    change CoeffLE (1 + C (amplifier t ^ (2 * interfaceParameter q i)) * X)
      (p.A * (m.A ^ 2 + X * m.B ^ 2))
    simpa only [one_pow, one_mul, hpow, mul_comm] using h
  have hO : CoeffLE (C (amplifier t ^ siteParameter q i k)) (interfaceO p m) := by
    change CoeffLE (C (amplifier t ^ siteParameter q i k)) (p.B * m.A ^ 2)
    simpa only [one_pow, mul_one] using hp.mul (m.one_le_A.pow 2)
  change CoeffLE (lowerSiteP q t i) _ ∧ CoeffLE (lowerSiteP q t i + C _) _
  simp only [siteDecoration, interfaceDecoration_A, interfaceDecoration_B]
  exact ⟨hE.trans (CoeffLE.le_add_right _ _), hE.add hO⟩

theorem coupler_lower_weights {q : ℕ} (hq : 1 ≤ q) (t : ℕ) :
    CoeffLE (lowerCouplerWeight q t).1 (couplerDecoration q t).A ∧
    CoeffLE (lowerCouplerWeight q t).2 (couplerDecoration q t).B := by
  have hp : 1 ≤ 2 * baseCoupling q := by
    unfold baseCoupling
    have : 0 < q ^ 2 := by positivity
    omega
  simp only [couplerDecoration, Block.decoration_A, Block.decoration_B]
  exact ⟨(Block.scaled t _).one_le_A, Block.scaled_constant_le_B t hp⟩

end TerminalLogConcavity
