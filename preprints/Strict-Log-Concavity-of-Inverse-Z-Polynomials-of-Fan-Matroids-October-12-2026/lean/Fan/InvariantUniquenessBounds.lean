import Fan.InvariantUniquenessSymmetry
import Fan.ConfigurationBounds
import ThagomizerTuran.InverseKLDegree

namespace Fan

theorem Q_high_coeff (n j : ℕ) (hn : 0 < n) (hj : n ≤ 2 * j) :
    (Q n).coeff j = 0 := by
  classical
  apply MatroidInverseZ.inverseKL_high_coeff configurationRank
    (configurationRank_strictMono n).monotone _ _ bot_le
  · intro h
    have he := congrArg configurationRank h
    simp only [configuration_bot_rank, configuration_top_rank] at he
    omega
  · simpa only [configuration_bot_rank, configuration_top_rank, Nat.sub_zero] using hj

theorem inverseZ_rank_reflect (n : ℕ) :
    Polynomial.reflect n (inverseZ n) = inverseZ n := by
  classical
  rw [inverseZ_configuration]
  simpa only [configurationBottom_rank, configurationTop_rank, Nat.sub_zero] using
    MatroidInverseZ.inverseZ_reflect configurationRank
      (configurationRank_strictMono n).monotone (configurationBottom n) (configurationTop n)

theorem inverseZ_rank_coeff_symm (n j : ℕ) (hj : j ≤ n) :
    (inverseZ n).coeff j = (inverseZ n).coeff (n - j) := by
  classical
  rw [inverseZ_configuration]
  simpa only [configurationBottom_rank, configurationTop_rank, Nat.sub_zero] using
    MatroidInverseZ.inverseZ_coeff_symm configurationRank
      (configurationRank_strictMono n).monotone (configurationBottom n) (configurationTop n) j
      (by simpa only [configurationBottom_rank, configurationTop_rank, Nat.sub_zero] using hj)

end Fan
