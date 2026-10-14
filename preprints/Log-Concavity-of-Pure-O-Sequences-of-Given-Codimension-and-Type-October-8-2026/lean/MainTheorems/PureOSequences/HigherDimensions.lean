import MainTheorems.PureOSequences.BlockMonomials
import MainTheorems.PureOSequences.Boxes

namespace ResearchMain.PureOSequences

open Classical

def higherDegree (k t : ℕ) : ℕ := t + 4 * k + 66

noncomputable def higherFlat (k t : ℕ) : Monomial (4 + k) :=
  blockMonomial (k + 14) (k + 14) (higherDegree k t - 2 * k - 28) 0 (fun _ => 0)

noncomputable def higherTube (k t q : ℕ) : Monomial (4 + k) :=
  blockMonomial (higherDegree k t - k - 12 - q) (4 + q) 4 4 (fun _ => 1)

noncomputable def higherTubeGenerators (k t : ℕ) : Finset (Monomial (4 + k)) :=
  (Finset.range (t - 1)).image (higherTube k t)

noncomputable def higherGenerators (k t : ℕ) : Finset (Monomial (4 + k)) :=
  insert (higherFlat k t) (higherTubeGenerators k t)

theorem higherFlat_degree (k t : ℕ) : totalDeg (higherFlat k t) = higherDegree k t := by
  simp only [higherFlat, degree_blockMonomial, Finset.sum_const_zero, add_zero]
  unfold higherDegree
  omega

theorem higherTube_degree (k t q : ℕ) (hq : q < t - 1) :
    totalDeg (higherTube k t q) = higherDegree k t := by
  simp only [higherTube, degree_blockMonomial, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  unfold higherDegree
  omega

theorem higherGenerators_degree (k t : ℕ) :
    ∀ m ∈ higherGenerators k t, totalDeg m = higherDegree k t := by
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · exact higherFlat_degree k t
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    exact higherTube_degree k t q (Finset.mem_range.mp hq)

theorem higherGenerators_nonempty (k t : ℕ) : (higherGenerators k t).Nonempty :=
  ⟨higherFlat k t, Finset.mem_insert_self _ _⟩

noncomputable def higherIdeal (k t : ℕ) : PureOrderIdeal (4 + k) :=
  pureGenerated (higherGenerators k t) (higherGenerators_degree k t)
    (higherGenerators_nonempty k t)

theorem higherTube_injective (k t : ℕ) : Function.Injective (higherTube k t) := by
  intro q p heq
  have h := congrArg (fun m => m (Fin.castAdd k 1)) heq
  simpa only [higherTube, blockMonomial_left, Matrix.cons_val_one, Matrix.cons_val_zero,
    add_right_inj] using h

theorem higherFlat_not_mem (k t : ℕ) : higherFlat k t ∉ higherTubeGenerators k t := by
  intro h
  obtain ⟨q, _, heq⟩ := Finset.mem_image.mp h
  have h := congrArg (fun m => m (Fin.castAdd k 3)) heq
  norm_num [higherTube, higherFlat] at h

theorem higherIdeal_type (k t : ℕ) (ht : 2 ≤ t) : typePO (higherIdeal k t) = t := by
  rw [higherIdeal, type_pureGenerated, higherGenerators,
    Finset.card_insert_of_notMem (higherFlat_not_mem k t), higherTubeGenerators,
    Finset.card_image_of_injective _ (higherTube_injective k t), Finset.card_range]
  omega

theorem higherIdeal_usesEveryVariable (k t : ℕ) (ht : 2 ≤ t) :
    UsesEveryVariable (higherIdeal k t) := by
  intro i
  refine ⟨higherTube k t 0, mem_generatedOrderIdeal_iff.mpr ⟨higherTube k t 0, ?_,
    le_rfl⟩, ?_⟩
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j <;> simp [higherTube, higherDegree]
      omega
    · simp [higherTube]

theorem quadratic_less_than_exponential (k : ℕ) : (k + 14) * (k + 15) < 250 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hstep : (k + 15) * (k + 16) ≤ 2 * ((k + 14) * (k + 15)) := by nlinarith
    calc
      _ ≤ 2 * ((k + 14) * (k + 15)) := by simpa only [Nat.add_assoc] using hstep
      _ < 2 * (250 * 2 ^ k) := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ = _ := by rw [pow_succ]; ring

theorem higher_defect_negative (k t : ℕ) (ht : 2 ≤ t) :
    (k + 14) * (k + 15) < 50 * (t + 3) * 2 ^ k := by
  exact (quadratic_less_than_exponential k).trans_le
    (Nat.mul_le_mul_right (2 ^ k) (by nlinarith))

end ResearchMain.PureOSequences
