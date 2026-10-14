import R34.Transfer
import R34.SchurIsing

open scoped BigOperators

namespace R34.ModelReduction

noncomputable section

open Transfer

def Gsite (j : ℕ) : Mat :=
  Matrix.diagonal ![(U + V) ^ j, S * T ^ j, T * S ^ j]

def Jsite (j : ℕ) : Mat :=
  Matrix.diagonal ![MvPolynomial.C (j : ℝ) * V * U ^ (j - 1),
    S * T ^ j, T * S ^ j]

def Gword (word : List ℕ) : Poly := value (word.map Gsite)
def Jword (word : List ℕ) : Poly := value (word.map Jsite)

def vacancyResidual (j : ℕ) : Poly :=
  (U + V) ^ j - MvPolynomial.C (j : ℝ) * V * U ^ (j - 1)

def powerRemainder (j : ℕ) : Poly := (U + V) ^ j - U ^ j

theorem powerRemainder_succ (j : ℕ) :
    powerRemainder (j + 1) = U * powerRemainder j + V * (U + V) ^ j := by
  simp only [powerRemainder, pow_succ]
  ring

theorem vacancyResidual_succ (j : ℕ) :
    vacancyResidual (j + 1) = U * vacancyResidual j + V * powerRemainder j := by
  cases j with
  | zero => simp [vacancyResidual, powerRemainder]
  | succ j =>
    simp only [vacancyResidual, powerRemainder,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_add, map_one, pow_succ]
    ring

theorem powerRemainder_schur (j : ℕ) : SchurPositive (powerRemainder j) := by
  induction j with
  | zero => simpa [powerRemainder] using SchurPositive.zero
  | succ j ih =>
    rw [powerRemainder_succ]
    exact schurPositive_add (schurPositive_mul schurPositive_U ih)
      (schurPositive_mul schurPositive_V
        (schurPositive_pow (schurPositive_add schurPositive_U schurPositive_V) j))

theorem vacancyResidual_schur (j : ℕ) : SchurPositive (vacancyResidual j) := by
  induction j with
  | zero => simpa [vacancyResidual] using schurPositive_one
  | succ j ih =>
    rw [vacancyResidual_succ]
    exact schurPositive_add (schurPositive_mul schurPositive_U ih)
      (schurPositive_mul schurPositive_V (powerRemainder_schur j))

def positiveCount : List ℕ → ℕ
  | [] => 0
  | j :: js => (if j = 0 then 0 else 1) + positiveCount js

def siteFactor (j : ℕ) : Poly := if j = 0 then 1 else V

theorem Jsite_normalized (j : ℕ) :
    Jsite j = siteFactor j • normalizedMatrix j := by
  cases j with
  | zero =>
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      simp [Jsite, siteFactor, normalizedMatrix, normalizedWeight,
        Matrix.smul_apply, smul_eq_mul,
        R34.S, R34.T, Transfer.S, Transfer.T]
  | succ j =>
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      simp [Jsite, siteFactor, normalizedMatrix, normalizedWeight,
        Matrix.smul_apply, smul_eq_mul, pow_succ,
        R34.S, R34.T, R34.U, R34.V,
        Transfer.S, Transfer.T, Transfer.U] <;> ring

theorem chain_cons (M : Mat) (sites : List Mat) :
    chain (M :: sites) = compatibility * M * chain sites := by
  simp [chain]

theorem chain_Jsite (word : List ℕ) :
    chain (word.map Jsite) =
      V ^ positiveCount word • chain (word.map normalizedMatrix) := by
  induction word with
  | nil => simp [positiveCount]
  | cons j js ih =>
    simp only [List.map_cons, chain_cons]
    rw [Jsite_normalized, ih]
    by_cases hj : j = 0
    · simp [siteFactor, hj, positiveCount, Matrix.mul_smul]
    · simp only [siteFactor, hj, ite_false, positiveCount]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.one_add, pow_succ]

theorem Jword_normalized (word : List ℕ) :
    Jword word = V ^ positiveCount word * normalizedModel word := by
  unfold Jword normalizedModel value
  rw [chain_Jsite]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem Gsite_split (j : ℕ) :
    Gsite j = Jsite j + vacancyResidual j • unitEntry 0 0 := by
  apply Matrix.ext
  intro i k
  fin_cases i <;> fin_cases k <;>
    simp [Gsite, Jsite, vacancyResidual, unitEntry,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

def mixed (leftWord rightWord : List ℕ) : Poly :=
  value (leftWord.map Jsite ++ rightWord.map Gsite)

theorem mixed_step (leftWord rightWord : List ℕ) (j : ℕ) :
    mixed leftWord (j :: rightWord) = mixed (leftWord ++ [j]) rightWord +
      vacancyResidual j * Jword leftWord * Gword rightWord := by
  have h : mixed leftWord (j :: rightWord) =
      value (leftWord.map Jsite ++ [Gsite j] ++ rightWord.map Gsite) := by
    simp [mixed, List.append_assoc]
  rw [h, Gsite_split, value_add_site, value_weighted_separator]
  simp [mixed, Jword, Gword, List.map_append, List.append_assoc]

theorem Gword_schur
    (hn : ∀ word : List ℕ, SchurPositive (normalizedModel word))
    (word : List ℕ) : SchurPositive (Gword word) := by
  have hj : ∀ w : List ℕ, SchurPositive (Jword w) := by
    intro w
    rw [Jword_normalized]
    exact schurPositive_mul (schurPositive_pow schurPositive_V _) (hn w)
  have hm : ∀ rightWord leftWord : List ℕ, SchurPositive (mixed leftWord rightWord) := by
    intro rightWord
    induction rightWord with
    | nil =>
      intro leftWord
      simpa [mixed, Jword] using hj leftWord
    | cons j rightWord ih =>
      intro leftWord
      rw [mixed_step]
      exact schurPositive_add (ih (leftWord ++ [j]))
        (schurPositive_mul
          (schurPositive_mul (vacancyResidual_schur j) (hj leftWord))
          (by simpa [mixed, Gword] using ih []))
  simpa [mixed, Gword] using hm word []

end

end R34.ModelReduction
