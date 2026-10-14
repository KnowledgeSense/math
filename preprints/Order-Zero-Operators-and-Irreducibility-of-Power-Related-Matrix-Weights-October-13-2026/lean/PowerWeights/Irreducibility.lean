import PowerWeights.WeightSymmetry

noncomputable section

namespace PowerWeights

open MeasureTheory

/-- A nontrivial block reduction by one fixed nonsingular complex congruence. -/
def ReducibleByConstantCongruence {N : ℕ} (I : Set ℝ)
    (W : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∃ M : Matrix (Fin N) (Fin N) ℂ, IsUnit M ∧
    ∃ S : Finset (Fin N), S.Nonempty ∧ S≠Finset.univ ∧
      ∀ᵐ x ∂volume.restrict I, ∀ i j : Fin N,
        ¬(i∈S ↔ j∈S) → (M*W x*M.conjTranspose) i j=0

def blockProjection {N : ℕ} (S : Finset (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if i∈S then 1 else 0

 theorem blockProjection_hermitian {N : ℕ} (S : Finset (Fin N)) :
    (blockProjection S).conjTranspose=blockProjection S := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [blockProjection,Matrix.conjTranspose_apply,Matrix.diagonal]
  · simp [blockProjection,Matrix.conjTranspose_apply,Matrix.diagonal,hij,Ne.symm hij]

 theorem blockProjection_commutes {N : ℕ} (S : Finset (Fin N))
    (V : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ i j, ¬(i∈S ↔ j∈S) → V i j=0) :
    blockProjection S*V=V*blockProjection S := by
  ext i j
  simp only [blockProjection,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi : i∈S <;> by_cases hj : j∈S
  · simp [hi,hj]
  · simp [hi,hj,h i j (by simp [hi,hj])]
  · simp [hi,hj,h i j (by simp [hi,hj])]
  · simp [hi,hj]

 theorem reduction_gives_symmetry {N : ℕ} {I : Set ℝ}
    (W : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (M : Matrix (Fin N) (Fin N) ℂ) (hM : IsUnit M) (S : Finset (Fin N))
    (h : ∀ᵐ x ∂volume.restrict I, ∀ i j : Fin N,
      ¬(i∈S ↔ j∈S) → (M*W x*M.conjTranspose) i j=0) :
    WeightSymmetric I W (M⁻¹*blockProjection S*M) := by
  let : Invertible M := hM.invertible
  have hleft : M⁻¹*M=1 := Matrix.inv_mul_of_invertible M
  have hright : M*M⁻¹=1 := Matrix.mul_inv_of_invertible M
  have hstar : M.conjTranspose*(M⁻¹).conjTranspose=1 := by
    rw [← Matrix.conjTranspose_mul,hleft,Matrix.conjTranspose_one]
  filter_upwards [h] with x hx
  have he := blockProjection_commutes S (M*W x*M.conjTranspose) hx
  have hh := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => M⁻¹*A*(M⁻¹).conjTranspose) he
  have hl : M⁻¹*(blockProjection S*(M*W x*M.conjTranspose))*(M⁻¹).conjTranspose =
      (M⁻¹*blockProjection S*M)*W x := by
    calc
      _ = (M⁻¹*blockProjection S*M)*W x*(M.conjTranspose*(M⁻¹).conjTranspose) := by
        simp only [mul_assoc]
      _ = _ := by rw [hstar,mul_one]
  have hr : M⁻¹*((M*W x*M.conjTranspose)*blockProjection S)*(M⁻¹).conjTranspose =
      W x*(M⁻¹*blockProjection S*M).conjTranspose := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,blockProjection_hermitian]
    calc
      _ = (M⁻¹*M)*(W x*(M.conjTranspose*blockProjection S*(M⁻¹).conjTranspose)) := by
        simp only [mul_assoc]
      _ = _ := by simp only [hleft,one_mul,mul_assoc]
  exact hl.symm.trans (hh.trans hr)

/-- Constant-congruence irreducibility of both actual matrix-weight families.
This conclusion does not require choosing an orthogonal-polynomial sequence. -/
theorem not_reducible_by_constant_congruence {N : ℕ} (hN : 0<N) (s : Schedule)
    (a : ℕ → ℝ) (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) :
    ¬ReducibleByConstantCongruence I (weight N s a w) := by
  rintro ⟨M,hM,S,hSne,hSnot,hblock⟩
  let : Invertible M := hM.invertible
  have hs := reduction_gives_symmetry (weight N s a w) M hM S hblock
  obtain ⟨c,hc⟩ := (weight_symmetric_iff_real_scalar hN s a ha H _).mp hs
  have he : blockProjection S=(c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    calc
      _ = M*(M⁻¹*blockProjection S*M)*M⁻¹ := by
        simp [Matrix.mul_inv_of_invertible,mul_assoc]
      _ = M*((c : ℂ) • 1)*M⁻¹ := by rw [hc]
      _ = _ := by simp [Matrix.mul_inv_of_invertible]
  obtain ⟨i,hi⟩ := hSne
  have hjex : ∃ j : Fin N, j∉S := by
    by_contra hh
    apply hSnot
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    exact hh ⟨j,hj⟩
  obtain ⟨j,hj⟩ := hjex
  have hei := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A i i) he
  have hej := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A j j) he
  simp [blockProjection,hi] at hei
  simp [blockProjection,hj] at hej
  exact one_ne_zero (hei.trans hej.symm)

end PowerWeights
