import PowerWeights.MomentBridge

namespace PowerWeights

open Polynomial MeasureTheory

/-- Constant symmetry for the original matrix weight, modulo null sets. -/
def WeightSymmetric {N : ℕ} (I : Set ℝ)
    (W : ℝ → Matrix (Fin N) (Fin N) ℂ) (F : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ᵐ x ∂volume.restrict I, F*W x=W x*F.conjTranspose

 theorem evaluate_sub {N : ℕ} (P Q : PolynomialMatrix N) (x : ℝ) :
    evaluate (P-Q) x=evaluate P x-evaluate Q x :=
  ((Polynomial.evalRingHom (x : ℂ)).mapMatrix).map_sub P Q

 theorem polynomial_symmetry_of_weight_symmetry {N : ℕ} {s : Schedule}
    {I : Set ℝ} {w : ℝ → ℝ} (H : AdmissibleWeight N s I w)
    (a : ℕ → ℝ) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : WeightSymmetric I (weight N s a w) F) :
    constant F*polynomialWeight N s a=polynomialWeight N s a*adjoint (constant F) := by
  let P := polynomialWeight N s a
  let Z := constant F*P-P*constant F.conjTranspose
  have hz : Z=0 := by
    apply Matrix.ext
    intro i j
    apply polynomial_zero_of_ae H.open_interval H.nonempty_interval (Z i j)
    filter_upwards [hF,H.positive] with x hx hw
    have hn : (w x : ℂ)≠0 := by exact_mod_cast (ne_of_gt hw)
    change F*((w x : ℂ) • evaluate P x)=((w x : ℂ) • evaluate P x)*F.conjTranspose at hx
    simp only [Matrix.mul_smul,Matrix.smul_mul] at hx
    have he : F*evaluate P x=evaluate P x*F.conjTranspose :=
      smul_right_injective _ hn hx
    have hZe : evaluate Z x=0 := by
      dsimp [Z]
      rw [evaluate_sub,evaluate_mul,evaluate_mul,evaluate_constant,evaluate_constant,he,sub_self]
    exact congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hZe
  simpa [Z,P,adjoint_constant] using sub_eq_zero.mp hz

 theorem weight_symmetric_iff_real_scalar {N : ℕ} (hN : 0<N) (s : Schedule)
    (a : ℕ → ℝ) (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (F : Matrix (Fin N) (Fin N) ℂ) :
    WeightSymmetric I (weight N s a w) F ↔
      ∃ c : ℝ, F=(c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  constructor
  · intro hF
    exact polynomial_symmetric_constants s a ha F
      (polynomial_symmetry_of_weight_symmetry H a F hF) hN
  · rintro ⟨c,rfl⟩
    filter_upwards [] with x
    simp [Matrix.conjTranspose_smul]

end PowerWeights
