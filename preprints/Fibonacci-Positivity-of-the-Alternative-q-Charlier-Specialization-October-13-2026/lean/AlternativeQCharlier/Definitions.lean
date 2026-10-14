import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# The alternative q-Charlier specialization
Indices for `x`, `y`, and `c` are zero based: index `n` denotes the
published index `n + 1`. The auxiliary sequence `t` retains index zero.
-/
namespace AlternativeQCharlier

noncomputable section

def ParameterBox (ρ q : ℝ) : Prop := 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < q ∧ q ≤ 1/5

def c (ρ q : ℝ) (n : ℕ) : ℝ :=
  q^n * (1 + ρ*q^n) / ((1 + ρ*q^(2*n+1)) * (1 + ρ*q^(2*n)))

def t (ρ q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => ρ*q^n*(1-q^(n+1))*(1+ρ*q^(2*n+3)) /
      ((1+ρ*q^(n+1))*(1+ρ*q^(2*n+1)))

def x (ρ q : ℝ) : ℕ → ℝ
  | 0 => (1+ρ*q⁻¹+ρ-ρ) / ((1+ρ*q⁻¹)*(1+ρ*q))
  | n+1 => q^(n+1)*(1+ρ*q^n+ρ*q^(n+1)-ρ*q^(2*n+2)) /
      ((1+ρ*q^(2*n+1))*(1+ρ*q^(2*n+3)))

def y (ρ q : ℝ) (n : ℕ) : ℝ :=
  ρ*q^(3*n+1)*(1-q^(n+1))*(1+ρ*q^n) /
    ((1+ρ*q^(2*n+2))*(1+ρ*q^(2*n+1))^2*(1+ρ*q^(2*n)))

/-- The source's tridiagonal matrix, using zero-based sequence indices. -/
def tridiagonal (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then a i else if i.val+1 = j.val then b i
    else if j.val+1 = i.val then 1 else 0

/-- The original determinant A, including the empty determinant. -/
def A (a b : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (tridiagonal (fun i => a (m+i)) (fun i => b (m+i)) n).det

/-- The original determinant B. Its first two diagonals are exceptional. -/
def B (a b : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (tridiagonal (fun i => if i = 0 then b m else a (m+i+1))
    (fun i => if i = 0 then a m*b (m+1) else b (m+i+1)) (n+1)).det

/-- A finite word expressed by its successive runs of ones separated by twos.
`terminal n` is the all-one word of length n; `prepend n w` is `1^n 2 w`.
This inductive datatype represents every finite word uniquely. -/
inductive Word where
  | terminal : ℕ → Word
  | prepend : ℕ → Word → Word
  deriving DecidableEq

def Word.weight : Word → ℕ
  | .terminal n => n
  | .prepend n w => n+2+w.weight

/-- `false` represents the letter one and `true` represents the letter two. -/
def Word.toList : Word → List Bool
  | .terminal n => List.replicate n false
  | .prepend n w => List.replicate n false ++ true :: w.toList

def Word.addOne : Word → Word
  | .terminal n => .terminal (n+1)
  | .prepend n w => .prepend (n+1) w

def Word.fromList : List Bool → Word
  | [] => .terminal 0
  | false :: w => (fromList w).addOne
  | true :: w => .prepend 0 (fromList w)

/-- The literal clone Schur recursion on the source determinants. -/
def cloneSchur (a b : ℕ → ℝ) : Word → ℝ
  | .terminal n => A a b 0 n
  | .prepend n w => B a b w.weight n * cloneSchur a b w

end
end AlternativeQCharlier
