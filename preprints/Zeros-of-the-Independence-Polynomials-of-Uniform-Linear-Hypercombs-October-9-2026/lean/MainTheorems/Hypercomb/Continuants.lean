import Mathlib.Tactic

namespace ResearchMain.Hypercomb

variable {K : Type*} [CommRing K]

def continuant (A B : K) : ℕ → K
  | 0 => 1
  | 1 => A
  | n + 2 => A * continuant A B (n + 1) + B * continuant A B n

def boundaryContinuant (A B z : K) : ℕ → K
  | 0 => 1
  | 1 => A + z
  | n + 2 => A * boundaryContinuant A B z (n + 1) + B * boundaryContinuant A B z n

theorem boundaryContinuant_eq (A B z : K) (n : ℕ) :
    boundaryContinuant A B z (n + 1) = continuant A B (n + 1) + z * continuant A B n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuant, boundaryContinuant]
  | one => simp [continuant, boundaryContinuant]; ring
  | more n h₀ h₁ =>
    rw [boundaryContinuant, h₁, h₀, continuant]
    rw [show continuant A B (n + 2 + 1) =
      A * continuant A B (n + 1 + 1) + B * continuant A B (n + 1) by
        change continuant A B ((n + 1) + 2) = _
        rfl]
    rw [continuant]
    ring

def transfer (A f z : K) : ℕ → K × K
  | 0 => (f, z)
  | n + 1 => (A * (transfer A f z n).1 + f * (transfer A f z n).2,
      z * (transfer A f z n).1)

theorem transfer_left_recurrence (A f z : K) (n : ℕ) :
    (transfer A f z (n + 2)).1 = A * (transfer A f z (n + 1)).1 +
      (f * z) * (transfer A f z n).1 := by
  simp only [transfer]
  ring

theorem transfer_left_eq (A f z : K) (n : ℕ) :
    (transfer A f z n).1 = f * boundaryContinuant A (f * z) z n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [transfer, boundaryContinuant]
  | one => simp [transfer, boundaryContinuant]; ring
  | more n h₀ h₁ =>
    rw [transfer_left_recurrence, h₀, h₁, boundaryContinuant]
    ring

def combValue (a z : K) (n : ℕ) : K :=
  let f := 1 + a * z
  let g := 1 + (a - 1) * z
  (transfer (f * g) f z n).1 + (transfer (f * g) f z n).2

theorem combValue_succ (a z : K) (n : ℕ) :
    combValue a z (n + 1) =
      (1 + a * z) * (boundaryContinuant ((1 + a * z) * (1 + (a - 1) * z))
        ((1 + a * z) * z) z (n + 1) + z *
        boundaryContinuant ((1 + a * z) * (1 + (a - 1) * z)) ((1 + a * z) * z) z n) := by
  dsimp only [combValue]
  rw [transfer_left_eq]
  change _ + z * (transfer _ _ _ n).1 = _
  rw [transfer_left_eq]
  ring

theorem combValue_zero (a : K) (n : ℕ) : combValue a 0 n = 1 := by
  have hstate : ∀ n, transfer (1 : K) 1 0 n = (1, 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [transfer, ih]
  simp [combValue, hstate]

theorem transfer_map {L : Type*} [CommRing L] (φ : K →+* L) (A f z : K) (n : ℕ) :
    (φ (transfer A f z n).1, φ (transfer A f z n).2) = transfer (φ A) (φ f) (φ z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h₁ := congrArg Prod.fst ih
    have h₂ := congrArg Prod.snd ih
    dsimp only at h₁ h₂
    simp only [transfer, map_add, map_mul]
    rw [h₁, h₂]

theorem combValue_map {L : Type*} [CommRing L] (φ : K →+* L) (a z : K) (n : ℕ) :
    φ (combValue a z n) = combValue (φ a) (φ z) n := by
  have h := transfer_map φ ((1 + a * z) * (1 + (a - 1) * z)) (1 + a * z) z n
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  dsimp only [combValue]
  rw [map_add, h₁, h₂]
  simp only [map_one, map_add, map_mul, map_sub]

end ResearchMain.Hypercomb
