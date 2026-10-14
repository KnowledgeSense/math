import MainTheorems.Corona.Basic

namespace ResearchMain.Corona

def UnimodalAt (f : ℕ → ℝ) (m : ℕ) : Prop :=
  (∀ k < m, f k ≤ f (k + 1)) ∧ (∀ k ≥ m, f (k + 1) ≤ f k)

def Unimodal (f : ℕ → ℝ) : Prop := ∃ m, UnimodalAt f m

def LogConcave (f : ℕ → ℝ) : Prop := ∀ k, 1 ≤ k → f (k - 1) * f (k + 1) ≤ f k ^ 2

theorem UnimodalAt.before {f : ℕ → ℝ} {m : ℕ} (hf : UnimodalAt f m)
    {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) : f i ≤ f j := by
  revert hjm
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hjm
    exact (ih (by omega)).trans (hf.1 j (by omega))

theorem UnimodalAt.after {f : ℕ → ℝ} {m : ℕ} (hf : UnimodalAt f m)
    {i j : ℕ} (hmi : m ≤ i) (hij : i ≤ j) : f j ≤ f i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (hf.2 j (by omega)).trans ih

theorem valley_not_unimodal {f : ℕ → ℝ} {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hi : f j < f i) (hk : f j < f k) : ¬Unimodal f := by
  rintro ⟨m, hm⟩
  by_cases hjm : j ≤ m
  · exact (not_lt_of_ge (hm.before hij.le hjm)) hi
  · exact (not_lt_of_ge (hm.after (by omega : m ≤ j) hjk.le)) hk

theorem UnimodalAt.add {f g : ℕ → ℝ} {m : ℕ} (hf : UnimodalAt f m) (hg : UnimodalAt g m) :
    UnimodalAt (fun k => f k + g k) m := by
  exact ⟨fun k hk => add_le_add (hf.1 k hk) (hg.1 k hk),
    fun k hk => add_le_add (hf.2 k hk) (hg.2 k hk)⟩

theorem UnimodalAt.mul_nonnegative {f : ℕ → ℝ} {m : ℕ} (hf : UnimodalAt f m)
    {c : ℝ} (hc : 0 ≤ c) : UnimodalAt (fun k => c * f k) m := by
  exact ⟨fun k hk => mul_le_mul_of_nonneg_left (hf.1 k hk) hc,
    fun k hk => mul_le_mul_of_nonneg_left (hf.2 k hk) hc⟩

theorem unimodal_mul_pos_iff {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c) :
    Unimodal (fun k => c * f k) ↔ Unimodal f := by
  constructor
  · rintro ⟨m, hup, hdown⟩
    exact ⟨m, (fun k hk => (mul_le_mul_iff_of_pos_left hc).mp (hup k hk)),
      fun k hk => (mul_le_mul_iff_of_pos_left hc).mp (hdown k hk)⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, hm.mul_nonnegative hc.le⟩

theorem LogConcave.geometric_scale {f : ℕ → ℝ} (hf : LogConcave f) {t : ℝ} (ht : 0 ≤ t) :
    LogConcave (fun k => t ^ k * f k) := by
  intro k hk
  have he : (t ^ (k - 1) * f (k - 1)) * (t ^ (k + 1) * f (k + 1)) =
      t ^ (2 * k) * (f (k - 1) * f (k + 1)) := by
    calc
      _ = (t ^ (k - 1) * t ^ (k + 1)) * (f (k - 1) * f (k + 1)) := by ring
      _ = _ := by rw [← pow_add, show k - 1 + (k + 1) = 2 * k by omega]
  rw [he]
  have h := mul_le_mul_of_nonneg_left (hf k hk) (pow_nonneg ht (2 * k))
  convert h using 1
  rw [mul_pow, pow_mul]
  ring

end ResearchMain.Corona
