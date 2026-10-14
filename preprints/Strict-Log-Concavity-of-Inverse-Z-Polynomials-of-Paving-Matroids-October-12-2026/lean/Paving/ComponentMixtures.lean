import Paving.Components
import Paving.SymmetricRows

noncomputable section
open Finset
namespace Paving

def lowerComponent (k n : ℕ) (h : Option ℕ) (i : ℕ) : ℝ :=
  match h with
  | none => uniformComponent k n i
  | some h => hyperplaneComponent k n h i

def ValidParameter (k n : ℕ) : Option ℕ→Prop
  | none => True
  | some h => k ≤ h ∧ h < n

theorem lowerComponent_positive {k n i : ℕ} (h : Option ℕ)
    (hik : i+1 < k) (hkn : k ≤ n) (hv : ValidParameter k n h) :
    0 < lowerComponent k n h i := by
  cases h with
  | none => exact uniformComponent_positive (by omega) hkn
  | some h => exact hyperplaneComponent_positive hik hv.1 hv.2

theorem lowerComponent_bounds {k n i : ℕ} (h : Option ℕ)
    (hi : 1 ≤ i) (hik : i+1 < k) (hkn : k ≤ n) (hv : ValidParameter k n h) :
    lowerRatio k n i*lowerComponent k n h (i-1) ≤ lowerComponent k n h i ∧
      lowerComponent k n h i ≤ upperRatio k n i*lowerComponent k n h (i-1) := by
  have hiR : (0:ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hikR : (i:ℝ)+1 < k := by exact_mod_cast hik
  have hknR : (k:ℝ) ≤ n := by exact_mod_cast hkn
  have he : ((i-1:ℕ):ℝ)+1=(i:ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hp := lowerComponent_positive h (show i-1+1 < k by omega) hkn hv
  cases h with
  | none =>
    change lowerRatio k n i*uniformComponent k n (i-1) ≤ uniformComponent k n i ∧
      uniformComponent k n i ≤ upperRatio k n i*uniformComponent k n (i-1)
    have hs := uniformComponent_step (show i-1+2 ≤ k by omega) hkn
    rw [Nat.sub_add_cancel hi,he] at hs
    rw [hs]
    exact ⟨mul_le_mul_of_nonneg_right (ratio_bounds_order hknR hiR (by linarith)) hp.le,le_rfl⟩
  | some h =>
    change lowerRatio k n i*hyperplaneComponent k n h (i-1) ≤ hyperplaneComponent k n h i ∧
      hyperplaneComponent k n h i ≤ upperRatio k n i*hyperplaneComponent k n h (i-1)
    have hs := hyperplaneComponent_step (show i-1+2 < k by omega) hv.1 hv.2
    rw [Nat.sub_add_cancel hi,he] at hs
    rw [hs]
    have hkhR : (k:ℝ) ≤ h := by exact_mod_cast hv.1
    have hhnR : (h:ℝ) ≤ (n:ℝ)-1 := by
      have h : (h:ℝ)+1 ≤ n := by exact_mod_cast hv.2
      linarith
    have hb := hyperplaneRatio_bounds hiR hikR hkhR hhnR
    exact ⟨mul_le_mul_of_nonneg_right hb.1 hp.le,
      mul_le_mul_of_nonneg_right hb.2.le hp.le⟩

def reflectedMixture {ι : Type*} (s : Finset ι) (w : ι→ℝ)
    (h : ι→Option ℕ) (k n i : ℕ) : ℝ :=
  ∑j∈s,w j*lowerComponent k n (h j) (min i (k-i))

theorem reflectedMixture_symm {ι : Type*} (s : Finset ι) (w : ι→ℝ)
    (h : ι→Option ℕ) (k n i : ℕ) (hi : i ≤ k) :
    reflectedMixture s w h k n (k-i)=reflectedMixture s w h k n i := by
  unfold reflectedMixture
  rw [Nat.sub_sub_self hi,min_comm]

theorem odd_mixture_strict {ι : Type*} (s : Finset ι) (w : ι→ℝ)
    (h : ι→Option ℕ) (m n : ℕ) (hm : 1 ≤ m) (hn : 2*m+1 ≤ n)
    (hw : ∀j∈s,0 ≤ w j) (hs : ∑j∈s,w j=1)
    (hv : ∀j∈s,ValidParameter (2*m+1) n (h j)) :
    ∀i, 1 ≤ i → i < 2*m+1 →
      reflectedMixture s w h (2*m+1) n (i-1)*reflectedMixture s w h (2*m+1) n (i+1) <
        reflectedMixture s w h (2*m+1) n i^2 := by
  apply odd_row_strict _ m n hm hn
  · intro i hi
    apply mixture_positive s w _ hw hs
    intro j hj
    apply lowerComponent_positive (h j) _ hn (hv j hj)
    have : min i (2*m+1-i) ≤ m := by omega
    omega
  · exact fun i hi => reflectedMixture_symm s w h _ _ _ hi
  · intro i hi him
    have hh : min i (2*m+1-i)=i := min_eq_left (by omega)
    have hp : min (i-1) (2*m+1-(i-1))=i-1 := min_eq_left (by omega)
    unfold reflectedMixture
    rw [hh,hp]
    apply mixture_linear_bounds s w _ _ _ _ hw
    · intro j hj
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
        (lowerComponent_bounds (h j) hi (by omega) hn (hv j hj)).1
    · intro j hj
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
        (lowerComponent_bounds (h j) hi (by omega) hn (hv j hj)).2

end Paving
