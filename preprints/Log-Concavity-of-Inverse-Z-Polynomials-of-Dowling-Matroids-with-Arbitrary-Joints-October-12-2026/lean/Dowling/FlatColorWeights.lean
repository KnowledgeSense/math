import Dowling.OrderedPartitionCounting
import Dowling.LabeledColorEnumeration

noncomputable section
namespace Dowling
open scoped Classical BigOperators
open Polynomial
variable {G : Type*} [Group G] [Fintype G]

def zeroBlockWeight (G : Type*) [Group G] [Fintype G] (j : ℕ) : Polynomial ℝ :=
  (fullZ G j).map (Int.castRingHom ℝ)

def balancedBlockWeight (G : Type*) [Group G] [Fintype G] (j : ℕ) : Polynomial ℝ :=
  if j=0 then 0 else C ((Fintype.card G : ℝ)^(j-1))*zeroBlockWeight Unit (j-1)

def flatColorWeight (G : Type*) [Group G] [Fintype G] {k : ℕ} : Option (Fin k) → ℕ → Polynomial ℝ
  | none => zeroBlockWeight G
  | some _ => balancedBlockWeight G

@[simp] theorem balancedBlockWeight_zero : balancedBlockWeight G 0=0 := by
  simp [balancedBlockWeight]

theorem occupied_weight {n k : ℕ} (w : OccupiedWord n k) :
    (∏ c : Option (Fin k), flatColorWeight G c (w.fiber c).card) =
      (∏ c : Fin k, (Fintype.card G : Polynomial ℝ)^((w.fiber (some c)).card-1))*
        (zeroBlockWeight G (w.fiber none).card *
          ∏ c : Fin k, zeroBlockWeight Unit ((w.fiber (some c)).card-1)) := by
  rw [Fintype.prod_option]
  simp only [flatColorWeight]
  have hpos (c : Fin k) : (w.fiber (some c)).card≠0 :=
    Nat.ne_of_gt (Finset.card_pos.mpr (w.fiber_nonempty c))
  simp only [balancedBlockWeight,hpos,ite_false]
  rw [Finset.prod_mul_distrib]
  simp only [map_pow,map_natCast]
  ring

theorem unoccupied_weight_zero {n k : ℕ} (w : Fin n → Option (Fin k))
    (hw : ¬ ∀ c, ∃ i, w i=some c) :
    (∏ c : Option (Fin k), flatColorWeight G c (Finset.univ.filter (fun i => w i=c)).card)=0 := by
  push Not at hw
  obtain ⟨c,hc⟩ := hw
  apply Finset.prod_eq_zero (Finset.mem_univ (some c))
  have he : Finset.univ.filter (fun i => w i=some c)=∅ := by
    ext i
    simp [hc i]
  rw [he,Finset.card_empty]
  exact balancedBlockWeight_zero

theorem sum_occupied_weight (n k : ℕ) :
    (∑ w : OccupiedWord n k, ∏ c : Option (Fin k), flatColorWeight G c (w.fiber c).card) =
      ∑ w : Fin n → Option (Fin k), ∏ c : Option (Fin k),
        flatColorWeight G c (Finset.univ.filter (fun i => w i=c)).card := by
  change (∑ w : {w : Fin n → Option (Fin k) // ∀ c, ∃ i, w i=some c},
    ∏ c : Option (Fin k), flatColorWeight G c (Finset.univ.filter (fun i => w.val i=c)).card)=_
  rw [← Finset.sum_subtype (Finset.univ.filter (fun w : Fin n → Option (Fin k) => ∀ c, ∃ i, w i=some c))
    (by simp) (fun w => ∏ c : Option (Fin k),
      flatColorWeight G c (Finset.univ.filter (fun i => w i=c)).card)]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro w _ hw
  apply unoccupied_weight_zero
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hw

theorem partitionZ_color_enumeration (n k : ℕ) :
    (k.factorial : Polynomial ℝ)*
      (∑ p : GainPartition G n with p.roots.card=k, (partitionZ p).map (Int.castRingHom ℝ)) =
      ∑ w : Fin n → Option (Fin k), ∏ c : Option (Fin k),
        flatColorWeight G c (Finset.univ.filter (fun i => w i=c)).card := by
  rw [← sum_occupied_weight]
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (partitionZ_ordered_enumeration (G := G) n k)
  simp only [Polynomial.map_mul,Polynomial.map_sum,Polynomial.map_prod,
    Polynomial.map_pow,Polynomial.map_natCast] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro w _
  exact (occupied_weight w).symm

end Dowling
