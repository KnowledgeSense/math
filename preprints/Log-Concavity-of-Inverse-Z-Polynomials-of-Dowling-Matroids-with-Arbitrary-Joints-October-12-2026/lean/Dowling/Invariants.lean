import Dowling.ZeroPartition
import ThagomizerTuran.IntervalTransport
import BoseBurton.ZIncidenceTransport
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section
namespace Dowling
open MatroidInverseZ Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

def configurationP (X : Set (Fin n)) : Polynomial ℤ :=
  kl (configurationRank X) (⊤ : Configuration G X) ⊥

def configurationZ (X : Set (Fin n)) : Polynomial ℤ :=
  zKernel (configurationRank X) (⊥ : Configuration G X) ⊤

def configurationY (X : Set (Fin n)) : Polynomial ℤ :=
  inverseZ (configurationRank X) (⊥ : Configuration G X) ⊤

/-- The computed interval invariant is exactly that of the genuine retained-joint matroid. -/
theorem actual_inverseZ_eq_configurationY (X : Set (Fin n)) :
    matroidInverseZ (matroid G n X) = configurationY (G := G) X := by
  let e := configurationOrderIso (G := G) X
  have h := inverseZ_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    (configurationRank X) (flatRank (matroid G n X))
    (fun a b => by
      change flatRank (matroid G n X) (configurationOrderIso X b) -
        flatRank (matroid G n X) (configurationOrderIso X a) = _
      rw [configurationOrderIso_rank, configurationOrderIso_rank])
    (⊥ : Configuration G X) ⊤
  change inverseZ (flatRank (matroid G n X)) (e ⊥) (e ⊤) = _ at h
  rw [configurationOrderIso_bot, configurationOrderIso_top] at h
  exact h

/-- Full Dowling invariants, including the genuine empty rank-zero object. -/
def fullP (G : Type*) [Group G] [Fintype G] (n : ℕ) : Polynomial ℤ :=
  configurationP (G := G) (Set.univ : Set (Fin n))
def fullZ (G : Type*) [Group G] [Fintype G] (n : ℕ) : Polynomial ℤ :=
  configurationZ (G := G) (Set.univ : Set (Fin n))
def fullY (G : Type*) [Group G] [Fintype G] (n : ℕ) : Polynomial ℤ :=
  configurationY (G := G) (Set.univ : Set (Fin n))

/-- Ordinary real exponential generating series of actual integer polynomials. -/
def invariantEGF (a : ℕ → Polynomial ℤ) : PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk (fun n => C ((n.factorial : ℝ)⁻¹) * (a n).map (Int.castRingHom ℝ))

def fullPSeries (G : Type*) [Group G] [Fintype G] : PowerSeries (Polynomial ℝ) := invariantEGF (fullP G)
def fullZSeries (G : Type*) [Group G] [Fintype G] : PowerSeries (Polynomial ℝ) := invariantEGF (fullZ G)
def fullYSeries (G : Type*) [Group G] [Fintype G] : PowerSeries (Polynomial ℝ) := invariantEGF (fullY G)

@[simp] theorem invariantEGF_coeff (a : ℕ → Polynomial ℤ) (n : ℕ) :
    PowerSeries.coeff n (invariantEGF a) = C ((n.factorial : ℝ)⁻¹) * (a n).map (Int.castRingHom ℝ) :=
  PowerSeries.coeff_mk _ _

end Dowling
