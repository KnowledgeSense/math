import MainTheorems.Tuza.Certificates.Basic
import MainTheorems.Tuza.FiniteCertificates

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ResearchMain.Tuza.Certificates

def canonical_small_4_5_4_1_1_1_profile : FerrersProfile 4 5 where
  degree := ![4, 1, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_5_4_1_1_1_triples : List (Fin (4 + 5) × Fin (4 + 5) × Fin (4 + 5)) :=
  [
    (0, 2, 3),
    (0, 4, 5),
    (0, 6, 7),
    (1, 3, 4),
    (4, 7, 8),
    (5, 6, 8)]

def canonical_small_4_5_4_1_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 5)) :=
  labeledPacking 4 5 canonical_small_4_5_4_1_1_1_triples

theorem canonical_small_4_5_4_1_1_1_verified : Packing canonical_small_4_5_4_1_1_1_profile.graph canonical_small_4_5_4_1_1_1_triangles ∧
    canonical_small_4_5_4_1_1_1_triangles.card = 6 := by
  have h := labeledPacking_correct canonical_small_4_5_4_1_1_1_profile canonical_small_4_5_4_1_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_5_4_1_1_1_inequality : Inequality canonical_small_4_5_4_1_1_1_profile.graph := by
  have hc := canonical_small_4_5_4_1_1_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_5_4_1_1_1_verified.1
  rw [canonical_small_4_5_4_1_1_1_verified.2] at hp
  have ht : canonical_small_4_5_4_1_1_1_profile.orderedCutCount 1 2 false ≤ 2 * 6 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_5_4_2_1_1_profile : FerrersProfile 4 5 where
  degree := ![4, 2, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_5_4_2_1_1_triples : List (Fin (4 + 5) × Fin (4 + 5) × Fin (4 + 5)) :=
  [
    (0, 1, 3),
    (0, 4, 7),
    (0, 5, 6),
    (1, 4, 5),
    (2, 3, 4),
    (4, 6, 8),
    (5, 7, 8)]

def canonical_small_4_5_4_2_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 5)) :=
  labeledPacking 4 5 canonical_small_4_5_4_2_1_1_triples

theorem canonical_small_4_5_4_2_1_1_verified : Packing canonical_small_4_5_4_2_1_1_profile.graph canonical_small_4_5_4_2_1_1_triangles ∧
    canonical_small_4_5_4_2_1_1_triangles.card = 7 := by
  have h := labeledPacking_correct canonical_small_4_5_4_2_1_1_profile canonical_small_4_5_4_2_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_5_4_2_1_1_inequality : Inequality canonical_small_4_5_4_2_1_1_profile.graph := by
  have hc := canonical_small_4_5_4_2_1_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_5_4_2_1_1_verified.1
  rw [canonical_small_4_5_4_2_1_1_verified.2] at hp
  have ht : canonical_small_4_5_4_2_1_1_profile.orderedCutCount 1 2 false ≤ 2 * 7 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_5_4_3_1_1_profile : FerrersProfile 4 5 where
  degree := ![4, 3, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_5_4_3_1_1_triples : List (Fin (4 + 5) × Fin (4 + 5) × Fin (4 + 5)) :=
  [
    (0, 1, 6),
    (0, 2, 4),
    (0, 5, 7),
    (1, 2, 3),
    (1, 4, 5),
    (4, 6, 7),
    (5, 6, 8)]

def canonical_small_4_5_4_3_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 5)) :=
  labeledPacking 4 5 canonical_small_4_5_4_3_1_1_triples

theorem canonical_small_4_5_4_3_1_1_verified : Packing canonical_small_4_5_4_3_1_1_profile.graph canonical_small_4_5_4_3_1_1_triangles ∧
    canonical_small_4_5_4_3_1_1_triangles.card = 7 := by
  have h := labeledPacking_correct canonical_small_4_5_4_3_1_1_profile canonical_small_4_5_4_3_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_5_4_3_1_1_inequality : Inequality canonical_small_4_5_4_3_1_1_profile.graph := by
  have hc := canonical_small_4_5_4_3_1_1_profile.ordered_cut_bound 2 3 true (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_5_4_3_1_1_verified.1
  rw [canonical_small_4_5_4_3_1_1_verified.2] at hp
  have ht : canonical_small_4_5_4_3_1_1_profile.orderedCutCount 2 3 true ≤ 2 * 7 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_5_4_2_2_1_profile : FerrersProfile 4 5 where
  degree := ![4, 2, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_5_4_2_2_1_triples : List (Fin (4 + 5) × Fin (4 + 5) × Fin (4 + 5)) :=
  [
    (0, 1, 3),
    (0, 4, 7),
    (0, 5, 6),
    (1, 2, 5),
    (2, 3, 4),
    (4, 6, 8),
    (5, 7, 8)]

def canonical_small_4_5_4_2_2_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 5)) :=
  labeledPacking 4 5 canonical_small_4_5_4_2_2_1_triples

theorem canonical_small_4_5_4_2_2_1_verified : Packing canonical_small_4_5_4_2_2_1_profile.graph canonical_small_4_5_4_2_2_1_triangles ∧
    canonical_small_4_5_4_2_2_1_triangles.card = 7 := by
  have h := labeledPacking_correct canonical_small_4_5_4_2_2_1_profile canonical_small_4_5_4_2_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_5_4_2_2_1_inequality : Inequality canonical_small_4_5_4_2_2_1_profile.graph := by
  have hc := canonical_small_4_5_4_2_2_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_5_4_2_2_1_verified.1
  rw [canonical_small_4_5_4_2_2_1_verified.2] at hp
  have ht : canonical_small_4_5_4_2_2_1_profile.orderedCutCount 1 2 false ≤ 2 * 7 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_5_4_3_2_1_profile : FerrersProfile 4 5 where
  degree := ![4, 3, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_5_4_3_2_1_triples : List (Fin (4 + 5) × Fin (4 + 5) × Fin (4 + 5)) :=
  [
    (0, 1, 3),
    (0, 4, 7),
    (0, 5, 6),
    (1, 2, 5),
    (1, 4, 6),
    (2, 3, 4),
    (4, 5, 8),
    (6, 7, 8)]

def canonical_small_4_5_4_3_2_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 5)) :=
  labeledPacking 4 5 canonical_small_4_5_4_3_2_1_triples

theorem canonical_small_4_5_4_3_2_1_verified : Packing canonical_small_4_5_4_3_2_1_profile.graph canonical_small_4_5_4_3_2_1_triangles ∧
    canonical_small_4_5_4_3_2_1_triangles.card = 8 := by
  have h := labeledPacking_correct canonical_small_4_5_4_3_2_1_profile canonical_small_4_5_4_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_5_4_3_2_1_inequality : Inequality canonical_small_4_5_4_3_2_1_profile.graph := by
  have hc := canonical_small_4_5_4_3_2_1_profile.ordered_cut_bound 3 3 true (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_5_4_3_2_1_verified.1
  rw [canonical_small_4_5_4_3_2_1_verified.2] at hp
  have ht : canonical_small_4_5_4_3_2_1_profile.orderedCutCount 3 3 true ≤ 2 * 8 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_5_5_4_3_1_profile : FerrersProfile 4 5 where
  degree := ![5, 4, 3, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_5_5_4_3_1_triples : List (Fin (4 + 5) × Fin (4 + 5) × Fin (4 + 5)) :=
  [
    (0, 1, 7),
    (0, 2, 6),
    (0, 3, 4),
    (0, 5, 8),
    (1, 2, 3),
    (1, 4, 6),
    (2, 4, 5),
    (4, 7, 8),
    (5, 6, 7)]

def canonical_small_4_5_5_4_3_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 5)) :=
  labeledPacking 4 5 canonical_small_4_5_5_4_3_1_triples

theorem canonical_small_4_5_5_4_3_1_verified : Packing canonical_small_4_5_5_4_3_1_profile.graph canonical_small_4_5_5_4_3_1_triangles ∧
    canonical_small_4_5_5_4_3_1_triangles.card = 9 := by
  have h := labeledPacking_correct canonical_small_4_5_5_4_3_1_profile canonical_small_4_5_5_4_3_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_5_5_4_3_1_inequality : Inequality canonical_small_4_5_5_4_3_1_profile.graph := by
  have hc := canonical_small_4_5_5_4_3_1_profile.ordered_cut_bound 1 3 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_5_5_4_3_1_verified.1
  rw [canonical_small_4_5_5_4_3_1_verified.2] at hp
  have ht : canonical_small_4_5_5_4_3_1_profile.orderedCutCount 1 3 false ≤ 2 * 9 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_5_5_5_4_3_2_0_profile : FerrersProfile 5 5 where
  degree := ![5, 4, 3, 2, 0]
  bound := by decide
  antitone := by decide

def canonical_small_5_5_5_4_3_2_0_triples : List (Fin (5 + 5) × Fin (5 + 5) × Fin (5 + 5)) :=
  [
    (0, 1, 7),
    (0, 3, 4),
    (0, 5, 6),
    (0, 8, 9),
    (1, 2, 4),
    (1, 3, 5),
    (1, 6, 8),
    (2, 3, 6),
    (5, 7, 8),
    (6, 7, 9)]

def canonical_small_5_5_5_4_3_2_0_triangles : Finset (Finset (Fin 5 ⊕ Fin 5)) :=
  labeledPacking 5 5 canonical_small_5_5_5_4_3_2_0_triples

theorem canonical_small_5_5_5_4_3_2_0_verified : Packing canonical_small_5_5_5_4_3_2_0_profile.graph canonical_small_5_5_5_4_3_2_0_triangles ∧
    canonical_small_5_5_5_4_3_2_0_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_small_5_5_5_4_3_2_0_profile canonical_small_5_5_5_4_3_2_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_5_5_5_4_3_2_0_inequality : Inequality canonical_small_5_5_5_4_3_2_0_profile.graph := by
  have hc := canonical_small_5_5_5_4_3_2_0_profile.ordered_cut_bound 2 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_5_5_5_4_3_2_0_verified.1
  rw [canonical_small_5_5_5_4_3_2_0_verified.2] at hp
  have ht : canonical_small_5_5_5_4_3_2_0_profile.orderedCutCount 2 2 false ≤ 2 * 10 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_5_5_5_4_3_1_1_profile : FerrersProfile 5 5 where
  degree := ![5, 4, 3, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_5_5_5_4_3_1_1_triples : List (Fin (5 + 5) × Fin (5 + 5) × Fin (5 + 5)) :=
  [
    (0, 1, 4),
    (0, 2, 7),
    (0, 5, 8),
    (0, 6, 9),
    (1, 2, 3),
    (1, 5, 7),
    (1, 6, 8),
    (2, 5, 6),
    (3, 4, 5),
    (7, 8, 9)]

def canonical_small_5_5_5_4_3_1_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 5)) :=
  labeledPacking 5 5 canonical_small_5_5_5_4_3_1_1_triples

theorem canonical_small_5_5_5_4_3_1_1_verified : Packing canonical_small_5_5_5_4_3_1_1_profile.graph canonical_small_5_5_5_4_3_1_1_triangles ∧
    canonical_small_5_5_5_4_3_1_1_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_small_5_5_5_4_3_1_1_profile canonical_small_5_5_5_4_3_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_5_5_5_4_3_1_1_inequality : Inequality canonical_small_5_5_5_4_3_1_1_profile.graph := by
  have hc := canonical_small_5_5_5_4_3_1_1_profile.ordered_cut_bound 2 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_5_5_5_4_3_1_1_verified.1
  rw [canonical_small_5_5_5_4_3_1_1_verified.2] at hp
  have ht : canonical_small_5_5_5_4_3_1_1_profile.orderedCutCount 2 2 false ≤ 2 * 10 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_5_5_5_3_3_2_1_profile : FerrersProfile 5 5 where
  degree := ![5, 3, 3, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_5_5_5_3_3_2_1_triples : List (Fin (5 + 5) × Fin (5 + 5) × Fin (5 + 5)) :=
  [
    (0, 1, 4),
    (0, 2, 3),
    (0, 5, 9),
    (0, 6, 8),
    (1, 2, 7),
    (1, 3, 6),
    (2, 5, 6),
    (3, 4, 5),
    (5, 7, 8),
    (6, 7, 9)]

def canonical_small_5_5_5_3_3_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 5)) :=
  labeledPacking 5 5 canonical_small_5_5_5_3_3_2_1_triples

theorem canonical_small_5_5_5_3_3_2_1_verified : Packing canonical_small_5_5_5_3_3_2_1_profile.graph canonical_small_5_5_5_3_3_2_1_triangles ∧
    canonical_small_5_5_5_3_3_2_1_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_small_5_5_5_3_3_2_1_profile canonical_small_5_5_5_3_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_5_5_5_3_3_2_1_inequality : Inequality canonical_small_5_5_5_3_3_2_1_profile.graph := by
  have hc := canonical_small_5_5_5_3_3_2_1_profile.ordered_cut_bound 1 3 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_5_5_5_3_3_2_1_verified.1
  rw [canonical_small_5_5_5_3_3_2_1_verified.2] at hp
  have ht : canonical_small_5_5_5_3_3_2_1_profile.orderedCutCount 1 3 false ≤ 2 * 10 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_5_5_4_4_3_2_1_profile : FerrersProfile 5 5 where
  degree := ![4, 4, 3, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_5_5_4_4_3_2_1_triples : List (Fin (5 + 5) × Fin (5 + 5) × Fin (5 + 5)) :=
  [
    (0, 1, 2),
    (0, 3, 4),
    (0, 5, 8),
    (0, 6, 7),
    (1, 4, 5),
    (1, 6, 8),
    (2, 3, 6),
    (2, 5, 7),
    (5, 6, 9),
    (7, 8, 9)]

def canonical_small_5_5_4_4_3_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 5)) :=
  labeledPacking 5 5 canonical_small_5_5_4_4_3_2_1_triples

theorem canonical_small_5_5_4_4_3_2_1_verified : Packing canonical_small_5_5_4_4_3_2_1_profile.graph canonical_small_5_5_4_4_3_2_1_triangles ∧
    canonical_small_5_5_4_4_3_2_1_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_small_5_5_4_4_3_2_1_profile canonical_small_5_5_4_4_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_5_5_4_4_3_2_1_inequality : Inequality canonical_small_5_5_4_4_3_2_1_profile.graph := by
  have hc := canonical_small_5_5_4_4_3_2_1_profile.ordered_cut_bound 2 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_5_5_4_4_3_2_1_verified.1
  rw [canonical_small_5_5_4_4_3_2_1_verified.2] at hp
  have ht : canonical_small_5_5_4_4_3_2_1_profile.orderedCutCount 2 2 false ≤ 2 * 10 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_5_5_5_4_3_2_1_profile : FerrersProfile 5 5 where
  degree := ![5, 4, 3, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_5_5_5_4_3_2_1_triples : List (Fin (5 + 5) × Fin (5 + 5) × Fin (5 + 5)) :=
  [
    (0, 1, 6),
    (0, 2, 3),
    (0, 5, 8),
    (0, 7, 9),
    (1, 2, 5),
    (1, 3, 4),
    (1, 7, 8),
    (2, 6, 7),
    (3, 5, 6),
    (6, 8, 9)]

def canonical_small_5_5_5_4_3_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 5)) :=
  labeledPacking 5 5 canonical_small_5_5_5_4_3_2_1_triples

theorem canonical_small_5_5_5_4_3_2_1_verified : Packing canonical_small_5_5_5_4_3_2_1_profile.graph canonical_small_5_5_5_4_3_2_1_triangles ∧
    canonical_small_5_5_5_4_3_2_1_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_small_5_5_5_4_3_2_1_profile canonical_small_5_5_5_4_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_5_5_5_4_3_2_1_inequality : Inequality canonical_small_5_5_5_4_3_2_1_profile.graph := by
  have hc := canonical_small_5_5_5_4_3_2_1_profile.ordered_cut_bound 2 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_5_5_5_4_3_2_1_verified.1
  rw [canonical_small_5_5_5_4_3_2_1_verified.2] at hp
  have ht : canonical_small_5_5_5_4_3_2_1_profile.orderedCutCount 2 2 false ≤ 2 * 10 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_2_4_4_3_profile : FerrersProfile 2 4 where
  degree := ![4, 3]
  bound := by decide
  antitone := by decide

def canonical_small_2_4_4_3_triples : List (Fin (2 + 4) × Fin (2 + 4) × Fin (2 + 4)) :=
  [
    (0, 2, 5),
    (0, 3, 4),
    (1, 2, 4)]

def canonical_small_2_4_4_3_triangles : Finset (Finset (Fin 2 ⊕ Fin 4)) :=
  labeledPacking 2 4 canonical_small_2_4_4_3_triples

theorem canonical_small_2_4_4_3_verified : Packing canonical_small_2_4_4_3_profile.graph canonical_small_2_4_4_3_triangles ∧
    canonical_small_2_4_4_3_triangles.card = 3 := by
  have h := labeledPacking_correct canonical_small_2_4_4_3_profile canonical_small_2_4_4_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_2_4_4_3_inequality : Inequality canonical_small_2_4_4_3_profile.graph := by
  have hc := canonical_small_2_4_4_3_profile.ordered_cut_bound 0 3 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_2_4_4_3_verified.1
  rw [canonical_small_2_4_4_3_verified.2] at hp
  have ht : canonical_small_2_4_4_3_profile.orderedCutCount 0 3 false ≤ 2 * 3 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_1_1_0_profile : FerrersProfile 4 4 where
  degree := ![4, 1, 1, 0]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_1_1_0_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 2, 3),
    (0, 4, 5),
    (1, 2, 4),
    (4, 6, 7)]

def canonical_small_4_4_4_1_1_0_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_1_1_0_triples

theorem canonical_small_4_4_4_1_1_0_verified : Packing canonical_small_4_4_4_1_1_0_profile.graph canonical_small_4_4_4_1_1_0_triangles ∧
    canonical_small_4_4_4_1_1_0_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_1_1_0_profile canonical_small_4_4_4_1_1_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_1_1_0_inequality : Inequality canonical_small_4_4_4_1_1_0_profile.graph := by
  have hc := canonical_small_4_4_4_1_1_0_profile.ordered_cut_bound 1 1 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_1_1_0_verified.1
  rw [canonical_small_4_4_4_1_1_0_verified.2] at hp
  have ht : canonical_small_4_4_4_1_1_0_profile.orderedCutCount 1 1 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_2_1_0_profile : FerrersProfile 4 4 where
  degree := ![4, 2, 1, 0]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_2_1_0_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 5),
    (0, 4, 6),
    (1, 2, 4),
    (4, 5, 7)]

def canonical_small_4_4_4_2_1_0_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_2_1_0_triples

theorem canonical_small_4_4_4_2_1_0_verified : Packing canonical_small_4_4_4_2_1_0_profile.graph canonical_small_4_4_4_2_1_0_triangles ∧
    canonical_small_4_4_4_2_1_0_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_2_1_0_profile canonical_small_4_4_4_2_1_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_2_1_0_inequality : Inequality canonical_small_4_4_4_2_1_0_profile.graph := by
  have hc := canonical_small_4_4_4_2_1_0_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_2_1_0_verified.1
  rw [canonical_small_4_4_4_2_1_0_verified.2] at hp
  have ht : canonical_small_4_4_4_2_1_0_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_3_1_0_profile : FerrersProfile 4 4 where
  degree := ![4, 3, 1, 0]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_3_1_0_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 3),
    (0, 5, 7),
    (1, 2, 4),
    (4, 5, 6)]

def canonical_small_4_4_4_3_1_0_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_3_1_0_triples

theorem canonical_small_4_4_4_3_1_0_verified : Packing canonical_small_4_4_4_3_1_0_profile.graph canonical_small_4_4_4_3_1_0_triangles ∧
    canonical_small_4_4_4_3_1_0_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_3_1_0_profile canonical_small_4_4_4_3_1_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_3_1_0_inequality : Inequality canonical_small_4_4_4_3_1_0_profile.graph := by
  have hc := canonical_small_4_4_4_3_1_0_profile.ordered_cut_bound 2 1 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_3_1_0_verified.1
  rw [canonical_small_4_4_4_3_1_0_verified.2] at hp
  have ht : canonical_small_4_4_4_3_1_0_profile.orderedCutCount 2 1 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_2_2_0_profile : FerrersProfile 4 4 where
  degree := ![4, 2, 2, 0]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_2_2_0_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 3),
    (0, 2, 4),
    (1, 4, 5),
    (5, 6, 7)]

def canonical_small_4_4_4_2_2_0_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_2_2_0_triples

theorem canonical_small_4_4_4_2_2_0_verified : Packing canonical_small_4_4_4_2_2_0_profile.graph canonical_small_4_4_4_2_2_0_triangles ∧
    canonical_small_4_4_4_2_2_0_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_2_2_0_profile canonical_small_4_4_4_2_2_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_2_2_0_inequality : Inequality canonical_small_4_4_4_2_2_0_profile.graph := by
  have hc := canonical_small_4_4_4_2_2_0_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_2_2_0_verified.1
  rw [canonical_small_4_4_4_2_2_0_verified.2] at hp
  have ht : canonical_small_4_4_4_2_2_0_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_3_2_0_profile : FerrersProfile 4 4 where
  degree := ![4, 3, 2, 0]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_3_2_0_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 2),
    (0, 4, 5),
    (1, 5, 6),
    (4, 6, 7)]

def canonical_small_4_4_4_3_2_0_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_3_2_0_triples

theorem canonical_small_4_4_4_3_2_0_verified : Packing canonical_small_4_4_4_3_2_0_profile.graph canonical_small_4_4_4_3_2_0_triangles ∧
    canonical_small_4_4_4_3_2_0_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_3_2_0_profile canonical_small_4_4_4_3_2_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_3_2_0_inequality : Inequality canonical_small_4_4_4_3_2_0_profile.graph := by
  have hc := canonical_small_4_4_4_3_2_0_profile.ordered_cut_bound 3 3 true (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_3_2_0_verified.1
  rw [canonical_small_4_4_4_3_2_0_verified.2] at hp
  have ht : canonical_small_4_4_4_3_2_0_profile.orderedCutCount 3 3 true ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_3_1_1_1_profile : FerrersProfile 4 4 where
  degree := ![3, 1, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_3_1_1_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 2),
    (0, 4, 5),
    (2, 3, 4),
    (4, 6, 7)]

def canonical_small_4_4_3_1_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_3_1_1_1_triples

theorem canonical_small_4_4_3_1_1_1_verified : Packing canonical_small_4_4_3_1_1_1_profile.graph canonical_small_4_4_3_1_1_1_triangles ∧
    canonical_small_4_4_3_1_1_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_3_1_1_1_profile canonical_small_4_4_3_1_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_3_1_1_1_inequality : Inequality canonical_small_4_4_3_1_1_1_profile.graph := by
  have hc := canonical_small_4_4_3_1_1_1_profile.ordered_cut_bound 1 1 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_3_1_1_1_verified.1
  rw [canonical_small_4_4_3_1_1_1_verified.2] at hp
  have ht : canonical_small_4_4_3_1_1_1_profile.orderedCutCount 1 1 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_1_1_1_profile : FerrersProfile 4 4 where
  degree := ![4, 1, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_1_1_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 3),
    (0, 4, 7),
    (0, 5, 6),
    (1, 2, 4)]

def canonical_small_4_4_4_1_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_1_1_1_triples

theorem canonical_small_4_4_4_1_1_1_verified : Packing canonical_small_4_4_4_1_1_1_profile.graph canonical_small_4_4_4_1_1_1_triangles ∧
    canonical_small_4_4_4_1_1_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_1_1_1_profile canonical_small_4_4_4_1_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_1_1_1_inequality : Inequality canonical_small_4_4_4_1_1_1_profile.graph := by
  have hc := canonical_small_4_4_4_1_1_1_profile.ordered_cut_bound 1 1 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_1_1_1_verified.1
  rw [canonical_small_4_4_4_1_1_1_verified.2] at hp
  have ht : canonical_small_4_4_4_1_1_1_profile.orderedCutCount 1 1 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_3_2_1_1_profile : FerrersProfile 4 4 where
  degree := ![3, 2, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_3_2_1_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 2),
    (0, 3, 4),
    (0, 5, 6),
    (4, 5, 7)]

def canonical_small_4_4_3_2_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_3_2_1_1_triples

theorem canonical_small_4_4_3_2_1_1_verified : Packing canonical_small_4_4_3_2_1_1_profile.graph canonical_small_4_4_3_2_1_1_triangles ∧
    canonical_small_4_4_3_2_1_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_3_2_1_1_profile canonical_small_4_4_3_2_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_3_2_1_1_inequality : Inequality canonical_small_4_4_3_2_1_1_profile.graph := by
  have hc := canonical_small_4_4_3_2_1_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_3_2_1_1_verified.1
  rw [canonical_small_4_4_3_2_1_1_verified.2] at hp
  have ht : canonical_small_4_4_3_2_1_1_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_2_1_1_profile : FerrersProfile 4 4 where
  degree := ![4, 2, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_2_1_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 3),
    (0, 5, 7),
    (1, 2, 4),
    (4, 6, 7)]

def canonical_small_4_4_4_2_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_2_1_1_triples

theorem canonical_small_4_4_4_2_1_1_verified : Packing canonical_small_4_4_4_2_1_1_profile.graph canonical_small_4_4_4_2_1_1_triangles ∧
    canonical_small_4_4_4_2_1_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_2_1_1_profile canonical_small_4_4_4_2_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_2_1_1_inequality : Inequality canonical_small_4_4_4_2_1_1_profile.graph := by
  have hc := canonical_small_4_4_4_2_1_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_2_1_1_verified.1
  rw [canonical_small_4_4_4_2_1_1_verified.2] at hp
  have ht : canonical_small_4_4_4_2_1_1_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_3_3_1_1_profile : FerrersProfile 4 4 where
  degree := ![3, 3, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_3_3_1_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 3),
    (0, 4, 5),
    (2, 3, 4),
    (4, 6, 7)]

def canonical_small_4_4_3_3_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_3_3_1_1_triples

theorem canonical_small_4_4_3_3_1_1_verified : Packing canonical_small_4_4_3_3_1_1_profile.graph canonical_small_4_4_3_3_1_1_triangles ∧
    canonical_small_4_4_3_3_1_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_3_3_1_1_profile canonical_small_4_4_3_3_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_3_3_1_1_inequality : Inequality canonical_small_4_4_3_3_1_1_profile.graph := by
  have hc := canonical_small_4_4_3_3_1_1_profile.ordered_cut_bound 2 1 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_3_3_1_1_verified.1
  rw [canonical_small_4_4_3_3_1_1_verified.2] at hp
  have ht : canonical_small_4_4_3_3_1_1_profile.orderedCutCount 2 1 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_3_1_1_profile : FerrersProfile 4 4 where
  degree := ![4, 3, 1, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_3_1_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 6),
    (0, 4, 5),
    (1, 2, 4),
    (4, 6, 7)]

def canonical_small_4_4_4_3_1_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_3_1_1_triples

theorem canonical_small_4_4_4_3_1_1_verified : Packing canonical_small_4_4_4_3_1_1_profile.graph canonical_small_4_4_4_3_1_1_triangles ∧
    canonical_small_4_4_4_3_1_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_3_1_1_profile canonical_small_4_4_4_3_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_3_1_1_inequality : Inequality canonical_small_4_4_4_3_1_1_profile.graph := by
  have hc := canonical_small_4_4_4_3_1_1_profile.ordered_cut_bound 2 1 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_3_1_1_verified.1
  rw [canonical_small_4_4_4_3_1_1_verified.2] at hp
  have ht : canonical_small_4_4_4_3_1_1_profile.orderedCutCount 2 1 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_3_2_2_1_profile : FerrersProfile 4 4 where
  degree := ![3, 2, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_3_2_2_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 3),
    (0, 2, 4),
    (1, 4, 5),
    (5, 6, 7)]

def canonical_small_4_4_3_2_2_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_3_2_2_1_triples

theorem canonical_small_4_4_3_2_2_1_verified : Packing canonical_small_4_4_3_2_2_1_profile.graph canonical_small_4_4_3_2_2_1_triangles ∧
    canonical_small_4_4_3_2_2_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_3_2_2_1_profile canonical_small_4_4_3_2_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_3_2_2_1_inequality : Inequality canonical_small_4_4_3_2_2_1_profile.graph := by
  have hc := canonical_small_4_4_3_2_2_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_3_2_2_1_verified.1
  rw [canonical_small_4_4_3_2_2_1_verified.2] at hp
  have ht : canonical_small_4_4_3_2_2_1_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_2_2_1_profile : FerrersProfile 4 4 where
  degree := ![4, 2, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_2_2_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 2),
    (0, 4, 5),
    (0, 6, 7),
    (2, 3, 4)]

def canonical_small_4_4_4_2_2_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_2_2_1_triples

theorem canonical_small_4_4_4_2_2_1_verified : Packing canonical_small_4_4_4_2_2_1_profile.graph canonical_small_4_4_4_2_2_1_triangles ∧
    canonical_small_4_4_4_2_2_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_2_2_1_profile canonical_small_4_4_4_2_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_2_2_1_inequality : Inequality canonical_small_4_4_4_2_2_1_profile.graph := by
  have hc := canonical_small_4_4_4_2_2_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_2_2_1_verified.1
  rw [canonical_small_4_4_4_2_2_1_verified.2] at hp
  have ht : canonical_small_4_4_4_2_2_1_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_3_3_2_1_profile : FerrersProfile 4 4 where
  degree := ![3, 3, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_3_3_2_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 1, 6),
    (0, 3, 4),
    (1, 4, 5),
    (4, 6, 7)]

def canonical_small_4_4_3_3_2_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_3_3_2_1_triples

theorem canonical_small_4_4_3_3_2_1_verified : Packing canonical_small_4_4_3_3_2_1_profile.graph canonical_small_4_4_3_3_2_1_triangles ∧
    canonical_small_4_4_3_3_2_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_3_3_2_1_profile canonical_small_4_4_3_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_3_3_2_1_inequality : Inequality canonical_small_4_4_3_3_2_1_profile.graph := by
  have hc := canonical_small_4_4_3_3_2_1_profile.ordered_cut_bound 3 3 true (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_3_3_2_1_verified.1
  rw [canonical_small_4_4_3_3_2_1_verified.2] at hp
  have ht : canonical_small_4_4_3_3_2_1_profile.orderedCutCount 3 3 true ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def canonical_small_4_4_4_3_2_1_profile : FerrersProfile 4 4 where
  degree := ![4, 3, 2, 1]
  bound := by decide
  antitone := by decide

def canonical_small_4_4_4_3_2_1_triples : List (Fin (4 + 4) × Fin (4 + 4) × Fin (4 + 4)) :=
  [
    (0, 4, 5),
    (0, 6, 7),
    (1, 2, 3),
    (1, 5, 6)]

def canonical_small_4_4_4_3_2_1_triangles : Finset (Finset (Fin 4 ⊕ Fin 4)) :=
  labeledPacking 4 4 canonical_small_4_4_4_3_2_1_triples

theorem canonical_small_4_4_4_3_2_1_verified : Packing canonical_small_4_4_4_3_2_1_profile.graph canonical_small_4_4_4_3_2_1_triangles ∧
    canonical_small_4_4_4_3_2_1_triangles.card = 4 := by
  have h := labeledPacking_correct canonical_small_4_4_4_3_2_1_profile canonical_small_4_4_4_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem canonical_small_4_4_4_3_2_1_inequality : Inequality canonical_small_4_4_4_3_2_1_profile.graph := by
  have hc := canonical_small_4_4_4_3_2_1_profile.ordered_cut_bound 1 2 false (by decide) (by decide)
  have hp := packing_le_number canonical_small_4_4_4_3_2_1_verified.1
  rw [canonical_small_4_4_4_3_2_1_verified.2] at hp
  have ht : canonical_small_4_4_4_3_2_1_profile.orderedCutCount 1 2 false ≤ 2 * 4 := by decide
  exact hc.trans (ht.trans (Nat.mul_le_mul_left 2 hp))

def smallProfiles : (a b : ℕ) → List (CertifiedProfile a b)
  | 2, 4 => [
      ⟨canonical_small_2_4_4_3_profile, canonical_small_2_4_4_3_inequality⟩]
  | 4, 4 => [
      ⟨canonical_small_4_4_4_1_1_0_profile, canonical_small_4_4_4_1_1_0_inequality⟩,
      ⟨canonical_small_4_4_4_2_1_0_profile, canonical_small_4_4_4_2_1_0_inequality⟩,
      ⟨canonical_small_4_4_4_3_1_0_profile, canonical_small_4_4_4_3_1_0_inequality⟩,
      ⟨canonical_small_4_4_4_2_2_0_profile, canonical_small_4_4_4_2_2_0_inequality⟩,
      ⟨canonical_small_4_4_4_3_2_0_profile, canonical_small_4_4_4_3_2_0_inequality⟩,
      ⟨canonical_small_4_4_3_1_1_1_profile, canonical_small_4_4_3_1_1_1_inequality⟩,
      ⟨canonical_small_4_4_4_1_1_1_profile, canonical_small_4_4_4_1_1_1_inequality⟩,
      ⟨canonical_small_4_4_3_2_1_1_profile, canonical_small_4_4_3_2_1_1_inequality⟩,
      ⟨canonical_small_4_4_4_2_1_1_profile, canonical_small_4_4_4_2_1_1_inequality⟩,
      ⟨canonical_small_4_4_3_3_1_1_profile, canonical_small_4_4_3_3_1_1_inequality⟩,
      ⟨canonical_small_4_4_4_3_1_1_profile, canonical_small_4_4_4_3_1_1_inequality⟩,
      ⟨canonical_small_4_4_3_2_2_1_profile, canonical_small_4_4_3_2_2_1_inequality⟩,
      ⟨canonical_small_4_4_4_2_2_1_profile, canonical_small_4_4_4_2_2_1_inequality⟩,
      ⟨canonical_small_4_4_3_3_2_1_profile, canonical_small_4_4_3_3_2_1_inequality⟩,
      ⟨canonical_small_4_4_4_3_2_1_profile, canonical_small_4_4_4_3_2_1_inequality⟩]
  | 4, 5 => [
      ⟨canonical_small_4_5_4_1_1_1_profile, canonical_small_4_5_4_1_1_1_inequality⟩,
      ⟨canonical_small_4_5_4_2_1_1_profile, canonical_small_4_5_4_2_1_1_inequality⟩,
      ⟨canonical_small_4_5_4_3_1_1_profile, canonical_small_4_5_4_3_1_1_inequality⟩,
      ⟨canonical_small_4_5_4_2_2_1_profile, canonical_small_4_5_4_2_2_1_inequality⟩,
      ⟨canonical_small_4_5_4_3_2_1_profile, canonical_small_4_5_4_3_2_1_inequality⟩,
      ⟨canonical_small_4_5_5_4_3_1_profile, canonical_small_4_5_5_4_3_1_inequality⟩]
  | 5, 5 => [
      ⟨canonical_small_5_5_5_4_3_2_0_profile, canonical_small_5_5_5_4_3_2_0_inequality⟩,
      ⟨canonical_small_5_5_5_4_3_1_1_profile, canonical_small_5_5_5_4_3_1_1_inequality⟩,
      ⟨canonical_small_5_5_5_3_3_2_1_profile, canonical_small_5_5_5_3_3_2_1_inequality⟩,
      ⟨canonical_small_5_5_4_4_3_2_1_profile, canonical_small_5_5_4_4_3_2_1_inequality⟩,
      ⟨canonical_small_5_5_5_4_3_2_1_profile, canonical_small_5_5_5_4_3_2_1_inequality⟩]
  | _, _ => []

end ResearchMain.Tuza.Certificates
