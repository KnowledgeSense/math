import MainTheorems.Tuza.Certificates.Basic
import MainTheorems.Tuza.FiniteCertificates

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ResearchMain.Tuza.Certificates

def canonical_sparse_3_8_0_3_profile : FerrersProfile 3 8 where
  degree := ![3, 3, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_3_8_0_3_triples : List (Fin (3 + 8) × Fin (3 + 8) × Fin (3 + 8)) :=
  [
    (0, 1, 2),
    (1, 3, 4),
    (3, 5, 6),
    (3, 7, 8),
    (3, 9, 10),
    (4, 5, 10),
    (4, 6, 7),
    (4, 8, 9),
    (5, 7, 9),
    (6, 8, 10)]

def canonical_sparse_3_8_0_3_triangles : Finset (Finset (Fin 3 ⊕ Fin 8)) :=
  labeledPacking 3 8 canonical_sparse_3_8_0_3_triples

theorem canonical_sparse_3_8_0_3_verified : Packing canonical_sparse_3_8_0_3_profile.graph canonical_sparse_3_8_0_3_triangles ∧
    canonical_sparse_3_8_0_3_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_sparse_3_8_0_3_profile canonical_sparse_3_8_0_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_3_8_1_2_profile : FerrersProfile 3 8 where
  degree := ![4, 2, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_3_8_1_2_triples : List (Fin (3 + 8) × Fin (3 + 8) × Fin (3 + 8)) :=
  [
    (0, 1, 2),
    (0, 3, 5),
    (0, 4, 6),
    (3, 4, 8),
    (3, 6, 10),
    (4, 5, 10),
    (4, 7, 9),
    (5, 6, 9),
    (5, 7, 8),
    (8, 9, 10)]

def canonical_sparse_3_8_1_2_triangles : Finset (Finset (Fin 3 ⊕ Fin 8)) :=
  labeledPacking 3 8 canonical_sparse_3_8_1_2_triples

theorem canonical_sparse_3_8_1_2_verified : Packing canonical_sparse_3_8_1_2_profile.graph canonical_sparse_3_8_1_2_triangles ∧
    canonical_sparse_3_8_1_2_triangles.card = 10 := by
  have h := labeledPacking_correct canonical_sparse_3_8_1_2_profile canonical_sparse_3_8_1_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_6_0_2_profile : FerrersProfile 5 6 where
  degree := ![2, 2, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_6_0_2_triples : List (Fin (5 + 6) × Fin (5 + 6) × Fin (5 + 6)) :=
  [
    (0, 1, 3),
    (0, 2, 6),
    (1, 2, 5),
    (2, 3, 4),
    (5, 6, 8),
    (5, 7, 10),
    (6, 9, 10),
    (7, 8, 9)]

def canonical_sparse_5_6_0_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 6)) :=
  labeledPacking 5 6 canonical_sparse_5_6_0_2_triples

theorem canonical_sparse_5_6_0_2_verified : Packing canonical_sparse_5_6_0_2_profile.graph canonical_sparse_5_6_0_2_triangles ∧
    canonical_sparse_5_6_0_2_triangles.card = 8 := by
  have h := labeledPacking_correct canonical_sparse_5_6_0_2_profile canonical_sparse_5_6_0_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_6_1_1_profile : FerrersProfile 5 6 where
  degree := ![3, 1, 1, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_6_1_1_triples : List (Fin (5 + 6) × Fin (5 + 6) × Fin (5 + 6)) :=
  [
    (0, 1, 5),
    (0, 3, 4),
    (0, 6, 7),
    (1, 2, 4),
    (5, 6, 9),
    (5, 7, 8),
    (6, 8, 10),
    (7, 9, 10)]

def canonical_sparse_5_6_1_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 6)) :=
  labeledPacking 5 6 canonical_sparse_5_6_1_1_triples

theorem canonical_sparse_5_6_1_1_verified : Packing canonical_sparse_5_6_1_1_profile.graph canonical_sparse_5_6_1_1_triangles ∧
    canonical_sparse_5_6_1_1_triangles.card = 8 := by
  have h := labeledPacking_correct canonical_sparse_5_6_1_1_profile canonical_sparse_5_6_1_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_6_1_2_profile : FerrersProfile 5 6 where
  degree := ![3, 2, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_6_1_2_triples : List (Fin (5 + 6) × Fin (5 + 6) × Fin (5 + 6)) :=
  [
    (0, 1, 4),
    (0, 2, 5),
    (0, 6, 7),
    (1, 2, 6),
    (2, 3, 4),
    (5, 6, 10),
    (5, 7, 8),
    (6, 8, 9),
    (7, 9, 10)]

def canonical_sparse_5_6_1_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 6)) :=
  labeledPacking 5 6 canonical_sparse_5_6_1_2_triples

theorem canonical_sparse_5_6_1_2_verified : Packing canonical_sparse_5_6_1_2_profile.graph canonical_sparse_5_6_1_2_triangles ∧
    canonical_sparse_5_6_1_2_triangles.card = 9 := by
  have h := labeledPacking_correct canonical_sparse_5_6_1_2_profile canonical_sparse_5_6_1_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_6_2_0_profile : FerrersProfile 5 6 where
  degree := ![3, 3, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_6_2_0_triples : List (Fin (5 + 6) × Fin (5 + 6) × Fin (5 + 6)) :=
  [
    (0, 1, 5),
    (0, 2, 3),
    (1, 3, 4),
    (1, 6, 7),
    (5, 6, 8),
    (5, 7, 10),
    (6, 9, 10),
    (7, 8, 9)]

def canonical_sparse_5_6_2_0_triangles : Finset (Finset (Fin 5 ⊕ Fin 6)) :=
  labeledPacking 5 6 canonical_sparse_5_6_2_0_triples

theorem canonical_sparse_5_6_2_0_verified : Packing canonical_sparse_5_6_2_0_profile.graph canonical_sparse_5_6_2_0_triangles ∧
    canonical_sparse_5_6_2_0_triangles.card = 8 := by
  have h := labeledPacking_correct canonical_sparse_5_6_2_0_profile canonical_sparse_5_6_2_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_6_2_1_profile : FerrersProfile 5 6 where
  degree := ![3, 3, 1, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_6_2_1_triples : List (Fin (5 + 6) × Fin (5 + 6) × Fin (5 + 6)) :=
  [
    (0, 1, 7),
    (0, 2, 3),
    (0, 5, 6),
    (1, 2, 5),
    (1, 3, 4),
    (5, 7, 9),
    (5, 8, 10),
    (6, 7, 8),
    (6, 9, 10)]

def canonical_sparse_5_6_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 6)) :=
  labeledPacking 5 6 canonical_sparse_5_6_2_1_triples

theorem canonical_sparse_5_6_2_1_verified : Packing canonical_sparse_5_6_2_1_profile.graph canonical_sparse_5_6_2_1_triangles ∧
    canonical_sparse_5_6_2_1_triangles.card = 9 := by
  have h := labeledPacking_correct canonical_sparse_5_6_2_1_profile canonical_sparse_5_6_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_6_2_2_profile : FerrersProfile 5 6 where
  degree := ![3, 3, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_6_2_2_triples : List (Fin (5 + 6) × Fin (5 + 6) × Fin (5 + 6)) :=
  [
    (0, 1, 4),
    (0, 2, 5),
    (1, 2, 6),
    (1, 5, 7),
    (2, 3, 4),
    (5, 6, 10),
    (5, 8, 9),
    (6, 7, 8),
    (7, 9, 10)]

def canonical_sparse_5_6_2_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 6)) :=
  labeledPacking 5 6 canonical_sparse_5_6_2_2_triples

theorem canonical_sparse_5_6_2_2_verified : Packing canonical_sparse_5_6_2_2_profile.graph canonical_sparse_5_6_2_2_triangles ∧
    canonical_sparse_5_6_2_2_triangles.card = 9 := by
  have h := labeledPacking_correct canonical_sparse_5_6_2_2_profile canonical_sparse_5_6_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_7_1_2_profile : FerrersProfile 5 7 where
  degree := ![4, 2, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_7_1_2_triples : List (Fin (5 + 7) × Fin (5 + 7) × Fin (5 + 7)) :=
  [
    (0, 1, 3),
    (0, 2, 6),
    (0, 7, 8),
    (1, 2, 5),
    (2, 3, 4),
    (5, 6, 11),
    (5, 7, 9),
    (5, 8, 10),
    (6, 7, 10),
    (6, 8, 9),
    (9, 10, 11)]

def canonical_sparse_5_7_1_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 7)) :=
  labeledPacking 5 7 canonical_sparse_5_7_1_2_triples

theorem canonical_sparse_5_7_1_2_verified : Packing canonical_sparse_5_7_1_2_profile.graph canonical_sparse_5_7_1_2_triangles ∧
    canonical_sparse_5_7_1_2_triangles.card = 11 := by
  have h := labeledPacking_correct canonical_sparse_5_7_1_2_profile canonical_sparse_5_7_1_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_7_1_3_profile : FerrersProfile 5 7 where
  degree := ![4, 3, 3, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_7_1_3_triples : List (Fin (5 + 7) × Fin (5 + 7) × Fin (5 + 7)) :=
  [
    (0, 1, 4),
    (0, 2, 5),
    (0, 6, 7),
    (1, 2, 6),
    (1, 5, 7),
    (2, 3, 4),
    (5, 8, 9),
    (5, 10, 11),
    (6, 8, 10),
    (6, 9, 11),
    (7, 8, 11),
    (7, 9, 10)]

def canonical_sparse_5_7_1_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 7)) :=
  labeledPacking 5 7 canonical_sparse_5_7_1_3_triples

theorem canonical_sparse_5_7_1_3_verified : Packing canonical_sparse_5_7_1_3_profile.graph canonical_sparse_5_7_1_3_triangles ∧
    canonical_sparse_5_7_1_3_triangles.card = 12 := by
  have h := labeledPacking_correct canonical_sparse_5_7_1_3_profile canonical_sparse_5_7_1_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_7_2_0_profile : FerrersProfile 5 7 where
  degree := ![4, 4, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_7_2_0_triples : List (Fin (5 + 7) × Fin (5 + 7) × Fin (5 + 7)) :=
  [
    (0, 1, 6),
    (0, 3, 4),
    (0, 5, 7),
    (1, 2, 3),
    (1, 5, 8),
    (5, 6, 9),
    (5, 10, 11),
    (6, 7, 11),
    (6, 8, 10),
    (7, 9, 10),
    (8, 9, 11)]

def canonical_sparse_5_7_2_0_triangles : Finset (Finset (Fin 5 ⊕ Fin 7)) :=
  labeledPacking 5 7 canonical_sparse_5_7_2_0_triples

theorem canonical_sparse_5_7_2_0_verified : Packing canonical_sparse_5_7_2_0_profile.graph canonical_sparse_5_7_2_0_triangles ∧
    canonical_sparse_5_7_2_0_triangles.card = 11 := by
  have h := labeledPacking_correct canonical_sparse_5_7_2_0_profile canonical_sparse_5_7_2_0_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_7_2_1_profile : FerrersProfile 5 7 where
  degree := ![4, 4, 1, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_7_2_1_triples : List (Fin (5 + 7) × Fin (5 + 7) × Fin (5 + 7)) :=
  [
    (0, 1, 8),
    (0, 2, 3),
    (0, 6, 7),
    (1, 2, 4),
    (1, 5, 7),
    (5, 8, 9),
    (5, 10, 11),
    (6, 8, 10),
    (6, 9, 11),
    (7, 8, 11),
    (7, 9, 10)]

def canonical_sparse_5_7_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 7)) :=
  labeledPacking 5 7 canonical_sparse_5_7_2_1_triples

theorem canonical_sparse_5_7_2_1_verified : Packing canonical_sparse_5_7_2_1_profile.graph canonical_sparse_5_7_2_1_triangles ∧
    canonical_sparse_5_7_2_1_triangles.card = 11 := by
  have h := labeledPacking_correct canonical_sparse_5_7_2_1_profile canonical_sparse_5_7_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_7_2_2_profile : FerrersProfile 5 7 where
  degree := ![4, 4, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_7_2_2_triples : List (Fin (5 + 7) × Fin (5 + 7) × Fin (5 + 7)) :=
  [
    (0, 1, 5),
    (0, 2, 6),
    (0, 3, 4),
    (0, 7, 8),
    (1, 2, 3),
    (1, 6, 8),
    (5, 6, 11),
    (5, 7, 9),
    (5, 8, 10),
    (6, 9, 10),
    (7, 10, 11),
    (8, 9, 11)]

def canonical_sparse_5_7_2_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 7)) :=
  labeledPacking 5 7 canonical_sparse_5_7_2_2_triples

theorem canonical_sparse_5_7_2_2_verified : Packing canonical_sparse_5_7_2_2_profile.graph canonical_sparse_5_7_2_2_triangles ∧
    canonical_sparse_5_7_2_2_triangles.card = 12 := by
  have h := labeledPacking_correct canonical_sparse_5_7_2_2_profile canonical_sparse_5_7_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_7_2_3_profile : FerrersProfile 5 7 where
  degree := ![4, 4, 3, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_7_2_3_triples : List (Fin (5 + 7) × Fin (5 + 7) × Fin (5 + 7)) :=
  [
    (0, 1, 8),
    (0, 2, 3),
    (0, 5, 7),
    (1, 2, 4),
    (1, 5, 6),
    (2, 6, 7),
    (5, 8, 10),
    (5, 9, 11),
    (6, 8, 9),
    (6, 10, 11),
    (7, 8, 11),
    (7, 9, 10)]

def canonical_sparse_5_7_2_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 7)) :=
  labeledPacking 5 7 canonical_sparse_5_7_2_3_triples

theorem canonical_sparse_5_7_2_3_verified : Packing canonical_sparse_5_7_2_3_profile.graph canonical_sparse_5_7_2_3_triangles ∧
    canonical_sparse_5_7_2_3_triangles.card = 12 := by
  have h := labeledPacking_correct canonical_sparse_5_7_2_3_profile canonical_sparse_5_7_2_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_8_0_3_profile : FerrersProfile 5 8 where
  degree := ![3, 3, 3, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_8_0_3_triples : List (Fin (5 + 8) × Fin (5 + 8) × Fin (5 + 8)) :=
  [
    (0, 1, 3),
    (0, 2, 7),
    (1, 2, 5),
    (1, 6, 7),
    (2, 3, 4),
    (5, 6, 8),
    (5, 7, 12),
    (5, 10, 11),
    (6, 9, 10),
    (6, 11, 12),
    (7, 8, 10),
    (7, 9, 11),
    (8, 9, 12)]

def canonical_sparse_5_8_0_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 8)) :=
  labeledPacking 5 8 canonical_sparse_5_8_0_3_triples

theorem canonical_sparse_5_8_0_3_verified : Packing canonical_sparse_5_8_0_3_profile.graph canonical_sparse_5_8_0_3_triangles ∧
    canonical_sparse_5_8_0_3_triangles.card = 13 := by
  have h := labeledPacking_correct canonical_sparse_5_8_0_3_profile canonical_sparse_5_8_0_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_8_1_2_profile : FerrersProfile 5 8 where
  degree := ![4, 2, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_8_1_2_triples : List (Fin (5 + 8) × Fin (5 + 8) × Fin (5 + 8)) :=
  [
    (0, 1, 3),
    (0, 2, 6),
    (0, 5, 8),
    (1, 2, 5),
    (2, 3, 4),
    (5, 6, 12),
    (5, 7, 11),
    (5, 9, 10),
    (6, 9, 11),
    (7, 8, 9),
    (7, 10, 12),
    (8, 10, 11)]

def canonical_sparse_5_8_1_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 8)) :=
  labeledPacking 5 8 canonical_sparse_5_8_1_2_triples

theorem canonical_sparse_5_8_1_2_verified : Packing canonical_sparse_5_8_1_2_profile.graph canonical_sparse_5_8_1_2_triangles ∧
    canonical_sparse_5_8_1_2_triangles.card = 12 := by
  have h := labeledPacking_correct canonical_sparse_5_8_1_2_profile canonical_sparse_5_8_1_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_8_2_1_profile : FerrersProfile 5 8 where
  degree := ![4, 4, 1, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_8_2_1_triples : List (Fin (5 + 8) × Fin (5 + 8) × Fin (5 + 8)) :=
  [
    (0, 1, 8),
    (0, 2, 5),
    (0, 3, 4),
    (0, 6, 7),
    (1, 2, 4),
    (1, 5, 7),
    (5, 6, 9),
    (5, 10, 11),
    (6, 8, 11),
    (6, 10, 12),
    (7, 8, 10),
    (7, 11, 12),
    (8, 9, 12)]

def canonical_sparse_5_8_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 8)) :=
  labeledPacking 5 8 canonical_sparse_5_8_2_1_triples

theorem canonical_sparse_5_8_2_1_verified : Packing canonical_sparse_5_8_2_1_profile.graph canonical_sparse_5_8_2_1_triangles ∧
    canonical_sparse_5_8_2_1_triangles.card = 13 := by
  have h := labeledPacking_correct canonical_sparse_5_8_2_1_profile canonical_sparse_5_8_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_8_2_3_profile : FerrersProfile 5 8 where
  degree := ![4, 4, 3, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_8_2_3_triples : List (Fin (5 + 8) × Fin (5 + 8) × Fin (5 + 8)) :=
  [
    (0, 1, 7),
    (0, 2, 6),
    (0, 3, 4),
    (0, 5, 8),
    (1, 2, 4),
    (1, 5, 6),
    (2, 5, 7),
    (5, 9, 10),
    (5, 11, 12),
    (6, 8, 11),
    (6, 10, 12),
    (7, 8, 10),
    (7, 9, 11),
    (8, 9, 12)]

def canonical_sparse_5_8_2_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 8)) :=
  labeledPacking 5 8 canonical_sparse_5_8_2_3_triples

theorem canonical_sparse_5_8_2_3_verified : Packing canonical_sparse_5_8_2_3_profile.graph canonical_sparse_5_8_2_3_triangles ∧
    canonical_sparse_5_8_2_3_triangles.card = 14 := by
  have h := labeledPacking_correct canonical_sparse_5_8_2_3_profile canonical_sparse_5_8_2_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_9_1_4_profile : FerrersProfile 5 9 where
  degree := ![5, 4, 4, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_9_1_4_triples : List (Fin (5 + 9) × Fin (5 + 9) × Fin (5 + 9)) :=
  [
    (0, 1, 4),
    (0, 2, 5),
    (0, 6, 7),
    (0, 8, 9),
    (1, 2, 6),
    (1, 5, 7),
    (2, 3, 4),
    (2, 7, 8),
    (5, 6, 10),
    (5, 8, 12),
    (5, 9, 11),
    (6, 8, 13),
    (6, 9, 12),
    (7, 9, 10),
    (7, 11, 13),
    (8, 10, 11),
    (10, 12, 13)]

def canonical_sparse_5_9_1_4_triangles : Finset (Finset (Fin 5 ⊕ Fin 9)) :=
  labeledPacking 5 9 canonical_sparse_5_9_1_4_triples

theorem canonical_sparse_5_9_1_4_verified : Packing canonical_sparse_5_9_1_4_profile.graph canonical_sparse_5_9_1_4_triangles ∧
    canonical_sparse_5_9_1_4_triangles.card = 17 := by
  have h := labeledPacking_correct canonical_sparse_5_9_1_4_profile canonical_sparse_5_9_1_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_9_2_1_profile : FerrersProfile 5 9 where
  degree := ![5, 5, 1, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_9_2_1_triples : List (Fin (5 + 9) × Fin (5 + 9) × Fin (5 + 9)) :=
  [
    (0, 1, 6),
    (0, 2, 3),
    (0, 5, 7),
    (0, 8, 9),
    (1, 3, 4),
    (1, 7, 9),
    (5, 6, 10),
    (5, 8, 13),
    (5, 9, 11),
    (6, 7, 8),
    (6, 9, 12),
    (6, 11, 13),
    (7, 10, 11),
    (7, 12, 13),
    (8, 11, 12),
    (9, 10, 13)]

def canonical_sparse_5_9_2_1_triangles : Finset (Finset (Fin 5 ⊕ Fin 9)) :=
  labeledPacking 5 9 canonical_sparse_5_9_2_1_triples

theorem canonical_sparse_5_9_2_1_verified : Packing canonical_sparse_5_9_2_1_profile.graph canonical_sparse_5_9_2_1_triangles ∧
    canonical_sparse_5_9_2_1_triangles.card = 16 := by
  have h := labeledPacking_correct canonical_sparse_5_9_2_1_profile canonical_sparse_5_9_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_9_2_2_profile : FerrersProfile 5 9 where
  degree := ![5, 5, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_9_2_2_triples : List (Fin (5 + 9) × Fin (5 + 9) × Fin (5 + 9)) :=
  [
    (0, 1, 7),
    (0, 2, 5),
    (0, 6, 9),
    (1, 2, 4),
    (1, 5, 6),
    (1, 8, 9),
    (5, 7, 13),
    (5, 8, 12),
    (5, 9, 10),
    (6, 7, 10),
    (6, 12, 13),
    (7, 8, 11),
    (7, 9, 12),
    (8, 10, 13),
    (9, 11, 13),
    (10, 11, 12)]

def canonical_sparse_5_9_2_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 9)) :=
  labeledPacking 5 9 canonical_sparse_5_9_2_2_triples

theorem canonical_sparse_5_9_2_2_verified : Packing canonical_sparse_5_9_2_2_profile.graph canonical_sparse_5_9_2_2_triangles ∧
    canonical_sparse_5_9_2_2_triangles.card = 16 := by
  have h := labeledPacking_correct canonical_sparse_5_9_2_2_profile canonical_sparse_5_9_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_9_2_3_profile : FerrersProfile 5 9 where
  degree := ![5, 5, 3, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_9_2_3_triples : List (Fin (5 + 9) × Fin (5 + 9) × Fin (5 + 9)) :=
  [
    (0, 1, 7),
    (0, 2, 4),
    (0, 5, 6),
    (0, 8, 9),
    (1, 2, 5),
    (1, 3, 4),
    (1, 6, 9),
    (2, 6, 7),
    (5, 10, 12),
    (5, 11, 13),
    (6, 8, 12),
    (6, 10, 13),
    (7, 8, 13),
    (7, 9, 10),
    (7, 11, 12),
    (8, 10, 11),
    (9, 12, 13)]

def canonical_sparse_5_9_2_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 9)) :=
  labeledPacking 5 9 canonical_sparse_5_9_2_3_triples

theorem canonical_sparse_5_9_2_3_verified : Packing canonical_sparse_5_9_2_3_profile.graph canonical_sparse_5_9_2_3_triangles ∧
    canonical_sparse_5_9_2_3_triangles.card = 17 := by
  have h := labeledPacking_correct canonical_sparse_5_9_2_3_profile canonical_sparse_5_9_2_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_9_2_4_profile : FerrersProfile 5 9 where
  degree := ![5, 5, 4, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_9_2_4_triples : List (Fin (5 + 9) × Fin (5 + 9) × Fin (5 + 9)) :=
  [
    (0, 1, 5),
    (0, 2, 3),
    (0, 6, 9),
    (0, 7, 8),
    (1, 2, 4),
    (1, 6, 7),
    (1, 8, 9),
    (2, 5, 7),
    (2, 6, 8),
    (5, 8, 10),
    (5, 9, 13),
    (5, 11, 12),
    (6, 10, 11),
    (6, 12, 13),
    (7, 9, 11),
    (8, 11, 13),
    (9, 10, 12)]

def canonical_sparse_5_9_2_4_triangles : Finset (Finset (Fin 5 ⊕ Fin 9)) :=
  labeledPacking 5 9 canonical_sparse_5_9_2_4_triples

theorem canonical_sparse_5_9_2_4_verified : Packing canonical_sparse_5_9_2_4_profile.graph canonical_sparse_5_9_2_4_triangles ∧
    canonical_sparse_5_9_2_4_triangles.card = 17 := by
  have h := labeledPacking_correct canonical_sparse_5_9_2_4_profile canonical_sparse_5_9_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_10_1_2_profile : FerrersProfile 5 10 where
  degree := ![5, 2, 2, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_10_1_2_triples : List (Fin (5 + 10) × Fin (5 + 10) × Fin (5 + 10)) :=
  [
    (0, 2, 3),
    (0, 5, 6),
    (0, 7, 9),
    (1, 2, 6),
    (1, 3, 4),
    (5, 7, 11),
    (5, 8, 9),
    (5, 10, 14),
    (6, 7, 8),
    (6, 9, 13),
    (6, 11, 14),
    (7, 10, 13),
    (7, 12, 14),
    (8, 10, 12),
    (8, 13, 14),
    (9, 10, 11),
    (11, 12, 13)]

def canonical_sparse_5_10_1_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 10)) :=
  labeledPacking 5 10 canonical_sparse_5_10_1_2_triples

theorem canonical_sparse_5_10_1_2_verified : Packing canonical_sparse_5_10_1_2_profile.graph canonical_sparse_5_10_1_2_triangles ∧
    canonical_sparse_5_10_1_2_triangles.card = 17 := by
  have h := labeledPacking_correct canonical_sparse_5_10_1_2_profile canonical_sparse_5_10_1_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_10_1_3_profile : FerrersProfile 5 10 where
  degree := ![5, 3, 3, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_10_1_3_triples : List (Fin (5 + 10) × Fin (5 + 10) × Fin (5 + 10)) :=
  [
    (0, 1, 4),
    (0, 2, 3),
    (0, 6, 8),
    (0, 7, 9),
    (1, 2, 6),
    (1, 5, 7),
    (5, 6, 11),
    (5, 9, 12),
    (5, 10, 14),
    (6, 7, 10),
    (6, 9, 14),
    (6, 12, 13),
    (7, 8, 11),
    (7, 13, 14),
    (8, 9, 10),
    (8, 12, 14),
    (9, 11, 13),
    (10, 11, 12)]

def canonical_sparse_5_10_1_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 10)) :=
  labeledPacking 5 10 canonical_sparse_5_10_1_3_triples

theorem canonical_sparse_5_10_1_3_verified : Packing canonical_sparse_5_10_1_3_profile.graph canonical_sparse_5_10_1_3_triangles ∧
    canonical_sparse_5_10_1_3_triangles.card = 18 := by
  have h := labeledPacking_correct canonical_sparse_5_10_1_3_profile canonical_sparse_5_10_1_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_5_11_1_4_profile : FerrersProfile 5 11 where
  degree := ![6, 4, 4, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_5_11_1_4_triples : List (Fin (5 + 11) × Fin (5 + 11) × Fin (5 + 11)) :=
  [
    (0, 1, 7),
    (0, 2, 8),
    (0, 9, 10),
    (1, 2, 6),
    (1, 3, 4),
    (1, 5, 8),
    (2, 5, 7),
    (5, 9, 15),
    (5, 10, 14),
    (5, 11, 13),
    (6, 7, 13),
    (6, 8, 11),
    (6, 10, 15),
    (6, 12, 14),
    (7, 8, 15),
    (7, 9, 12),
    (7, 10, 11),
    (8, 9, 13),
    (9, 11, 14),
    (10, 12, 13),
    (11, 12, 15),
    (13, 14, 15)]

def canonical_sparse_5_11_1_4_triangles : Finset (Finset (Fin 5 ⊕ Fin 11)) :=
  labeledPacking 5 11 canonical_sparse_5_11_1_4_triples

theorem canonical_sparse_5_11_1_4_verified : Packing canonical_sparse_5_11_1_4_profile.graph canonical_sparse_5_11_1_4_triangles ∧
    canonical_sparse_5_11_1_4_triangles.card = 22 := by
  have h := labeledPacking_correct canonical_sparse_5_11_1_4_profile canonical_sparse_5_11_1_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_6_7_2_2_profile : FerrersProfile 6 7 where
  degree := ![4, 4, 2, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_6_7_2_2_triples : List (Fin (6 + 7) × Fin (6 + 7) × Fin (6 + 7)) :=
  [
    (0, 1, 5),
    (0, 2, 4),
    (0, 6, 9),
    (0, 7, 8),
    (1, 2, 7),
    (1, 3, 4),
    (1, 8, 9),
    (2, 3, 5),
    (6, 7, 12),
    (6, 8, 10),
    (7, 9, 11),
    (8, 11, 12),
    (9, 10, 12)]

def canonical_sparse_6_7_2_2_triangles : Finset (Finset (Fin 6 ⊕ Fin 7)) :=
  labeledPacking 6 7 canonical_sparse_6_7_2_2_triples

theorem canonical_sparse_6_7_2_2_verified : Packing canonical_sparse_6_7_2_2_profile.graph canonical_sparse_6_7_2_2_triangles ∧
    canonical_sparse_6_7_2_2_triangles.card = 13 := by
  have h := labeledPacking_correct canonical_sparse_6_7_2_2_profile canonical_sparse_6_7_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_7_3_3_profile : FerrersProfile 7 7 where
  degree := ![4, 4, 4, 3, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_7_3_3_triples : List (Fin (7 + 7) × Fin (7 + 7) × Fin (7 + 7)) :=
  [
    (0, 1, 5),
    (0, 3, 9),
    (0, 4, 6),
    (0, 8, 10),
    (1, 2, 4),
    (1, 3, 6),
    (1, 8, 9),
    (2, 3, 8),
    (2, 5, 6),
    (2, 9, 10),
    (3, 4, 5),
    (7, 8, 11),
    (7, 9, 13),
    (7, 10, 12),
    (8, 12, 13),
    (9, 11, 12),
    (10, 11, 13)]

def canonical_sparse_7_7_3_3_triangles : Finset (Finset (Fin 7 ⊕ Fin 7)) :=
  labeledPacking 7 7 canonical_sparse_7_7_3_3_triples

theorem canonical_sparse_7_7_3_3_verified : Packing canonical_sparse_7_7_3_3_profile.graph canonical_sparse_7_7_3_3_triangles ∧
    canonical_sparse_7_7_3_3_triangles.card = 17 := by
  have h := labeledPacking_correct canonical_sparse_7_7_3_3_profile canonical_sparse_7_7_3_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_8_2_3_profile : FerrersProfile 7 8 where
  degree := ![4, 4, 3, 3, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_8_2_3_triples : List (Fin (7 + 8) × Fin (7 + 8) × Fin (7 + 8)) :=
  [
    (0, 1, 6),
    (0, 2, 4),
    (0, 3, 5),
    (0, 7, 9),
    (1, 2, 7),
    (1, 3, 9),
    (1, 4, 5),
    (1, 8, 10),
    (2, 5, 6),
    (2, 8, 9),
    (3, 4, 6),
    (3, 7, 8),
    (7, 10, 13),
    (7, 11, 14),
    (9, 10, 14),
    (9, 11, 13),
    (10, 11, 12),
    (12, 13, 14)]

def canonical_sparse_7_8_2_3_triangles : Finset (Finset (Fin 7 ⊕ Fin 8)) :=
  labeledPacking 7 8 canonical_sparse_7_8_2_3_triples

theorem canonical_sparse_7_8_2_3_verified : Packing canonical_sparse_7_8_2_3_profile.graph canonical_sparse_7_8_2_3_triangles ∧
    canonical_sparse_7_8_2_3_triangles.card = 18 := by
  have h := labeledPacking_correct canonical_sparse_7_8_2_3_profile canonical_sparse_7_8_2_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_9_2_4_profile : FerrersProfile 7 9 where
  degree := ![5, 5, 4, 4, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_9_2_4_triples : List (Fin (7 + 9) × Fin (7 + 9) × Fin (7 + 9)) :=
  [
    (0, 1, 6),
    (0, 2, 4),
    (0, 3, 5),
    (0, 7, 11),
    (0, 8, 9),
    (1, 2, 8),
    (1, 3, 10),
    (1, 4, 5),
    (2, 3, 9),
    (2, 5, 6),
    (2, 7, 10),
    (3, 4, 6),
    (3, 7, 8),
    (7, 9, 13),
    (7, 14, 15),
    (8, 10, 12),
    (8, 11, 14),
    (8, 13, 15),
    (9, 10, 14),
    (9, 11, 15),
    (10, 11, 13),
    (12, 13, 14)]

def canonical_sparse_7_9_2_4_triangles : Finset (Finset (Fin 7 ⊕ Fin 9)) :=
  labeledPacking 7 9 canonical_sparse_7_9_2_4_triples

theorem canonical_sparse_7_9_2_4_verified : Packing canonical_sparse_7_9_2_4_profile.graph canonical_sparse_7_9_2_4_triangles ∧
    canonical_sparse_7_9_2_4_triangles.card = 22 := by
  have h := labeledPacking_correct canonical_sparse_7_9_2_4_profile canonical_sparse_7_9_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_9_3_3_profile : FerrersProfile 7 9 where
  degree := ![5, 5, 5, 3, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_9_3_3_triples : List (Fin (7 + 9) × Fin (7 + 9) × Fin (7 + 9)) :=
  [
    (0, 1, 6),
    (0, 2, 5),
    (0, 3, 4),
    (0, 7, 11),
    (0, 8, 10),
    (1, 2, 3),
    (1, 4, 5),
    (1, 9, 11),
    (2, 4, 6),
    (2, 7, 8),
    (2, 10, 11),
    (3, 5, 6),
    (3, 8, 9),
    (7, 9, 14),
    (7, 10, 12),
    (7, 13, 15),
    (8, 11, 13),
    (8, 12, 15),
    (9, 10, 15),
    (9, 12, 13),
    (10, 13, 14),
    (11, 12, 14)]

def canonical_sparse_7_9_3_3_triangles : Finset (Finset (Fin 7 ⊕ Fin 9)) :=
  labeledPacking 7 9 canonical_sparse_7_9_3_3_triples

theorem canonical_sparse_7_9_3_3_verified : Packing canonical_sparse_7_9_3_3_profile.graph canonical_sparse_7_9_3_3_triangles ∧
    canonical_sparse_7_9_3_3_triangles.card = 22 := by
  have h := labeledPacking_correct canonical_sparse_7_9_3_3_profile canonical_sparse_7_9_3_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_9_3_4_profile : FerrersProfile 7 9 where
  degree := ![5, 5, 5, 4, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_9_3_4_triples : List (Fin (7 + 9) × Fin (7 + 9) × Fin (7 + 9)) :=
  [
    (0, 1, 4),
    (0, 2, 10),
    (0, 3, 9),
    (0, 5, 6),
    (0, 8, 11),
    (1, 2, 6),
    (1, 3, 5),
    (1, 7, 9),
    (1, 10, 11),
    (2, 4, 5),
    (2, 7, 8),
    (2, 9, 11),
    (3, 4, 6),
    (7, 10, 12),
    (7, 11, 15),
    (7, 13, 14),
    (8, 9, 13),
    (8, 10, 14),
    (8, 12, 15),
    (9, 14, 15),
    (10, 13, 15),
    (11, 12, 13)]

def canonical_sparse_7_9_3_4_triangles : Finset (Finset (Fin 7 ⊕ Fin 9)) :=
  labeledPacking 7 9 canonical_sparse_7_9_3_4_triples

theorem canonical_sparse_7_9_3_4_verified : Packing canonical_sparse_7_9_3_4_profile.graph canonical_sparse_7_9_3_4_triangles ∧
    canonical_sparse_7_9_3_4_triangles.card = 22 := by
  have h := labeledPacking_correct canonical_sparse_7_9_3_4_profile canonical_sparse_7_9_3_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_11_2_4_profile : FerrersProfile 7 11 where
  degree := ![6, 6, 4, 4, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_11_2_4_triples : List (Fin (7 + 11) × Fin (7 + 11) × Fin (7 + 11)) :=
  [
    (0, 1, 12),
    (0, 2, 10),
    (0, 3, 4),
    (0, 5, 6),
    (0, 7, 8),
    (0, 9, 11),
    (1, 2, 7),
    (1, 3, 9),
    (1, 4, 6),
    (1, 10, 11),
    (2, 3, 5),
    (2, 8, 9),
    (3, 7, 10),
    (7, 9, 13),
    (7, 11, 16),
    (7, 12, 14),
    (7, 15, 17),
    (8, 10, 17),
    (8, 11, 12),
    (8, 14, 16),
    (9, 10, 16),
    (9, 14, 17),
    (10, 13, 14),
    (11, 13, 17),
    (11, 14, 15),
    (12, 13, 15),
    (12, 16, 17)]

def canonical_sparse_7_11_2_4_triangles : Finset (Finset (Fin 7 ⊕ Fin 11)) :=
  labeledPacking 7 11 canonical_sparse_7_11_2_4_triples

theorem canonical_sparse_7_11_2_4_verified : Packing canonical_sparse_7_11_2_4_profile.graph canonical_sparse_7_11_2_4_triangles ∧
    canonical_sparse_7_11_2_4_triangles.card = 27 := by
  have h := labeledPacking_correct canonical_sparse_7_11_2_4_profile canonical_sparse_7_11_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_12_2_5_profile : FerrersProfile 7 12 where
  degree := ![6, 6, 5, 5, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_12_2_5_triples : List (Fin (7 + 12) × Fin (7 + 12) × Fin (7 + 12)) :=
  [
    (0, 1, 4),
    (0, 2, 5),
    (0, 3, 11),
    (0, 7, 10),
    (0, 8, 12),
    (1, 2, 7),
    (1, 3, 6),
    (1, 8, 11),
    (1, 9, 12),
    (2, 3, 8),
    (2, 9, 10),
    (3, 4, 5),
    (3, 7, 9),
    (7, 8, 16),
    (7, 11, 13),
    (7, 12, 14),
    (7, 15, 18),
    (8, 9, 13),
    (8, 10, 17),
    (8, 14, 18),
    (9, 11, 18),
    (9, 14, 17),
    (9, 15, 16),
    (10, 11, 12),
    (10, 13, 15),
    (10, 16, 18),
    (11, 14, 15),
    (11, 16, 17),
    (12, 13, 18),
    (12, 15, 17),
    (13, 14, 16)]

def canonical_sparse_7_12_2_5_triangles : Finset (Finset (Fin 7 ⊕ Fin 12)) :=
  labeledPacking 7 12 canonical_sparse_7_12_2_5_triples

theorem canonical_sparse_7_12_2_5_verified : Packing canonical_sparse_7_12_2_5_profile.graph canonical_sparse_7_12_2_5_triangles ∧
    canonical_sparse_7_12_2_5_triangles.card = 31 := by
  have h := labeledPacking_correct canonical_sparse_7_12_2_5_profile canonical_sparse_7_12_2_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_7_14_2_5_profile : FerrersProfile 7 14 where
  degree := ![7, 7, 5, 5, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_7_14_2_5_triples : List (Fin (7 + 14) × Fin (7 + 14) × Fin (7 + 14)) :=
  [
    (0, 1, 9),
    (0, 3, 10),
    (0, 5, 6),
    (0, 8, 11),
    (0, 12, 13),
    (1, 3, 11),
    (1, 8, 12),
    (1, 10, 13),
    (2, 3, 8),
    (2, 4, 6),
    (2, 7, 10),
    (2, 9, 11),
    (3, 4, 5),
    (7, 8, 9),
    (7, 11, 13),
    (7, 12, 14),
    (7, 15, 20),
    (7, 17, 18),
    (8, 10, 15),
    (8, 13, 18),
    (8, 14, 20),
    (9, 10, 12),
    (9, 13, 19),
    (9, 14, 18),
    (9, 15, 17),
    (9, 16, 20),
    (10, 11, 17),
    (10, 14, 16),
    (10, 18, 19),
    (11, 14, 15),
    (11, 16, 18),
    (11, 19, 20),
    (12, 15, 19),
    (12, 16, 17),
    (12, 18, 20),
    (13, 15, 16),
    (13, 17, 20),
    (14, 17, 19)]

def canonical_sparse_7_14_2_5_triangles : Finset (Finset (Fin 7 ⊕ Fin 14)) :=
  labeledPacking 7 14 canonical_sparse_7_14_2_5_triples

theorem canonical_sparse_7_14_2_5_verified : Packing canonical_sparse_7_14_2_5_profile.graph canonical_sparse_7_14_2_5_triangles ∧
    canonical_sparse_7_14_2_5_triangles.card = 38 := by
  have h := labeledPacking_correct canonical_sparse_7_14_2_5_profile canonical_sparse_7_14_2_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_8_9_3_2_profile : FerrersProfile 8 9 where
  degree := ![5, 5, 5, 2, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_8_9_3_2_triples : List (Fin (8 + 9) × Fin (8 + 9) × Fin (8 + 9)) :=
  [
    (0, 1, 10),
    (0, 2, 4),
    (0, 3, 7),
    (0, 5, 6),
    (0, 8, 9),
    (1, 2, 12),
    (1, 3, 5),
    (1, 4, 7),
    (1, 9, 11),
    (2, 3, 9),
    (2, 5, 7),
    (2, 8, 11),
    (3, 4, 6),
    (8, 10, 15),
    (8, 12, 13),
    (8, 14, 16),
    (9, 10, 14),
    (9, 12, 15),
    (9, 13, 16),
    (10, 11, 13),
    (10, 12, 16),
    (11, 12, 14),
    (11, 15, 16)]

def canonical_sparse_8_9_3_2_triangles : Finset (Finset (Fin 8 ⊕ Fin 9)) :=
  labeledPacking 8 9 canonical_sparse_8_9_3_2_triples

theorem canonical_sparse_8_9_3_2_verified : Packing canonical_sparse_8_9_3_2_profile.graph canonical_sparse_8_9_3_2_triangles ∧
    canonical_sparse_8_9_3_2_triangles.card = 23 := by
  have h := labeledPacking_correct canonical_sparse_8_9_3_2_profile canonical_sparse_8_9_3_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_8_11_3_4_profile : FerrersProfile 8 11 where
  degree := ![6, 6, 6, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_8_11_3_4_triples : List (Fin (8 + 11) × Fin (8 + 11) × Fin (8 + 11)) :=
  [
    (0, 1, 12),
    (0, 2, 10),
    (0, 3, 9),
    (0, 4, 5),
    (0, 6, 7),
    (0, 8, 13),
    (1, 2, 13),
    (1, 3, 4),
    (1, 5, 7),
    (1, 8, 9),
    (1, 10, 11),
    (2, 3, 7),
    (2, 4, 6),
    (2, 8, 12),
    (2, 9, 11),
    (3, 5, 6),
    (3, 8, 10),
    (8, 11, 18),
    (8, 14, 15),
    (8, 16, 17),
    (9, 12, 13),
    (9, 14, 17),
    (9, 16, 18),
    (10, 12, 18),
    (10, 13, 17),
    (10, 15, 16),
    (11, 12, 14),
    (11, 13, 16),
    (12, 15, 17),
    (13, 14, 18)]

def canonical_sparse_8_11_3_4_triangles : Finset (Finset (Fin 8 ⊕ Fin 11)) :=
  labeledPacking 8 11 canonical_sparse_8_11_3_4_triples

theorem canonical_sparse_8_11_3_4_verified : Packing canonical_sparse_8_11_3_4_profile.graph canonical_sparse_8_11_3_4_triangles ∧
    canonical_sparse_8_11_3_4_triangles.card = 30 := by
  have h := labeledPacking_correct canonical_sparse_8_11_3_4_profile canonical_sparse_8_11_3_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_1_4_profile : FerrersProfile 9 9 where
  degree := ![5, 4, 4, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_1_4_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 7),
    (0, 2, 6),
    (0, 3, 8),
    (0, 4, 12),
    (0, 9, 13),
    (0, 10, 11),
    (1, 2, 11),
    (1, 3, 4),
    (1, 5, 6),
    (2, 3, 5),
    (2, 4, 10),
    (2, 7, 8),
    (2, 9, 12),
    (3, 6, 7),
    (3, 9, 10),
    (3, 11, 12),
    (4, 5, 7),
    (4, 6, 8),
    (9, 11, 14),
    (9, 15, 16),
    (10, 12, 13),
    (10, 14, 16),
    (10, 15, 17),
    (11, 13, 15),
    (12, 14, 15),
    (12, 16, 17),
    (13, 14, 17)]

def canonical_sparse_9_9_1_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_1_4_triples

theorem canonical_sparse_9_9_1_4_verified : Packing canonical_sparse_9_9_1_4_profile.graph canonical_sparse_9_9_1_4_triangles ∧
    canonical_sparse_9_9_1_4_triangles.card = 27 := by
  have h := labeledPacking_correct canonical_sparse_9_9_1_4_profile canonical_sparse_9_9_1_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_2_4_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 4, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_2_4_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 5),
    (0, 2, 7),
    (0, 3, 12),
    (0, 4, 9),
    (0, 6, 8),
    (0, 10, 13),
    (1, 2, 12),
    (1, 3, 6),
    (1, 7, 8),
    (1, 9, 13),
    (1, 10, 11),
    (2, 3, 8),
    (2, 4, 11),
    (2, 5, 6),
    (2, 9, 10),
    (3, 5, 7),
    (4, 5, 8),
    (4, 6, 7),
    (4, 10, 12),
    (9, 11, 14),
    (9, 12, 15),
    (10, 15, 17),
    (11, 12, 16),
    (11, 13, 15),
    (12, 14, 17),
    (13, 16, 17),
    (14, 15, 16)]

def canonical_sparse_9_9_2_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_2_4_triples

theorem canonical_sparse_9_9_2_4_verified : Packing canonical_sparse_9_9_2_4_profile.graph canonical_sparse_9_9_2_4_triangles ∧
    canonical_sparse_9_9_2_4_triangles.card = 27 := by
  have h := labeledPacking_correct canonical_sparse_9_9_2_4_profile canonical_sparse_9_9_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_3_3_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 5, 3, 3, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_3_3_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 2, 6),
    (0, 3, 9),
    (0, 4, 5),
    (0, 7, 8),
    (0, 10, 13),
    (1, 2, 8),
    (1, 3, 10),
    (1, 4, 7),
    (1, 5, 6),
    (1, 9, 13),
    (1, 11, 12),
    (2, 3, 11),
    (2, 4, 9),
    (2, 5, 7),
    (3, 6, 7),
    (4, 6, 8),
    (4, 10, 11),
    (9, 10, 16),
    (9, 11, 14),
    (9, 12, 17),
    (10, 12, 14),
    (10, 15, 17),
    (11, 13, 15),
    (11, 16, 17),
    (12, 13, 16),
    (13, 14, 17),
    (14, 15, 16)]

def canonical_sparse_9_9_3_3_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_3_3_triples

theorem canonical_sparse_9_9_3_3_verified : Packing canonical_sparse_9_9_3_3_profile.graph canonical_sparse_9_9_3_3_triangles ∧
    canonical_sparse_9_9_3_3_triangles.card = 27 := by
  have h := labeledPacking_correct canonical_sparse_9_9_3_3_profile canonical_sparse_9_9_3_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_3_4_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 5, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_3_4_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 6),
    (0, 2, 11),
    (0, 3, 10),
    (0, 4, 5),
    (0, 7, 8),
    (0, 9, 13),
    (1, 2, 4),
    (1, 3, 9),
    (1, 5, 7),
    (1, 10, 12),
    (1, 11, 13),
    (2, 3, 7),
    (2, 5, 8),
    (2, 9, 12),
    (2, 10, 13),
    (3, 4, 8),
    (3, 5, 6),
    (4, 6, 7),
    (4, 9, 10),
    (9, 11, 15),
    (9, 14, 17),
    (10, 14, 15),
    (10, 16, 17),
    (11, 12, 17),
    (11, 14, 16),
    (12, 13, 14),
    (12, 15, 16),
    (13, 15, 17)]

def canonical_sparse_9_9_3_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_3_4_triples

theorem canonical_sparse_9_9_3_4_verified : Packing canonical_sparse_9_9_3_4_profile.graph canonical_sparse_9_9_3_4_triangles ∧
    canonical_sparse_9_9_3_4_triangles.card = 28 := by
  have h := labeledPacking_correct canonical_sparse_9_9_3_4_profile canonical_sparse_9_9_3_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_4_1_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 5, 5, 1, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_4_1_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 4),
    (0, 2, 13),
    (0, 3, 8),
    (0, 5, 6),
    (0, 9, 12),
    (0, 10, 11),
    (1, 2, 12),
    (1, 3, 5),
    (1, 6, 8),
    (1, 9, 13),
    (2, 3, 11),
    (2, 4, 6),
    (2, 5, 8),
    (2, 9, 10),
    (3, 4, 9),
    (3, 6, 7),
    (3, 10, 13),
    (4, 7, 8),
    (9, 14, 16),
    (9, 15, 17),
    (10, 12, 14),
    (10, 16, 17),
    (11, 12, 17),
    (11, 13, 16),
    (11, 14, 15),
    (12, 15, 16),
    (13, 14, 17)]

def canonical_sparse_9_9_4_1_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_4_1_triples

theorem canonical_sparse_9_9_4_1_verified : Packing canonical_sparse_9_9_4_1_profile.graph canonical_sparse_9_9_4_1_triangles ∧
    canonical_sparse_9_9_4_1_triangles.card = 27 := by
  have h := labeledPacking_correct canonical_sparse_9_9_4_1_profile canonical_sparse_9_9_4_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_4_2_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 5, 5, 2, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_4_2_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 3),
    (0, 2, 5),
    (0, 4, 7),
    (0, 6, 8),
    (0, 9, 10),
    (1, 2, 6),
    (1, 4, 8),
    (1, 5, 7),
    (1, 10, 11),
    (1, 12, 13),
    (2, 3, 11),
    (2, 4, 9),
    (2, 7, 8),
    (3, 5, 8),
    (3, 6, 7),
    (3, 9, 13),
    (3, 10, 12),
    (4, 5, 6),
    (9, 11, 14),
    (9, 12, 15),
    (10, 13, 14),
    (10, 15, 17),
    (11, 12, 16),
    (11, 13, 15),
    (12, 14, 17),
    (13, 16, 17),
    (14, 15, 16)]

def canonical_sparse_9_9_4_2_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_4_2_triples

theorem canonical_sparse_9_9_4_2_verified : Packing canonical_sparse_9_9_4_2_profile.graph canonical_sparse_9_9_4_2_triangles ∧
    canonical_sparse_9_9_4_2_triangles.card = 27 := by
  have h := labeledPacking_correct canonical_sparse_9_9_4_2_profile canonical_sparse_9_9_4_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_4_3_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 5, 5, 3, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_4_3_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 7),
    (0, 2, 11),
    (0, 3, 10),
    (0, 4, 9),
    (0, 5, 8),
    (0, 12, 13),
    (1, 2, 9),
    (1, 3, 13),
    (1, 4, 11),
    (1, 6, 8),
    (1, 10, 12),
    (2, 3, 5),
    (2, 4, 8),
    (2, 6, 7),
    (2, 10, 13),
    (3, 4, 6),
    (3, 7, 8),
    (3, 9, 12),
    (4, 5, 7),
    (9, 10, 17),
    (9, 14, 15),
    (10, 11, 14),
    (10, 15, 16),
    (11, 13, 15),
    (11, 16, 17),
    (12, 14, 16),
    (12, 15, 17),
    (13, 14, 17)]

def canonical_sparse_9_9_4_3_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_4_3_triples

theorem canonical_sparse_9_9_4_3_verified : Packing canonical_sparse_9_9_4_3_profile.graph canonical_sparse_9_9_4_3_triangles ∧
    canonical_sparse_9_9_4_3_triangles.card = 28 := by
  have h := labeledPacking_correct canonical_sparse_9_9_4_3_profile canonical_sparse_9_9_4_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_9_4_4_profile : FerrersProfile 9 9 where
  degree := ![5, 5, 5, 5, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_9_4_4_triples : List (Fin (9 + 9) × Fin (9 + 9) × Fin (9 + 9)) :=
  [
    (0, 1, 12),
    (0, 2, 7),
    (0, 3, 10),
    (0, 4, 8),
    (0, 5, 6),
    (0, 9, 13),
    (1, 2, 5),
    (1, 3, 11),
    (1, 4, 6),
    (1, 7, 8),
    (1, 10, 13),
    (2, 3, 13),
    (2, 6, 8),
    (2, 9, 10),
    (2, 11, 12),
    (3, 4, 9),
    (3, 5, 8),
    (3, 6, 7),
    (4, 5, 7),
    (4, 10, 11),
    (9, 12, 16),
    (9, 15, 17),
    (10, 12, 14),
    (10, 16, 17),
    (11, 13, 15),
    (11, 14, 17),
    (12, 13, 17),
    (13, 14, 16)]

def canonical_sparse_9_9_4_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 9)) :=
  labeledPacking 9 9 canonical_sparse_9_9_4_4_triples

theorem canonical_sparse_9_9_4_4_verified : Packing canonical_sparse_9_9_4_4_profile.graph canonical_sparse_9_9_4_4_triangles ∧
    canonical_sparse_9_9_4_4_triangles.card = 28 := by
  have h := labeledPacking_correct canonical_sparse_9_9_4_4_profile canonical_sparse_9_9_4_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_11_1_4_profile : FerrersProfile 9 11 where
  degree := ![6, 4, 4, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_11_1_4_triples : List (Fin (9 + 11) × Fin (9 + 11) × Fin (9 + 11)) :=
  [
    (0, 1, 10),
    (0, 3, 8),
    (0, 4, 7),
    (0, 5, 6),
    (0, 9, 14),
    (0, 11, 13),
    (1, 2, 11),
    (1, 3, 4),
    (1, 5, 8),
    (1, 6, 7),
    (2, 3, 6),
    (2, 4, 5),
    (2, 7, 8),
    (2, 9, 12),
    (3, 5, 7),
    (3, 9, 10),
    (3, 11, 12),
    (4, 6, 8),
    (4, 9, 11),
    (4, 10, 12),
    (9, 13, 19),
    (9, 16, 17),
    (10, 11, 14),
    (10, 13, 18),
    (10, 15, 19),
    (11, 16, 18),
    (12, 13, 17),
    (12, 14, 18),
    (12, 16, 19),
    (13, 14, 16),
    (14, 17, 19),
    (15, 17, 18)]

def canonical_sparse_9_11_1_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 11)) :=
  labeledPacking 9 11 canonical_sparse_9_11_1_4_triples

theorem canonical_sparse_9_11_1_4_verified : Packing canonical_sparse_9_11_1_4_profile.graph canonical_sparse_9_11_1_4_triangles ∧
    canonical_sparse_9_11_1_4_triangles.card = 32 := by
  have h := labeledPacking_correct canonical_sparse_9_11_1_4_profile canonical_sparse_9_11_1_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_11_2_4_profile : FerrersProfile 9 11 where
  degree := ![6, 6, 4, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_11_2_4_triples : List (Fin (9 + 11) × Fin (9 + 11) × Fin (9 + 11)) :=
  [
    (0, 1, 6),
    (0, 2, 7),
    (0, 3, 4),
    (0, 5, 8),
    (0, 9, 13),
    (0, 10, 11),
    (0, 12, 14),
    (1, 2, 10),
    (1, 4, 5),
    (1, 7, 8),
    (1, 11, 14),
    (1, 12, 13),
    (2, 3, 9),
    (2, 4, 8),
    (2, 5, 6),
    (3, 5, 7),
    (3, 6, 8),
    (4, 6, 7),
    (4, 9, 10),
    (9, 11, 17),
    (9, 12, 18),
    (9, 14, 15),
    (9, 16, 19),
    (10, 12, 16),
    (10, 13, 19),
    (10, 14, 17),
    (10, 15, 18),
    (11, 12, 15),
    (11, 13, 16),
    (11, 18, 19),
    (12, 17, 19),
    (13, 14, 18),
    (16, 17, 18)]

def canonical_sparse_9_11_2_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 11)) :=
  labeledPacking 9 11 canonical_sparse_9_11_2_4_triples

theorem canonical_sparse_9_11_2_4_verified : Packing canonical_sparse_9_11_2_4_profile.graph canonical_sparse_9_11_2_4_triangles ∧
    canonical_sparse_9_11_2_4_triangles.card = 33 := by
  have h := labeledPacking_correct canonical_sparse_9_11_2_4_profile canonical_sparse_9_11_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_11_3_4_profile : FerrersProfile 9 11 where
  degree := ![6, 6, 6, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_11_3_4_triples : List (Fin (9 + 11) × Fin (9 + 11) × Fin (9 + 11)) :=
  [
    (0, 1, 12),
    (0, 3, 5),
    (0, 4, 8),
    (0, 6, 7),
    (0, 9, 10),
    (0, 11, 14),
    (1, 3, 7),
    (1, 4, 6),
    (1, 5, 8),
    (1, 9, 11),
    (1, 10, 13),
    (2, 3, 9),
    (2, 4, 10),
    (2, 5, 6),
    (2, 7, 8),
    (2, 12, 14),
    (3, 4, 11),
    (3, 6, 8),
    (4, 5, 7),
    (4, 9, 12),
    (9, 13, 16),
    (9, 14, 18),
    (9, 15, 19),
    (10, 11, 19),
    (10, 14, 17),
    (10, 15, 18),
    (11, 12, 13),
    (11, 15, 17),
    (12, 15, 16),
    (12, 18, 19),
    (13, 14, 15),
    (13, 17, 19),
    (14, 16, 19),
    (16, 17, 18)]

def canonical_sparse_9_11_3_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 11)) :=
  labeledPacking 9 11 canonical_sparse_9_11_3_4_triples

theorem canonical_sparse_9_11_3_4_verified : Packing canonical_sparse_9_11_3_4_profile.graph canonical_sparse_9_11_3_4_triangles ∧
    canonical_sparse_9_11_3_4_triangles.card = 34 := by
  have h := labeledPacking_correct canonical_sparse_9_11_3_4_profile canonical_sparse_9_11_3_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_13_3_4_profile : FerrersProfile 9 13 where
  degree := ![7, 7, 7, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_13_3_4_triples : List (Fin (9 + 13) × Fin (9 + 13) × Fin (9 + 13)) :=
  [
    (0, 1, 13),
    (0, 2, 10),
    (0, 3, 7),
    (0, 4, 6),
    (0, 5, 8),
    (0, 9, 14),
    (0, 12, 15),
    (1, 3, 5),
    (1, 4, 8),
    (1, 6, 7),
    (1, 9, 11),
    (1, 10, 15),
    (2, 3, 11),
    (2, 4, 9),
    (2, 5, 6),
    (2, 7, 8),
    (2, 12, 13),
    (3, 4, 12),
    (3, 6, 8),
    (4, 5, 7),
    (4, 10, 11),
    (9, 10, 19),
    (9, 12, 18),
    (9, 15, 16),
    (9, 17, 21),
    (10, 12, 17),
    (10, 13, 16),
    (10, 18, 20),
    (11, 12, 16),
    (11, 14, 17),
    (11, 15, 21),
    (11, 18, 19),
    (12, 19, 20),
    (13, 15, 20),
    (13, 17, 19),
    (13, 18, 21),
    (14, 15, 19),
    (14, 16, 18),
    (14, 20, 21),
    (15, 17, 18),
    (16, 17, 20)]

def canonical_sparse_9_13_3_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 13)) :=
  labeledPacking 9 13 canonical_sparse_9_13_3_4_triples

theorem canonical_sparse_9_13_3_4_verified : Packing canonical_sparse_9_13_3_4_profile.graph canonical_sparse_9_13_3_4_triangles ∧
    canonical_sparse_9_13_3_4_triangles.card = 41 := by
  have h := labeledPacking_correct canonical_sparse_9_13_3_4_profile canonical_sparse_9_13_3_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_9_13_4_5_profile : FerrersProfile 9 13 where
  degree := ![7, 7, 7, 7, 5, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_9_13_4_5_triples : List (Fin (9 + 13) × Fin (9 + 13) × Fin (9 + 13)) :=
  [
    (0, 1, 9),
    (0, 2, 8),
    (0, 3, 12),
    (0, 4, 10),
    (0, 5, 6),
    (0, 11, 13),
    (0, 14, 15),
    (1, 2, 6),
    (1, 3, 8),
    (1, 4, 13),
    (1, 10, 15),
    (1, 12, 14),
    (2, 4, 12),
    (2, 9, 10),
    (2, 11, 15),
    (2, 13, 14),
    (3, 4, 6),
    (3, 5, 7),
    (3, 9, 15),
    (3, 10, 13),
    (3, 11, 14),
    (4, 5, 8),
    (4, 9, 11),
    (6, 7, 8),
    (9, 13, 19),
    (9, 14, 17),
    (9, 16, 21),
    (9, 18, 20),
    (10, 12, 18),
    (10, 14, 19),
    (10, 16, 17),
    (10, 20, 21),
    (11, 12, 21),
    (11, 16, 19),
    (12, 13, 16),
    (12, 15, 17),
    (13, 15, 20),
    (13, 17, 21),
    (14, 16, 20),
    (14, 18, 21),
    (15, 16, 18),
    (15, 19, 21),
    (17, 19, 20)]

def canonical_sparse_9_13_4_5_triangles : Finset (Finset (Fin 9 ⊕ Fin 13)) :=
  labeledPacking 9 13 canonical_sparse_9_13_4_5_triples

theorem canonical_sparse_9_13_4_5_verified : Packing canonical_sparse_9_13_4_5_profile.graph canonical_sparse_9_13_4_5_triangles ∧
    canonical_sparse_9_13_4_5_triangles.card = 43 := by
  have h := labeledPacking_correct canonical_sparse_9_13_4_5_profile canonical_sparse_9_13_4_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_10_11_3_4_profile : FerrersProfile 10 11 where
  degree := ![6, 6, 6, 4, 4, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_10_11_3_4_triples : List (Fin (10 + 11) × Fin (10 + 11) × Fin (10 + 11)) :=
  [
    (0, 1, 5),
    (0, 2, 13),
    (0, 3, 4),
    (0, 6, 8),
    (0, 7, 9),
    (0, 10, 12),
    (0, 11, 14),
    (1, 2, 14),
    (1, 3, 9),
    (1, 4, 13),
    (1, 7, 8),
    (1, 11, 12),
    (2, 3, 10),
    (2, 4, 12),
    (2, 5, 6),
    (2, 8, 9),
    (2, 11, 15),
    (3, 5, 8),
    (3, 6, 7),
    (4, 5, 7),
    (4, 6, 9),
    (10, 11, 18),
    (10, 13, 15),
    (10, 14, 20),
    (10, 16, 19),
    (11, 13, 20),
    (11, 16, 17),
    (12, 13, 16),
    (12, 14, 19),
    (12, 15, 18),
    (12, 17, 20),
    (13, 14, 18),
    (14, 15, 17),
    (15, 19, 20),
    (16, 18, 20),
    (17, 18, 19)]

def canonical_sparse_10_11_3_4_triangles : Finset (Finset (Fin 10 ⊕ Fin 11)) :=
  labeledPacking 10 11 canonical_sparse_10_11_3_4_triples

theorem canonical_sparse_10_11_3_4_verified : Packing canonical_sparse_10_11_3_4_profile.graph canonical_sparse_10_11_3_4_triangles ∧
    canonical_sparse_10_11_3_4_triangles.card = 36 := by
  have h := labeledPacking_correct canonical_sparse_10_11_3_4_profile canonical_sparse_10_11_3_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_11_11_3_3_profile : FerrersProfile 11 11 where
  degree := ![6, 6, 6, 3, 3, 3, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_11_11_3_3_triples : List (Fin (11 + 11) × Fin (11 + 11) × Fin (11 + 11)) :=
  [
    (0, 1, 6),
    (0, 2, 14),
    (0, 3, 9),
    (0, 4, 7),
    (0, 5, 12),
    (0, 8, 10),
    (0, 11, 15),
    (0, 13, 16),
    (1, 2, 7),
    (1, 4, 8),
    (1, 5, 10),
    (1, 11, 13),
    (1, 12, 15),
    (1, 14, 16),
    (2, 4, 11),
    (2, 5, 9),
    (2, 6, 10),
    (2, 12, 13),
    (2, 15, 16),
    (3, 4, 12),
    (3, 5, 11),
    (3, 6, 8),
    (3, 7, 10),
    (4, 5, 6),
    (4, 9, 10),
    (5, 7, 8),
    (6, 7, 9),
    (11, 16, 19),
    (11, 17, 18),
    (11, 20, 21),
    (12, 16, 21),
    (12, 17, 19),
    (12, 18, 20),
    (13, 14, 19),
    (13, 15, 17),
    (13, 18, 21),
    (14, 15, 20),
    (14, 17, 21),
    (15, 18, 19)]

def canonical_sparse_11_11_3_3_triangles : Finset (Finset (Fin 11 ⊕ Fin 11)) :=
  labeledPacking 11 11 canonical_sparse_11_11_3_3_triples

theorem canonical_sparse_11_11_3_3_verified : Packing canonical_sparse_11_11_3_3_profile.graph canonical_sparse_11_11_3_3_triangles ∧
    canonical_sparse_11_11_3_3_triangles.card = 39 := by
  have h := labeledPacking_correct canonical_sparse_11_11_3_3_profile canonical_sparse_11_11_3_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_11_11_4_4_profile : FerrersProfile 11 11 where
  degree := ![6, 6, 6, 6, 4, 4, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_11_11_4_4_triples : List (Fin (11 + 11) × Fin (11 + 11) × Fin (11 + 11)) :=
  [
    (0, 1, 8),
    (0, 2, 11),
    (0, 3, 15),
    (0, 4, 14),
    (0, 6, 10),
    (0, 7, 9),
    (0, 13, 16),
    (1, 2, 16),
    (1, 3, 13),
    (1, 4, 12),
    (1, 6, 7),
    (1, 9, 10),
    (1, 11, 15),
    (2, 3, 14),
    (2, 4, 10),
    (2, 5, 9),
    (2, 7, 8),
    (2, 13, 15),
    (3, 4, 6),
    (3, 5, 12),
    (3, 8, 10),
    (4, 5, 11),
    (4, 8, 9),
    (5, 6, 8),
    (5, 7, 10),
    (5, 13, 14),
    (11, 12, 18),
    (11, 13, 20),
    (11, 14, 19),
    (11, 16, 17),
    (12, 13, 17),
    (12, 14, 15),
    (12, 16, 21),
    (12, 19, 20),
    (13, 18, 21),
    (14, 16, 20),
    (14, 17, 18),
    (15, 17, 19),
    (15, 18, 20),
    (16, 18, 19),
    (17, 20, 21)]

def canonical_sparse_11_11_4_4_triangles : Finset (Finset (Fin 11 ⊕ Fin 11)) :=
  labeledPacking 11 11 canonical_sparse_11_11_4_4_triples

theorem canonical_sparse_11_11_4_4_verified : Packing canonical_sparse_11_11_4_4_profile.graph canonical_sparse_11_11_4_4_triangles ∧
    canonical_sparse_11_11_4_4_triangles.card = 41 := by
  have h := labeledPacking_correct canonical_sparse_11_11_4_4_profile canonical_sparse_11_11_4_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_11_11_5_5_profile : FerrersProfile 11 11 where
  degree := ![6, 6, 6, 6, 6, 5, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_11_11_5_5_triples : List (Fin (11 + 11) × Fin (11 + 11) × Fin (11 + 11)) :=
  [
    (0, 1, 8),
    (0, 2, 9),
    (0, 3, 4),
    (0, 5, 12),
    (0, 6, 7),
    (0, 11, 13),
    (0, 14, 15),
    (1, 2, 6),
    (1, 3, 13),
    (1, 4, 7),
    (1, 5, 11),
    (1, 9, 10),
    (1, 12, 14),
    (2, 3, 15),
    (2, 4, 11),
    (2, 5, 7),
    (2, 8, 10),
    (2, 12, 13),
    (2, 14, 16),
    (3, 5, 8),
    (3, 6, 9),
    (3, 7, 10),
    (3, 11, 12),
    (4, 5, 9),
    (4, 6, 8),
    (4, 12, 15),
    (4, 13, 16),
    (5, 6, 10),
    (7, 8, 9),
    (11, 14, 18),
    (11, 17, 21),
    (11, 19, 20),
    (12, 16, 19),
    (12, 17, 20),
    (12, 18, 21),
    (13, 14, 20),
    (13, 15, 21),
    (13, 18, 19),
    (14, 19, 21),
    (15, 17, 19),
    (15, 18, 20),
    (16, 17, 18),
    (16, 20, 21)]

def canonical_sparse_11_11_5_5_triangles : Finset (Finset (Fin 11 ⊕ Fin 11)) :=
  labeledPacking 11 11 canonical_sparse_11_11_5_5_triples

theorem canonical_sparse_11_11_5_5_verified : Packing canonical_sparse_11_11_5_5_profile.graph canonical_sparse_11_11_5_5_triangles ∧
    canonical_sparse_11_11_5_5_triangles.card = 43 := by
  have h := labeledPacking_correct canonical_sparse_11_11_5_5_profile canonical_sparse_11_11_5_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_11_13_4_3_profile : FerrersProfile 11 13 where
  degree := ![7, 7, 7, 7, 3, 3, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_11_13_4_3_triples : List (Fin (11 + 13) × Fin (11 + 13) × Fin (11 + 13)) :=
  [
    (0, 1, 17),
    (0, 2, 6),
    (0, 3, 13),
    (0, 4, 8),
    (0, 5, 11),
    (0, 7, 9),
    (0, 12, 14),
    (1, 2, 7),
    (1, 4, 13),
    (1, 5, 6),
    (1, 9, 10),
    (1, 11, 14),
    (1, 12, 15),
    (2, 3, 16),
    (2, 4, 9),
    (2, 5, 13),
    (2, 8, 10),
    (3, 4, 11),
    (3, 6, 9),
    (3, 7, 10),
    (3, 12, 17),
    (3, 14, 15),
    (4, 5, 12),
    (4, 6, 10),
    (5, 8, 9),
    (6, 7, 8),
    (11, 13, 16),
    (11, 18, 22),
    (11, 19, 23),
    (11, 20, 21),
    (12, 13, 19),
    (12, 16, 20),
    (12, 18, 21),
    (12, 22, 23),
    (13, 14, 22),
    (13, 15, 20),
    (13, 17, 18),
    (13, 21, 23),
    (14, 16, 18),
    (14, 19, 21),
    (14, 20, 23),
    (15, 16, 23),
    (15, 17, 19),
    (15, 21, 22),
    (16, 17, 21),
    (16, 19, 22),
    (17, 20, 22),
    (18, 19, 20)]

def canonical_sparse_11_13_4_3_triangles : Finset (Finset (Fin 11 ⊕ Fin 13)) :=
  labeledPacking 11 13 canonical_sparse_11_13_4_3_triples

theorem canonical_sparse_11_13_4_3_verified : Packing canonical_sparse_11_13_4_3_profile.graph canonical_sparse_11_13_4_3_triangles ∧
    canonical_sparse_11_13_4_3_triangles.card = 48 := by
  have h := labeledPacking_correct canonical_sparse_11_13_4_3_profile canonical_sparse_11_13_4_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_11_16_4_6_profile : FerrersProfile 11 16 where
  degree := ![8, 8, 8, 8, 6, 6, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_11_16_4_6_triples : List (Fin (11 + 16) × Fin (11 + 16) × Fin (11 + 16)) :=
  [
    (0, 1, 2),
    (0, 3, 5),
    (0, 4, 13),
    (0, 6, 8),
    (0, 7, 10),
    (0, 11, 17),
    (0, 16, 18),
    (1, 3, 16),
    (1, 4, 8),
    (1, 5, 6),
    (1, 9, 10),
    (1, 11, 15),
    (1, 12, 13),
    (1, 17, 18),
    (2, 3, 18),
    (2, 4, 6),
    (2, 5, 7),
    (2, 8, 9),
    (2, 12, 16),
    (2, 13, 14),
    (2, 15, 17),
    (3, 4, 12),
    (3, 6, 10),
    (3, 7, 8),
    (3, 11, 13),
    (3, 14, 17),
    (4, 5, 9),
    (4, 14, 15),
    (5, 8, 10),
    (5, 11, 12),
    (6, 7, 9),
    (11, 14, 16),
    (11, 18, 25),
    (11, 19, 22),
    (11, 20, 21),
    (11, 24, 26),
    (12, 14, 24),
    (12, 15, 18),
    (12, 17, 19),
    (12, 20, 25),
    (12, 21, 23),
    (12, 22, 26),
    (13, 15, 20),
    (13, 16, 17),
    (13, 18, 19),
    (13, 21, 24),
    (13, 22, 25),
    (13, 23, 26),
    (14, 18, 21),
    (14, 19, 25),
    (14, 20, 22),
    (15, 16, 26),
    (15, 19, 21),
    (15, 24, 25),
    (16, 19, 23),
    (16, 21, 25),
    (16, 22, 24),
    (17, 21, 22),
    (17, 23, 24),
    (17, 25, 26),
    (18, 20, 24),
    (18, 22, 23),
    (19, 20, 26)]

def canonical_sparse_11_16_4_6_triangles : Finset (Finset (Fin 11 ⊕ Fin 16)) :=
  labeledPacking 11 16 canonical_sparse_11_16_4_6_triples

theorem canonical_sparse_11_16_4_6_verified : Packing canonical_sparse_11_16_4_6_profile.graph canonical_sparse_11_16_4_6_triangles ∧
    canonical_sparse_11_16_4_6_triangles.card = 63 := by
  have h := labeledPacking_correct canonical_sparse_11_16_4_6_profile canonical_sparse_11_16_4_6_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_13_13_5_6_profile : FerrersProfile 13 13 where
  degree := ![7, 7, 7, 7, 7, 6, 6, 0, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_13_13_5_6_triples : List (Fin (13 + 13) × Fin (13 + 13) × Fin (13 + 13)) :=
  [
    (0, 2, 13),
    (0, 3, 7),
    (0, 4, 17),
    (0, 5, 8),
    (0, 6, 12),
    (0, 9, 11),
    (0, 14, 18),
    (0, 16, 19),
    (1, 2, 17),
    (1, 3, 16),
    (1, 4, 19),
    (1, 6, 14),
    (1, 7, 12),
    (1, 8, 9),
    (1, 10, 11),
    (1, 15, 18),
    (2, 3, 10),
    (2, 4, 18),
    (2, 5, 16),
    (2, 6, 15),
    (2, 7, 8),
    (2, 9, 12),
    (2, 14, 19),
    (3, 4, 13),
    (3, 5, 14),
    (3, 6, 8),
    (3, 11, 12),
    (3, 15, 19),
    (3, 17, 18),
    (4, 6, 16),
    (4, 7, 11),
    (4, 9, 10),
    (4, 14, 15),
    (5, 6, 11),
    (5, 7, 10),
    (5, 13, 15),
    (6, 7, 9),
    (6, 13, 17),
    (8, 10, 12),
    (13, 14, 22),
    (13, 16, 24),
    (13, 18, 23),
    (13, 19, 25),
    (13, 20, 21),
    (14, 16, 23),
    (14, 17, 25),
    (14, 21, 24),
    (15, 16, 21),
    (15, 20, 22),
    (15, 23, 24),
    (16, 17, 20),
    (16, 18, 22),
    (17, 21, 23),
    (17, 22, 24),
    (18, 19, 24),
    (18, 21, 25),
    (19, 20, 23),
    (19, 21, 22),
    (20, 24, 25),
    (22, 23, 25)]

def canonical_sparse_13_13_5_6_triangles : Finset (Finset (Fin 13 ⊕ Fin 13)) :=
  labeledPacking 13 13 canonical_sparse_13_13_5_6_triples

theorem canonical_sparse_13_13_5_6_verified : Packing canonical_sparse_13_13_5_6_profile.graph canonical_sparse_13_13_5_6_triangles ∧
    canonical_sparse_13_13_5_6_triangles.card = 60 := by
  have h := labeledPacking_correct canonical_sparse_13_13_5_6_profile canonical_sparse_13_13_5_6_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_13_13_6_5_profile : FerrersProfile 13 13 where
  degree := ![7, 7, 7, 7, 7, 7, 5, 0, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_13_13_6_5_triples : List (Fin (13 + 13) × Fin (13 + 13) × Fin (13 + 13)) :=
  [
    (0, 1, 15),
    (0, 2, 3),
    (0, 4, 10),
    (0, 5, 19),
    (0, 6, 9),
    (0, 7, 11),
    (0, 13, 16),
    (0, 14, 18),
    (1, 2, 5),
    (1, 3, 16),
    (1, 4, 18),
    (1, 6, 7),
    (1, 8, 11),
    (1, 9, 10),
    (1, 17, 19),
    (2, 4, 6),
    (2, 7, 10),
    (2, 8, 9),
    (2, 11, 12),
    (2, 13, 17),
    (2, 14, 19),
    (2, 16, 18),
    (3, 4, 15),
    (3, 5, 6),
    (3, 7, 8),
    (3, 9, 12),
    (3, 10, 11),
    (3, 13, 19),
    (4, 5, 13),
    (4, 7, 9),
    (4, 8, 12),
    (4, 14, 17),
    (5, 7, 12),
    (5, 8, 10),
    (5, 9, 11),
    (5, 16, 17),
    (6, 10, 12),
    (6, 13, 15),
    (6, 14, 16),
    (13, 14, 25),
    (13, 18, 22),
    (13, 20, 24),
    (13, 21, 23),
    (14, 15, 20),
    (14, 21, 22),
    (14, 23, 24),
    (15, 16, 19),
    (15, 17, 18),
    (15, 22, 23),
    (15, 24, 25),
    (16, 20, 25),
    (16, 22, 24),
    (17, 20, 22),
    (17, 21, 24),
    (17, 23, 25),
    (18, 19, 24),
    (18, 20, 23),
    (18, 21, 25),
    (19, 20, 21),
    (19, 22, 25)]

def canonical_sparse_13_13_6_5_triangles : Finset (Finset (Fin 13 ⊕ Fin 13)) :=
  labeledPacking 13 13 canonical_sparse_13_13_6_5_triples

theorem canonical_sparse_13_13_6_5_verified : Packing canonical_sparse_13_13_6_5_profile.graph canonical_sparse_13_13_6_5_triangles ∧
    canonical_sparse_13_13_6_5_triangles.card = 60 := by
  have h := labeledPacking_correct canonical_sparse_13_13_6_5_profile canonical_sparse_13_13_6_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_13_13_6_6_profile : FerrersProfile 13 13 where
  degree := ![7, 7, 7, 7, 7, 7, 6, 0, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_13_13_6_6_triples : List (Fin (13 + 13) × Fin (13 + 13) × Fin (13 + 13)) :=
  [
    (0, 1, 16),
    (0, 3, 9),
    (0, 4, 7),
    (0, 5, 18),
    (0, 6, 8),
    (0, 10, 12),
    (0, 13, 14),
    (0, 15, 19),
    (1, 2, 6),
    (1, 3, 13),
    (1, 4, 12),
    (1, 5, 14),
    (1, 8, 10),
    (1, 9, 11),
    (1, 15, 17),
    (1, 18, 19),
    (2, 3, 18),
    (2, 4, 9),
    (2, 5, 8),
    (2, 7, 10),
    (2, 11, 12),
    (2, 14, 15),
    (2, 17, 19),
    (3, 4, 19),
    (3, 5, 15),
    (3, 6, 14),
    (3, 7, 11),
    (3, 8, 12),
    (3, 16, 17),
    (4, 5, 16),
    (4, 6, 15),
    (4, 8, 11),
    (4, 14, 18),
    (5, 6, 17),
    (5, 9, 12),
    (5, 10, 11),
    (6, 7, 12),
    (6, 9, 10),
    (6, 13, 16),
    (7, 8, 9),
    (13, 15, 23),
    (13, 17, 24),
    (13, 18, 22),
    (13, 19, 25),
    (13, 20, 21),
    (14, 16, 23),
    (14, 19, 20),
    (14, 21, 24),
    (14, 22, 25),
    (15, 16, 25),
    (15, 18, 24),
    (15, 21, 22),
    (16, 18, 20),
    (16, 19, 21),
    (16, 22, 24),
    (17, 20, 22),
    (17, 21, 25),
    (18, 21, 23),
    (19, 23, 24),
    (20, 23, 25)]

def canonical_sparse_13_13_6_6_triangles : Finset (Finset (Fin 13 ⊕ Fin 13)) :=
  labeledPacking 13 13 canonical_sparse_13_13_6_6_triples

theorem canonical_sparse_13_13_6_6_verified : Packing canonical_sparse_13_13_6_6_profile.graph canonical_sparse_13_13_6_6_triangles ∧
    canonical_sparse_13_13_6_6_triangles.card = 60 := by
  have h := labeledPacking_correct canonical_sparse_13_13_6_6_profile canonical_sparse_13_13_6_6_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_13_17_5_6_profile : FerrersProfile 13 17 where
  degree := ![9, 9, 9, 9, 9, 6, 6, 0, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_13_17_5_6_triples : List (Fin (13 + 17) × Fin (13 + 17) × Fin (13 + 17)) :=
  [
    (0, 1, 3),
    (0, 2, 16),
    (0, 4, 6),
    (0, 5, 18),
    (0, 7, 10),
    (0, 8, 12),
    (0, 9, 11),
    (0, 13, 17),
    (0, 15, 21),
    (1, 2, 6),
    (1, 4, 7),
    (1, 5, 13),
    (1, 8, 9),
    (1, 10, 11),
    (1, 14, 15),
    (1, 17, 20),
    (1, 18, 19),
    (2, 3, 15),
    (2, 4, 5),
    (2, 7, 11),
    (2, 8, 10),
    (2, 9, 12),
    (2, 13, 21),
    (2, 17, 18),
    (3, 4, 8),
    (3, 5, 10),
    (3, 6, 9),
    (3, 7, 12),
    (3, 13, 19),
    (3, 16, 18),
    (3, 20, 21),
    (4, 9, 10),
    (4, 11, 12),
    (4, 15, 18),
    (4, 16, 19),
    (5, 6, 16),
    (5, 7, 9),
    (5, 8, 11),
    (6, 7, 8),
    (6, 10, 12),
    (6, 13, 18),
    (13, 14, 29),
    (13, 15, 16),
    (13, 20, 24),
    (13, 22, 25),
    (13, 23, 27),
    (13, 26, 28),
    (14, 16, 20),
    (14, 17, 22),
    (14, 18, 23),
    (14, 19, 21),
    (14, 24, 26),
    (14, 25, 27),
    (15, 17, 28),
    (15, 19, 20),
    (15, 23, 25),
    (15, 24, 27),
    (15, 26, 29),
    (16, 17, 24),
    (16, 21, 23),
    (16, 22, 27),
    (16, 25, 29),
    (17, 19, 27),
    (17, 21, 25),
    (17, 23, 29),
    (18, 20, 22),
    (18, 21, 26),
    (18, 24, 25),
    (18, 28, 29),
    (19, 22, 29),
    (19, 23, 24),
    (19, 25, 28),
    (20, 23, 28),
    (20, 25, 26),
    (20, 27, 29),
    (21, 24, 29),
    (21, 27, 28),
    (22, 23, 26),
    (22, 24, 28)]

def canonical_sparse_13_17_5_6_triangles : Finset (Finset (Fin 13 ⊕ Fin 17)) :=
  labeledPacking 13 17 canonical_sparse_13_17_5_6_triples

theorem canonical_sparse_13_17_5_6_verified : Packing canonical_sparse_13_17_5_6_profile.graph canonical_sparse_13_17_5_6_triangles ∧
    canonical_sparse_13_17_5_6_triangles.card = 79 := by
  have h := labeledPacking_correct canonical_sparse_13_17_5_6_profile canonical_sparse_13_17_5_6_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

def canonical_sparse_17_17_5_5_profile : FerrersProfile 17 17 where
  degree := ![9, 9, 9, 9, 9, 5, 5, 5, 5, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def canonical_sparse_17_17_5_5_triples : List (Fin (17 + 17) × Fin (17 + 17) × Fin (17 + 17)) :=
  [
    (0, 1, 8),
    (0, 2, 22),
    (0, 3, 10),
    (0, 4, 9),
    (0, 5, 16),
    (0, 6, 7),
    (0, 11, 14),
    (0, 12, 15),
    (0, 17, 18),
    (0, 19, 25),
    (0, 20, 21),
    (1, 2, 18),
    (1, 3, 5),
    (1, 4, 25),
    (1, 6, 17),
    (1, 7, 12),
    (1, 9, 15),
    (1, 11, 13),
    (1, 19, 24),
    (2, 3, 23),
    (2, 4, 15),
    (2, 5, 14),
    (2, 6, 10),
    (2, 7, 16),
    (2, 8, 13),
    (2, 9, 12),
    (2, 19, 21),
    (3, 4, 22),
    (3, 6, 19),
    (3, 7, 13),
    (3, 8, 9),
    (3, 12, 14),
    (3, 15, 16),
    (3, 17, 21),
    (3, 18, 25),
    (3, 20, 24),
    (4, 5, 6),
    (4, 7, 14),
    (4, 8, 17),
    (4, 10, 11),
    (4, 12, 16),
    (4, 18, 24),
    (5, 7, 10),
    (5, 8, 12),
    (5, 9, 13),
    (5, 11, 15),
    (6, 8, 14),
    (6, 11, 12),
    (6, 13, 16),
    (6, 18, 20),
    (7, 8, 15),
    (7, 9, 11),
    (7, 17, 20),
    (7, 18, 21),
    (8, 11, 16),
    (8, 19, 20),
    (10, 12, 13),
    (10, 14, 16),
    (13, 14, 15),
    (17, 19, 22),
    (17, 23, 30),
    (17, 24, 31),
    (17, 25, 28),
    (17, 26, 29),
    (17, 27, 33),
    (18, 19, 30),
    (18, 22, 33),
    (18, 23, 26),
    (18, 28, 31),
    (18, 29, 32),
    (19, 23, 28),
    (19, 26, 27),
    (19, 29, 31),
    (19, 32, 33),
    (20, 22, 29),
    (20, 23, 33),
    (20, 25, 31),
    (20, 26, 32),
    (20, 27, 28),
    (21, 22, 25),
    (21, 23, 29),
    (21, 24, 32),
    (21, 26, 28),
    (21, 27, 31),
    (21, 30, 33),
    (22, 23, 24),
    (22, 27, 32),
    (22, 30, 31),
    (23, 25, 27),
    (23, 31, 32),
    (24, 25, 33),
    (24, 26, 30),
    (24, 27, 29),
    (25, 29, 30),
    (26, 31, 33),
    (28, 29, 33),
    (28, 30, 32)]

def canonical_sparse_17_17_5_5_triangles : Finset (Finset (Fin 17 ⊕ Fin 17)) :=
  labeledPacking 17 17 canonical_sparse_17_17_5_5_triples

theorem canonical_sparse_17_17_5_5_verified : Packing canonical_sparse_17_17_5_5_profile.graph canonical_sparse_17_17_5_5_triangles ∧
    canonical_sparse_17_17_5_5_triangles.card = 97 := by
  have h := labeledPacking_correct canonical_sparse_17_17_5_5_profile canonical_sparse_17_17_5_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

end ResearchMain.Tuza.Certificates
