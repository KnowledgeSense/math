import MainTheorems.Tuza.Certificates.Basic

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ResearchMain.Tuza.Certificates

def sparse_5_8_1_3_profile : FerrersProfile 5 8 where
  degree := ![4, 3, 3, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_5_8_1_3_triples : List (Fin (5 + 8) × Fin (5 + 8) × Fin (5 + 8)) :=
  [
    (0, 1, 5),
    (0, 2, 3),
    (0, 7, 8),
    (1, 2, 6),
    (1, 3, 4),
    (2, 5, 7),
    (5, 6, 12),
    (5, 8, 10),
    (5, 9, 11),
    (6, 10, 11),
    (7, 9, 10),
    (7, 11, 12),
    (8, 9, 12)]

def sparse_5_8_1_3_triangles : Finset (Finset (Fin 5 ⊕ Fin 8)) :=
  labeledPacking 5 8 sparse_5_8_1_3_triples

theorem sparse_5_8_1_3_verified : Packing sparse_5_8_1_3_profile.graph sparse_5_8_1_3_triangles ∧
    sparse_5_8_1_3_triangles.card = 13 := by
  have h := labeledPacking_correct sparse_5_8_1_3_profile sparse_5_8_1_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_5_8_1_3_packing : Packing sparse_5_8_1_3_profile.graph sparse_5_8_1_3_triangles :=
  sparse_5_8_1_3_verified.1

theorem sparse_5_8_1_3_card : sparse_5_8_1_3_triangles.card = 13 :=
  sparse_5_8_1_3_verified.2

def sparse_5_8_2_2_profile : FerrersProfile 5 8 where
  degree := ![4, 4, 2, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_5_8_2_2_triples : List (Fin (5 + 8) × Fin (5 + 8) × Fin (5 + 8)) :=
  [
    (0, 1, 3),
    (0, 2, 5),
    (1, 5, 6),
    (1, 7, 8),
    (2, 3, 4),
    (5, 7, 11),
    (5, 8, 9),
    (5, 10, 12),
    (6, 7, 12),
    (6, 8, 10),
    (6, 9, 11),
    (7, 9, 10),
    (8, 11, 12)]

def sparse_5_8_2_2_triangles : Finset (Finset (Fin 5 ⊕ Fin 8)) :=
  labeledPacking 5 8 sparse_5_8_2_2_triples

theorem sparse_5_8_2_2_verified : Packing sparse_5_8_2_2_profile.graph sparse_5_8_2_2_triangles ∧
    sparse_5_8_2_2_triangles.card = 13 := by
  have h := labeledPacking_correct sparse_5_8_2_2_profile sparse_5_8_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_5_8_2_2_packing : Packing sparse_5_8_2_2_profile.graph sparse_5_8_2_2_triangles :=
  sparse_5_8_2_2_verified.1

theorem sparse_5_8_2_2_card : sparse_5_8_2_2_triangles.card = 13 :=
  sparse_5_8_2_2_verified.2

def sparse_5_12_0_5_profile : FerrersProfile 5 12 where
  degree := ![5, 5, 5, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_5_12_0_5_triples : List (Fin (5 + 12) × Fin (5 + 12) × Fin (5 + 12)) :=
  [
    (0, 1, 4),
    (0, 5, 6),
    (0, 7, 8),
    (1, 2, 9),
    (1, 5, 7),
    (1, 6, 8),
    (2, 3, 4),
    (2, 5, 8),
    (2, 6, 7),
    (5, 9, 14),
    (5, 10, 16),
    (5, 11, 12),
    (6, 9, 16),
    (6, 10, 14),
    (6, 13, 15),
    (7, 9, 12),
    (7, 10, 15),
    (7, 11, 14),
    (7, 13, 16),
    (8, 9, 13),
    (8, 10, 12),
    (8, 14, 15),
    (10, 11, 13),
    (11, 15, 16),
    (12, 13, 14)]

def sparse_5_12_0_5_triangles : Finset (Finset (Fin 5 ⊕ Fin 12)) :=
  labeledPacking 5 12 sparse_5_12_0_5_triples

theorem sparse_5_12_0_5_verified : Packing sparse_5_12_0_5_profile.graph sparse_5_12_0_5_triangles ∧
    sparse_5_12_0_5_triangles.card = 25 := by
  have h := labeledPacking_correct sparse_5_12_0_5_profile sparse_5_12_0_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_5_12_0_5_packing : Packing sparse_5_12_0_5_profile.graph sparse_5_12_0_5_triangles :=
  sparse_5_12_0_5_verified.1

theorem sparse_5_12_0_5_card : sparse_5_12_0_5_triangles.card = 25 :=
  sparse_5_12_0_5_verified.2

def sparse_5_12_1_5_profile : FerrersProfile 5 12 where
  degree := ![6, 5, 5, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_5_12_1_5_triples : List (Fin (5 + 12) × Fin (5 + 12) × Fin (5 + 12)) :=
  [
    (0, 1, 5),
    (0, 2, 7),
    (0, 8, 9),
    (1, 6, 8),
    (1, 7, 9),
    (2, 3, 4),
    (2, 5, 8),
    (5, 6, 10),
    (5, 7, 13),
    (5, 9, 15),
    (5, 11, 14),
    (5, 12, 16),
    (6, 7, 15),
    (6, 9, 11),
    (6, 12, 14),
    (6, 13, 16),
    (7, 8, 14),
    (7, 10, 16),
    (7, 11, 12),
    (8, 10, 13),
    (8, 15, 16),
    (9, 10, 12),
    (9, 14, 16),
    (10, 14, 15),
    (12, 13, 15)]

def sparse_5_12_1_5_triangles : Finset (Finset (Fin 5 ⊕ Fin 12)) :=
  labeledPacking 5 12 sparse_5_12_1_5_triples

theorem sparse_5_12_1_5_verified : Packing sparse_5_12_1_5_profile.graph sparse_5_12_1_5_triangles ∧
    sparse_5_12_1_5_triangles.card = 25 := by
  have h := labeledPacking_correct sparse_5_12_1_5_profile sparse_5_12_1_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_5_12_1_5_packing : Packing sparse_5_12_1_5_profile.graph sparse_5_12_1_5_triangles :=
  sparse_5_12_1_5_verified.1

theorem sparse_5_12_1_5_card : sparse_5_12_1_5_triangles.card = 25 :=
  sparse_5_12_1_5_verified.2

def sparse_5_12_2_5_profile : FerrersProfile 5 12 where
  degree := ![6, 6, 5, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_5_12_2_5_triples : List (Fin (5 + 12) × Fin (5 + 12) × Fin (5 + 12)) :=
  [
    (0, 1, 8),
    (0, 2, 6),
    (0, 5, 10),
    (0, 7, 9),
    (1, 5, 7),
    (1, 9, 10),
    (2, 3, 4),
    (2, 8, 9),
    (5, 6, 9),
    (5, 8, 14),
    (5, 11, 15),
    (5, 13, 16),
    (6, 7, 12),
    (6, 8, 16),
    (6, 10, 11),
    (6, 14, 15),
    (7, 8, 15),
    (7, 10, 16),
    (7, 13, 14),
    (8, 10, 13),
    (8, 11, 12),
    (9, 11, 14),
    (9, 12, 13),
    (9, 15, 16),
    (10, 12, 15),
    (12, 14, 16)]

def sparse_5_12_2_5_triangles : Finset (Finset (Fin 5 ⊕ Fin 12)) :=
  labeledPacking 5 12 sparse_5_12_2_5_triples

theorem sparse_5_12_2_5_verified : Packing sparse_5_12_2_5_profile.graph sparse_5_12_2_5_triangles ∧
    sparse_5_12_2_5_triangles.card = 26 := by
  have h := labeledPacking_correct sparse_5_12_2_5_profile sparse_5_12_2_5_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_5_12_2_5_packing : Packing sparse_5_12_2_5_profile.graph sparse_5_12_2_5_triangles :=
  sparse_5_12_2_5_verified.1

theorem sparse_5_12_2_5_card : sparse_5_12_2_5_triangles.card = 26 :=
  sparse_5_12_2_5_verified.2

def sparse_6_8_2_3_profile : FerrersProfile 6 8 where
  degree := ![4, 4, 3, 0, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_6_8_2_3_triples : List (Fin (6 + 8) × Fin (6 + 8) × Fin (6 + 8)) :=
  [
    (0, 1, 6),
    (0, 3, 4),
    (0, 7, 8),
    (1, 2, 8),
    (1, 3, 5),
    (1, 7, 9),
    (2, 4, 5),
    (2, 6, 7),
    (6, 8, 10),
    (6, 9, 12),
    (7, 11, 13),
    (8, 9, 11),
    (8, 12, 13),
    (9, 10, 13),
    (10, 11, 12)]

def sparse_6_8_2_3_triangles : Finset (Finset (Fin 6 ⊕ Fin 8)) :=
  labeledPacking 6 8 sparse_6_8_2_3_triples

theorem sparse_6_8_2_3_verified : Packing sparse_6_8_2_3_profile.graph sparse_6_8_2_3_triangles ∧
    sparse_6_8_2_3_triangles.card = 15 := by
  have h := labeledPacking_correct sparse_6_8_2_3_profile sparse_6_8_2_3_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_6_8_2_3_packing : Packing sparse_6_8_2_3_profile.graph sparse_6_8_2_3_triangles :=
  sparse_6_8_2_3_verified.1

theorem sparse_6_8_2_3_card : sparse_6_8_2_3_triangles.card = 15 :=
  sparse_6_8_2_3_verified.2

def sparse_7_12_2_4_profile : FerrersProfile 7 12 where
  degree := ![6, 6, 4, 4, 0, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_7_12_2_4_triples : List (Fin (7 + 12) × Fin (7 + 12) × Fin (7 + 12)) :=
  [
    (0, 2, 9),
    (0, 3, 10),
    (0, 4, 5),
    (0, 7, 12),
    (0, 8, 11),
    (1, 2, 4),
    (1, 3, 7),
    (1, 5, 6),
    (1, 8, 9),
    (2, 3, 5),
    (2, 8, 10),
    (3, 4, 6),
    (7, 8, 15),
    (7, 9, 11),
    (7, 13, 14),
    (7, 17, 18),
    (8, 14, 17),
    (8, 16, 18),
    (9, 10, 17),
    (9, 12, 15),
    (9, 13, 18),
    (9, 14, 16),
    (10, 11, 13),
    (10, 12, 18),
    (10, 15, 16),
    (11, 12, 14),
    (11, 15, 18),
    (11, 16, 17),
    (12, 13, 16),
    (13, 15, 17)]

def sparse_7_12_2_4_triangles : Finset (Finset (Fin 7 ⊕ Fin 12)) :=
  labeledPacking 7 12 sparse_7_12_2_4_triples

theorem sparse_7_12_2_4_verified : Packing sparse_7_12_2_4_profile.graph sparse_7_12_2_4_triangles ∧
    sparse_7_12_2_4_triangles.card = 30 := by
  have h := labeledPacking_correct sparse_7_12_2_4_profile sparse_7_12_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_7_12_2_4_packing : Packing sparse_7_12_2_4_profile.graph sparse_7_12_2_4_triangles :=
  sparse_7_12_2_4_verified.1

theorem sparse_7_12_2_4_card : sparse_7_12_2_4_triangles.card = 30 :=
  sparse_7_12_2_4_verified.2

def sparse_9_12_2_4_profile : FerrersProfile 9 12 where
  degree := ![6, 6, 4, 4, 4, 0, 0, 0, 0]
  bound := by decide
  antitone := by decide

def sparse_9_12_2_4_triples : List (Fin (9 + 12) × Fin (9 + 12) × Fin (9 + 12)) :=
  [
    (0, 1, 6),
    (0, 2, 12),
    (0, 4, 8),
    (0, 5, 7),
    (0, 10, 11),
    (1, 2, 10),
    (1, 3, 9),
    (1, 4, 5),
    (1, 7, 8),
    (1, 11, 13),
    (1, 12, 14),
    (2, 3, 7),
    (2, 4, 11),
    (2, 6, 8),
    (3, 4, 10),
    (3, 5, 8),
    (3, 11, 12),
    (4, 6, 7),
    (9, 10, 13),
    (9, 11, 19),
    (9, 12, 15),
    (9, 14, 20),
    (9, 16, 18),
    (10, 12, 19),
    (10, 14, 17),
    (10, 18, 20),
    (11, 15, 20),
    (11, 17, 18),
    (12, 13, 17),
    (13, 14, 15),
    (13, 16, 20),
    (14, 16, 19),
    (15, 16, 17),
    (15, 18, 19),
    (17, 19, 20)]

def sparse_9_12_2_4_triangles : Finset (Finset (Fin 9 ⊕ Fin 12)) :=
  labeledPacking 9 12 sparse_9_12_2_4_triples

theorem sparse_9_12_2_4_verified : Packing sparse_9_12_2_4_profile.graph sparse_9_12_2_4_triangles ∧
    sparse_9_12_2_4_triangles.card = 35 := by
  have h := labeledPacking_correct sparse_9_12_2_4_profile sparse_9_12_2_4_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem sparse_9_12_2_4_packing : Packing sparse_9_12_2_4_profile.graph sparse_9_12_2_4_triangles :=
  sparse_9_12_2_4_verified.1

theorem sparse_9_12_2_4_card : sparse_9_12_2_4_triangles.card = 35 :=
  sparse_9_12_2_4_verified.2

def dense_9_11_7_9_4_3_1_profile : FerrersProfile 9 11 where
  degree := ![9, 9, 9, 9, 9, 9, 7, 0, 0]
  bound := by decide
  antitone := by decide

def dense_9_11_7_9_4_3_1_triples : List (Fin (9 + 11) × Fin (9 + 11) × Fin (9 + 11)) :=
  [
    (0, 1, 14),
    (0, 2, 13),
    (0, 3, 16),
    (0, 4, 17),
    (0, 5, 9),
    (0, 6, 15),
    (0, 7, 8),
    (0, 10, 11),
    (1, 2, 7),
    (1, 3, 4),
    (1, 5, 17),
    (1, 6, 11),
    (1, 9, 13),
    (1, 12, 15),
    (2, 3, 14),
    (2, 4, 11),
    (2, 5, 6),
    (2, 12, 16),
    (2, 15, 17),
    (3, 5, 8),
    (3, 6, 10),
    (3, 11, 15),
    (3, 12, 17),
    (4, 5, 7),
    (4, 6, 14),
    (4, 9, 15),
    (4, 10, 16),
    (5, 11, 16),
    (5, 12, 14),
    (5, 13, 15),
    (9, 10, 17),
    (9, 11, 12),
    (10, 12, 13),
    (10, 14, 15),
    (11, 14, 18),
    (13, 16, 17),
    (14, 17, 19),
    (16, 18, 19)]

def dense_9_11_7_9_4_3_1_triangles : Finset (Finset (Fin 9 ⊕ Fin 11)) :=
  labeledPacking 9 11 dense_9_11_7_9_4_3_1_triples

theorem dense_9_11_7_9_4_3_1_verified : Packing dense_9_11_7_9_4_3_1_profile.graph dense_9_11_7_9_4_3_1_triangles ∧
    dense_9_11_7_9_4_3_1_triangles.card = 38 := by
  have h := labeledPacking_correct dense_9_11_7_9_4_3_1_profile dense_9_11_7_9_4_3_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem dense_9_11_7_9_4_3_1_packing : Packing dense_9_11_7_9_4_3_1_profile.graph dense_9_11_7_9_4_3_1_triangles :=
  dense_9_11_7_9_4_3_1_verified.1

theorem dense_9_11_7_9_4_3_1_card : dense_9_11_7_9_4_3_1_triangles.card = 38 :=
  dense_9_11_7_9_4_3_1_verified.2

def dense_9_11_7_9_4_2_2_profile : FerrersProfile 9 11 where
  degree := ![9, 9, 9, 9, 9, 8, 8, 0, 0]
  bound := by decide
  antitone := by decide

def dense_9_11_7_9_4_2_2_triples : List (Fin (9 + 11) × Fin (9 + 11) × Fin (9 + 11)) :=
  [
    (0, 1, 17),
    (0, 4, 15),
    (0, 5, 7),
    (0, 6, 8),
    (0, 9, 16),
    (0, 10, 14),
    (0, 12, 13),
    (1, 3, 4),
    (1, 5, 15),
    (1, 7, 8),
    (1, 9, 10),
    (1, 11, 12),
    (1, 14, 16),
    (2, 3, 17),
    (2, 4, 11),
    (2, 5, 16),
    (2, 6, 7),
    (2, 12, 14),
    (3, 5, 14),
    (3, 10, 11),
    (3, 12, 16),
    (4, 6, 13),
    (4, 10, 12),
    (5, 6, 10),
    (5, 9, 13),
    (6, 11, 14),
    (6, 15, 16),
    (9, 11, 15),
    (9, 12, 19),
    (9, 14, 17),
    (10, 13, 15),
    (10, 17, 18),
    (11, 13, 18),
    (11, 17, 19),
    (12, 15, 18),
    (13, 14, 19),
    (13, 16, 17),
    (16, 18, 19)]

def dense_9_11_7_9_4_2_2_triangles : Finset (Finset (Fin 9 ⊕ Fin 11)) :=
  labeledPacking 9 11 dense_9_11_7_9_4_2_2_triples

theorem dense_9_11_7_9_4_2_2_verified : Packing dense_9_11_7_9_4_2_2_profile.graph dense_9_11_7_9_4_2_2_triangles ∧
    dense_9_11_7_9_4_2_2_triangles.card = 38 := by
  have h := labeledPacking_correct dense_9_11_7_9_4_2_2_profile dense_9_11_7_9_4_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem dense_9_11_7_9_4_2_2_packing : Packing dense_9_11_7_9_4_2_2_profile.graph dense_9_11_7_9_4_2_2_triangles :=
  dense_9_11_7_9_4_2_2_verified.1

theorem dense_9_11_7_9_4_2_2_card : dense_9_11_7_9_4_2_2_triangles.card = 38 :=
  dense_9_11_7_9_4_2_2_verified.2

def dense_11_11_8_8_3_2_1_profile : FerrersProfile 11 11 where
  degree := ![8, 8, 8, 8, 8, 8, 8, 7, 0, 0, 0]
  bound := by decide
  antitone := by decide

def dense_11_11_8_8_3_2_1_triples : List (Fin (11 + 11) × Fin (11 + 11) × Fin (11 + 11)) :=
  [
    (0, 1, 10),
    (0, 2, 3),
    (0, 4, 14),
    (0, 5, 12),
    (0, 6, 7),
    (0, 11, 13),
    (0, 16, 18),
    (1, 2, 17),
    (1, 3, 9),
    (1, 6, 16),
    (1, 7, 8),
    (1, 11, 18),
    (1, 12, 15),
    (2, 4, 15),
    (2, 5, 6),
    (2, 8, 9),
    (2, 11, 12),
    (2, 13, 16),
    (2, 14, 18),
    (3, 4, 10),
    (3, 6, 8),
    (3, 11, 17),
    (3, 12, 18),
    (3, 14, 16),
    (4, 5, 16),
    (4, 6, 11),
    (4, 7, 17),
    (4, 12, 13),
    (5, 7, 13),
    (5, 8, 10),
    (5, 14, 17),
    (6, 9, 10),
    (6, 12, 17),
    (6, 13, 18),
    (6, 14, 15),
    (7, 11, 15),
    (11, 14, 21),
    (11, 19, 20),
    (12, 14, 20),
    (12, 19, 21),
    (13, 15, 21),
    (13, 17, 19),
    (15, 17, 18),
    (16, 17, 20),
    (18, 20, 21)]

def dense_11_11_8_8_3_2_1_triangles : Finset (Finset (Fin 11 ⊕ Fin 11)) :=
  labeledPacking 11 11 dense_11_11_8_8_3_2_1_triples

theorem dense_11_11_8_8_3_2_1_verified : Packing dense_11_11_8_8_3_2_1_profile.graph dense_11_11_8_8_3_2_1_triangles ∧
    dense_11_11_8_8_3_2_1_triangles.card = 45 := by
  have h := labeledPacking_correct dense_11_11_8_8_3_2_1_profile dense_11_11_8_8_3_2_1_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem dense_11_11_8_8_3_2_1_packing : Packing dense_11_11_8_8_3_2_1_profile.graph dense_11_11_8_8_3_2_1_triangles :=
  dense_11_11_8_8_3_2_1_verified.1

theorem dense_11_11_8_8_3_2_1_card : dense_11_11_8_8_3_2_1_triangles.card = 45 :=
  dense_11_11_8_8_3_2_1_verified.2

def dense_11_11_8_8_4_2_2_profile : FerrersProfile 11 11 where
  degree := ![8, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0]
  bound := by decide
  antitone := by decide

def dense_11_11_8_8_4_2_2_triples : List (Fin (11 + 11) × Fin (11 + 11) × Fin (11 + 11)) :=
  [
    (0, 1, 10),
    (0, 2, 18),
    (0, 3, 13),
    (0, 4, 5),
    (0, 7, 14),
    (0, 8, 9),
    (0, 11, 17),
    (0, 12, 15),
    (1, 2, 15),
    (1, 3, 6),
    (1, 4, 13),
    (1, 5, 11),
    (1, 7, 8),
    (1, 12, 17),
    (2, 3, 12),
    (2, 4, 7),
    (2, 5, 16),
    (2, 6, 11),
    (2, 9, 10),
    (2, 13, 17),
    (3, 4, 8),
    (3, 5, 9),
    (3, 7, 15),
    (3, 11, 14),
    (3, 17, 18),
    (4, 6, 14),
    (4, 11, 12),
    (5, 12, 18),
    (5, 13, 14),
    (5, 15, 17),
    (6, 7, 17),
    (6, 8, 10),
    (6, 13, 18),
    (7, 12, 13),
    (7, 16, 18),
    (11, 15, 16),
    (11, 18, 21),
    (11, 19, 20),
    (12, 14, 16),
    (12, 20, 21),
    (13, 16, 20),
    (13, 19, 21),
    (14, 15, 21),
    (14, 18, 20),
    (15, 18, 19)]

def dense_11_11_8_8_4_2_2_triangles : Finset (Finset (Fin 11 ⊕ Fin 11)) :=
  labeledPacking 11 11 dense_11_11_8_8_4_2_2_triples

theorem dense_11_11_8_8_4_2_2_verified : Packing dense_11_11_8_8_4_2_2_profile.graph dense_11_11_8_8_4_2_2_triangles ∧
    dense_11_11_8_8_4_2_2_triangles.card = 45 := by
  have h := labeledPacking_correct dense_11_11_8_8_4_2_2_profile dense_11_11_8_8_4_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem dense_11_11_8_8_4_2_2_packing : Packing dense_11_11_8_8_4_2_2_profile.graph dense_11_11_8_8_4_2_2_triangles :=
  dense_11_11_8_8_4_2_2_verified.1

theorem dense_11_11_8_8_4_2_2_card : dense_11_11_8_8_4_2_2_triangles.card = 45 :=
  dense_11_11_8_8_4_2_2_verified.2

def dense_11_12_8_8_4_2_2_profile : FerrersProfile 11 12 where
  degree := ![8, 8, 8, 8, 8, 8, 8, 8, 0, 0, 0]
  bound := by decide
  antitone := by decide

def dense_11_12_8_8_4_2_2_triples : List (Fin (11 + 12) × Fin (11 + 12) × Fin (11 + 12)) :=
  [
    (0, 1, 4),
    (0, 3, 10),
    (0, 5, 9),
    (0, 6, 14),
    (0, 7, 16),
    (0, 11, 15),
    (0, 17, 18),
    (1, 2, 3),
    (1, 5, 16),
    (1, 6, 15),
    (1, 7, 18),
    (1, 8, 9),
    (1, 14, 17),
    (2, 4, 12),
    (2, 6, 16),
    (2, 7, 9),
    (2, 8, 10),
    (2, 13, 17),
    (2, 14, 18),
    (3, 4, 16),
    (3, 5, 12),
    (3, 6, 7),
    (3, 11, 18),
    (3, 13, 14),
    (4, 5, 15),
    (4, 6, 17),
    (4, 7, 8),
    (4, 9, 10),
    (4, 11, 14),
    (5, 6, 11),
    (5, 7, 10),
    (7, 11, 13),
    (7, 12, 14),
    (11, 12, 16),
    (11, 21, 22),
    (12, 13, 22),
    (12, 15, 18),
    (12, 17, 20),
    (12, 19, 21),
    (13, 15, 21),
    (13, 16, 18),
    (13, 19, 20),
    (14, 15, 19),
    (14, 16, 21),
    (14, 20, 22),
    (15, 16, 17),
    (17, 19, 22),
    (18, 20, 21)]

def dense_11_12_8_8_4_2_2_triangles : Finset (Finset (Fin 11 ⊕ Fin 12)) :=
  labeledPacking 11 12 dense_11_12_8_8_4_2_2_triples

theorem dense_11_12_8_8_4_2_2_verified : Packing dense_11_12_8_8_4_2_2_profile.graph dense_11_12_8_8_4_2_2_triangles ∧
    dense_11_12_8_8_4_2_2_triangles.card = 48 := by
  have h := labeledPacking_correct dense_11_12_8_8_4_2_2_profile dense_11_12_8_8_4_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem dense_11_12_8_8_4_2_2_packing : Packing dense_11_12_8_8_4_2_2_profile.graph dense_11_12_8_8_4_2_2_triangles :=
  dense_11_12_8_8_4_2_2_verified.1

theorem dense_11_12_8_8_4_2_2_card : dense_11_12_8_8_4_2_2_triangles.card = 48 :=
  dense_11_12_8_8_4_2_2_verified.2

def dense_10_10_7_7_4_2_2_profile : FerrersProfile 10 10 where
  degree := ![7, 7, 7, 7, 7, 7, 7, 0, 0, 0]
  bound := by decide
  antitone := by decide

def dense_10_10_7_7_4_2_2_triples : List (Fin (10 + 10) × Fin (10 + 10) × Fin (10 + 10)) :=
  [
    (0, 1, 15),
    (0, 2, 9),
    (0, 3, 8),
    (0, 4, 12),
    (0, 6, 7),
    (0, 10, 16),
    (0, 11, 14),
    (1, 2, 14),
    (1, 4, 11),
    (1, 5, 10),
    (1, 6, 13),
    (1, 8, 9),
    (2, 3, 10),
    (2, 4, 7),
    (2, 5, 13),
    (2, 6, 8),
    (2, 11, 15),
    (3, 5, 15),
    (3, 6, 16),
    (3, 13, 14),
    (4, 5, 8),
    (4, 6, 9),
    (4, 10, 13),
    (5, 6, 11),
    (5, 7, 9),
    (6, 10, 15),
    (6, 12, 14),
    (10, 14, 19),
    (10, 17, 18),
    (11, 12, 17),
    (11, 13, 18),
    (11, 16, 19),
    (12, 13, 16),
    (12, 15, 19),
    (14, 15, 16)]

def dense_10_10_7_7_4_2_2_triangles : Finset (Finset (Fin 10 ⊕ Fin 10)) :=
  labeledPacking 10 10 dense_10_10_7_7_4_2_2_triples

theorem dense_10_10_7_7_4_2_2_verified : Packing dense_10_10_7_7_4_2_2_profile.graph dense_10_10_7_7_4_2_2_triangles ∧
    dense_10_10_7_7_4_2_2_triangles.card = 35 := by
  have h := labeledPacking_correct dense_10_10_7_7_4_2_2_profile dense_10_10_7_7_4_2_2_triples (by decide) (by decide +kernel)
  exact ⟨h.1, h.2⟩

theorem dense_10_10_7_7_4_2_2_packing : Packing dense_10_10_7_7_4_2_2_profile.graph dense_10_10_7_7_4_2_2_triangles :=
  dense_10_10_7_7_4_2_2_verified.1

theorem dense_10_10_7_7_4_2_2_card : dense_10_10_7_7_4_2_2_triangles.card = 35 :=
  dense_10_10_7_7_4_2_2_verified.2

end ResearchMain.Tuza.Certificates
