import KRk.Definitions
import KRk.Instances
import Batteries.Data.Fin.Basic
import Batteries.Data.Fin.Lemmas

def MoveBlackKingAlt {N} (P1 P2: Position N) :=
  P2.BKx + 1 = P1.BKx ∧ P2.BKy + 1 = P1.BKy ∨
  P2.BKx + 1 = P1.BKx ∧ P2.BKy = P1.BKy     ∨
  P2.BKx + 1 = P1.BKx ∧ P2.BKy = P1.BKy + 1 ∨
  P2.BKx = P1.BKx     ∧ P2.BKy = P1.BKy + 1 ∨
  P2.BKx = P1.BKx + 1 ∧ P2.BKy = P1.BKy + 1 ∨
  P2.BKx = P1.BKx + 1 ∧ P2.BKy = P1.BKy     ∨
  P2.BKx = P1.BKx + 1 ∧ P2.BKy + 1 = P1.BKy ∨
  P2.BKx = P1.BKx     ∧ P2.BKy + 1 = P1.BKy

theorem MoveBlackKingAltThm {N} (P1 P2: Position N): MoveBlackKing P1 P2 ↔ MoveBlackKingAlt P1 P2 := by
  unfold MoveBlackKing
  unfold MoveBlackKingAlt
  cases P1
  cases P2
  simp at *
  omega

  def AllBlackKingMoves {N} (P: Position N): List (Position N) := by
  have makePosition: ∀ (x y: Nat) (H: x < N ∧ y < N), Position N := by
    intros x y H
    refine (@Position.mk N P.WKx P.WKy P.WRx P.WRy x y White (by cases P; simp at *; omega))
  have T1: List (Position N) := by
    by_cases (0 < P.BKx ∧ 0 < P.BKy)
    . exact [makePosition (P.BKx - 1) (P.BKy -1) (by cases P; simp at *; omega)]
    . exact []
  have T2: List (Position N) := by
    by_cases (0 < P.BKx)
    . exact [makePosition (P.BKx - 1) P.BKy (by cases P; simp at *; omega)]
    . exact []
  have T3: List (Position N) := by
    by_cases (0 < P.BKx ∧ P.BKy + 1 < N)
    . exact [makePosition (P.BKx - 1) (P.BKy + 1) (by cases P; simp at *; omega)]
    . exact []
  have T4: List (Position N) := by
    by_cases (P.BKy + 1 < N)
    . exact [makePosition P.BKx (P.BKy + 1) (by cases P; simp at *; omega)]
    . exact []
  have T5: List (Position N) := by
    by_cases (P.BKx + 1 < N ∧ P.BKy + 1 < N)
    . exact [makePosition (P.BKx + 1) (P.BKy + 1) (by cases P; simp at *; omega)]
    . exact []
  have T6: List (Position N) := by
    by_cases (P.BKx + 1 < N)
    . exact [makePosition (P.BKx + 1) P.BKy (by cases P; simp at *; omega)]
    . exact []
  have T7: List (Position N) := by
    by_cases (P.BKx + 1 < N ∧ 0 < P.BKy)
    . exact [makePosition (P.BKx + 1) (P.BKy - 1) (by cases P; simp at *; omega)]
    . exact []
  have T8: List (Position N) := by
    by_cases (0 < P.BKy)
    . exact [makePosition P.BKx (P.BKy - 1) (by cases P; simp at *; omega)]
    . exact []
  have L := T1 ++ T2 ++ T3 ++ T4 ++ T5 ++ T6 ++ T7 ++ T8
  exact List.filter (λ p => Decidable.decide (LegalPosition p)) L


theorem AllBlackKingMovesCorrect {N} (P: Position N) (H: LegalPosition P) (Ht: P.Turn = Black):
  ∀ P', LegalBlackMove P P' ↔ P' ∈ AllBlackKingMoves P := by
    intros P'
    constructor
    . intros H0
      unfold LegalBlackMove at H0
      obtain ⟨H0, H1, H2, H3, H4, H5⟩ := H0
      unfold AllBlackKingMoves
      rewrite [MoveBlackKingAltThm] at H0
      unfold MoveBlackKingAlt at H0
      obtain H0 | H0 | H0 | H0 | H0 | H0 | H0 | H0 := H0
      . obtain ⟨H0, H1⟩ := H0
        simp
        left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; right; right; right
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveBlackKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
    . intros H0
      unfold AllBlackKingMoves at H0
      simp at H0
      obtain H0 | H0 | H0 | H0 | H0 | H0 | H0 | H0 := H0
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at *
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalBlackMove
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveBlackKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveBlackKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *

def MoveWhiteKingAlt {N} (P1 P2: Position N) :=
  P2.WKx + 1 = P1.WKx ∧ P2.WKy + 1 = P1.WKy ∨
  P2.WKx + 1 = P1.WKx ∧ P2.WKy = P1.WKy     ∨
  P2.WKx + 1 = P1.WKx ∧ P2.WKy = P1.WKy + 1 ∨
  P2.WKx = P1.WKx     ∧ P2.WKy = P1.WKy + 1 ∨
  P2.WKx = P1.WKx + 1 ∧ P2.WKy = P1.WKy + 1 ∨
  P2.WKx = P1.WKx + 1 ∧ P2.WKy = P1.WKy     ∨
  P2.WKx = P1.WKx + 1 ∧ P2.WKy + 1 = P1.WKy ∨
  P2.WKx = P1.WKx     ∧ P2.WKy + 1 = P1.WKy

theorem MoveWhiteKingAltThm {N} (P1 P2: Position N): MoveWhiteKing P1 P2 ↔ MoveWhiteKingAlt P1 P2 := by
  unfold MoveWhiteKing
  unfold MoveWhiteKingAlt
  cases P1
  cases P2
  simp at *
  omega

def AllWhiteKingMoves {N} (P: Position N): List (Position N) := by
  have makePosition: ∀ (x y: Nat) (H: x < N ∧ y < N), Position N := by
    intros x y H
    refine (@Position.mk N x y P.WRx P.WRy P.BKx P.BKy Black (by cases P; simp at *; omega))
  have T1: List (Position N) := by
    by_cases (0 < P.WKx ∧ 0 < P.WKy)
    . exact [makePosition (P.WKx - 1) (P.WKy - 1) (by cases P; simp at *; omega)]
    . exact []
  have T2: List (Position N) := by
    by_cases (0 < P.WKx)
    . exact [makePosition (P.WKx - 1) P.WKy (by cases P; simp at *; omega)]
    . exact []
  have T3: List (Position N) := by
    by_cases (0 < P.WKx ∧ P.WKy + 1 < N)
    . exact [makePosition (P.WKx - 1) (P.WKy + 1) (by cases P; simp at *; omega)]
    . exact []
  have T4: List (Position N) := by
    by_cases (P.WKy + 1 < N)
    . exact [makePosition P.WKx (P.WKy + 1) (by cases P; simp at *; omega)]
    . exact []
  have T5: List (Position N) := by
    by_cases (P.WKx + 1 < N ∧ P.WKy + 1 < N)
    . exact [makePosition (P.WKx + 1) (P.WKy + 1) (by cases P; simp at *; omega)]
    . exact []
  have T6: List (Position N) := by
    by_cases (P.WKx + 1 < N)
    . exact [makePosition (P.WKx + 1) P.WKy (by cases P; simp at *; omega)]
    . exact []
  have T7: List (Position N) := by
    by_cases (P.WKx + 1 < N ∧ 0 < P.WKy)
    . exact [makePosition (P.WKx + 1) (P.WKy - 1) (by cases P; simp at *; omega)]
    . exact []
  have T8: List (Position N) := by
    by_cases (0 < P.WKy)
    . exact [makePosition P.WKx (P.WKy - 1) (by cases P; simp at *; omega)]
    . exact []
  have L := T1 ++ T2 ++ T3 ++ T4 ++ T5 ++ T6 ++ T7 ++ T8
  exact List.filter (λ p => Decidable.decide (LegalPosition p)) L

theorem AllWhiteKingMovesCorrect {N} (P: Position N) (H: LegalPosition P) (Ht: P.Turn = White):
  ∀ P', LegalMoveWhiteKing P P' ↔ P' ∈ AllWhiteKingMoves P := by
    intros P'
    constructor
    . intros H0
      unfold LegalMoveWhiteKing at H0
      obtain ⟨H0, H1, H2, H3, H4, H5⟩ := H0
      unfold AllWhiteKingMoves
      rewrite [MoveWhiteKingAltThm] at H0
      unfold MoveWhiteKingAlt at H0
      obtain H0 | H0 | H0 | H0 | H0 | H0 | H0 | H0 := H0
      . obtain ⟨H0, H1⟩ := H0
        simp
        left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; right; right; left
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
      . obtain ⟨H0, H1⟩ := H0
        simp
        right; right; right; right; right; right; right
        split
        . rw [List.mem_filter]
          simp
          constructor
          . cases P'
            cases P
            simp at *
            unfold OtherAfterMoveWhiteKing at *
            simp at *
            omega
          . assumption
        . simp
          cases P'
          cases P
          simp at *
          omega
    . intros H0
      unfold AllWhiteKingMoves at H0
      simp at H0
      obtain H0 | H0 | H0 | H0 | H0 | H0 | H0 | H0 := H0
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at *
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *
      . rw [List.mem_filter] at H0
        simp at *
        obtain ⟨H0, H1⟩ := H0
        split at H0
        . simp at H0
          unfold LegalMoveWhiteKing
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          . clear H H1 Ht
            unfold MoveWhiteKing
            rw [H0]
            simp at *
            omega
          . clear H H1 Ht
            unfold OtherAfterMoveWhiteKing
            cases P
            cases P'
            simp at *
            omega
          . assumption
          . rw [H0]
          . assumption
          . assumption
        . simp at *

def AllWhiteRookMoves {N} (P: Position N): List (Position N) := by
  have makePosition1: ∀ (x: Fin N), Position N := by
    intros x
    refine (@Position.mk N P.WKx P.WKy x.1 P.WRy P.BKx P.BKy Black (by cases x; cases P; simp at *; omega))
  have makePosition2: ∀ (y: Fin N), Position N := by
    intros y
    refine (@Position.mk N P.WKx P.WKy P.WRx y.1 P.BKx P.BKy Black (by cases y; cases P; simp at *; omega))
  have L1: List (Position N) := List.map makePosition1 (Fin.list N)
  have L2: List (Position N) := List.map makePosition2 (Fin.list N)
  have L := L1 ++ L2
  exact List.filter (λ p => Decidable.decide (LegalMoveWhiteRook P p)) L


theorem everyFinInFinList: ∀ {N} (f: Fin N), f ∈ Fin.list N := by
  intro n m
  refine List.mem_iff_get.mpr ?_
  have : m.val < (Fin.list n).length := by
    rw [Fin.length_list]
    exact m.2
  refine ⟨⟨m.val,this⟩,?_⟩
  simp

theorem AllWhiteRookMovesCorrect {N} (P: Position N) (H: LegalPosition P) (Ht: P.Turn = White):
  ∀ P', LegalMoveWhiteRook P P' ↔ P' ∈ AllWhiteRookMoves P := by
  intros P'
  constructor
  . intros H0
    unfold LegalMoveWhiteRook at H0
    obtain ⟨H0, H1, H2, H3, H4, H5⟩ := H0
    unfold AllWhiteRookMoves
    simp
    unfold MoveWhiteRook at H0
    obtain H0 | H0 := H0
    . right
      obtain ⟨H6, H7, H8, H9⟩ := H0
      rw [List.mem_filter]
      constructor
      . clear H H4 H5 H7 H8 H9 Ht
        rewrite [List.mem_map]
        let a: Fin N := ⟨P'.WRy, (by cases P'; simp at *; omega)⟩
        exists a
        constructor
        . apply everyFinInFinList
        . simp
          unfold OtherAfterMoveWhiteRook at H1
          cases P'
          cases P
          simp
          simp at H1
          simp at H2
          simp at H3
          simp at H6
          omega
      . simp
        unfold LegalMoveWhiteRook
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try assumption
        unfold MoveWhiteRook
        left
        trivial
    . left
      obtain ⟨H6, H7, H8, H9⟩ := H0
      rw [List.mem_filter]
      constructor
      . clear H H4 H5 H7 H8 H9 Ht
        rewrite [List.mem_map]
        let a: Fin N := ⟨P'.WRx, (by cases P'; simp at *; omega)⟩
        exists a
        constructor
        . apply everyFinInFinList
        . simp
          unfold OtherAfterMoveWhiteRook at H1
          cases P'
          cases P
          simp
          simp at H1
          simp at H2
          simp at H3
          simp at H6
          omega
      . simp
        unfold LegalMoveWhiteRook
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try assumption
        unfold MoveWhiteRook
        right
        trivial
  . intros H0
    unfold AllWhiteRookMoves at H0
    simp at *
    obtain H0 | H0 := H0
    . rw [List.mem_filter] at H0
      obtain ⟨H0, H1⟩ := H0
      simp at *
      assumption
    . rw [List.mem_filter] at H0
      obtain ⟨H0, H1⟩ := H0
      simp at *
      assumption
