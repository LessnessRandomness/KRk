def White: Nat := 0
def Black: Nat := 1

structure Position (N: Nat) where
  WKx: Nat
  WKy: Nat
  WRx: Nat
  WRy: Nat
  BKx: Nat
  BKy: Nat
  Turn: Nat
  DimensionCheck: WKx < N ∧ WKy < N ∧ WRx < N ∧ WRy < N ∧ BKx < N ∧ BKy < N

def NotOnSameSquare {N} (P: Position N) :=
  (P.WKx ≠ P.WRx ∨ P.WKy ≠ P.WRy) ∧ (P.Turn = Black → (P.WRx ≠ P.BKx ∨ P.WRy ≠ P.BKy))

def NotKingNextToKing {N} (P: Position N) :=
  P.WKx > P.BKx + 1 ∨ P.BKx > P.WKx + 1 ∨ P.WKy > P.BKy + 1 ∨ P.BKy > P.WKy + 1

def Between (x y z: Nat) :=
  x < y ∧ y < z ∨ z < y ∧ y < x

def BlackKingAttacked {N} (P: Position N) :=
  P.WRx = P.BKx ∧ P.BKy ≠ P.WRy ∧ (¬ Between P.WRy P.WKy P.BKy ∨ P.WRx ≠ P.WKx) ∨
  P.WRy = P.BKy ∧ P.BKx ≠ P.WRx ∧ (¬ Between P.WRx P.WKx P.BKx ∨ P.WRy ≠ P.WKy)

def LegalPosition {N} (P: Position N) :=
  NotOnSameSquare P ∧ NotKingNextToKing P ∧ P.Turn ≤ 1 ∧ ¬ (BlackKingAttacked P ∧ P.Turn = White)

def MoveWhiteKing {N} (P1 P2: Position N) :=
  P1.WKx ≤ P2.WKx + 1 ∧ P2.WKx ≤ P1.WKx + 1 ∧
  P1.WKy ≤ P2.WKy + 1 ∧ P2.WKy ≤ P1.WKy + 1 ∧
  (P1.WKx ≠ P2.WKx ∨ P1.WKy ≠ P2.WKy)

def OtherAfterMoveWhiteKing {N} (P1 P2: Position N) :=
  P1.BKx = P2.BKx ∧ P1.BKy = P2.BKy ∧ P1.WRx = P2.WRx ∧ P1.WRy = P2.WRy

def LegalMoveWhiteKing {N} (P1 P2: Position N) :=
  MoveWhiteKing P1 P2 ∧ OtherAfterMoveWhiteKing P1 P2 ∧
  P1.Turn = White ∧ P2.Turn = Black ∧
  LegalPosition P1 ∧ LegalPosition P2

def MoveWhiteRook {N} (P1 P2: Position N) :=
  (P1.WRx = P2.WRx ∧ P1.WRy ≠ P2.WRy ∧
   (P1.WKx ≠ P1.WRx ∨ ¬ Between P1.WRy P1.WKy P2.WRy) ∧
   (P1.BKx ≠ P1.WRx ∨ ¬ Between P1.WRy P2.BKy P2.WRy))
  ∨
  (P1.WRy = P2.WRy ∧ P1.WRx ≠ P2.WRx ∧
   (P1.WKy ≠ P1.WRy ∨ ¬ Between P1.WRx P1.WKx P2.WRx) ∧
   (P1.BKy ≠ P1.WRy ∨ ¬ Between P1.WRx P1.BKx P2.WRx))

def OtherAfterMoveWhiteRook {N} (P1 P2: Position N) :=
  P1.WKx = P2.WKx ∧ P1.WKy = P2.WKy ∧ P1.BKx = P2.BKx ∧ P1.BKy = P2.BKy

def LegalMoveWhiteRook {N} (P1 P2: Position N) :=
  MoveWhiteRook P1 P2 ∧ OtherAfterMoveWhiteRook P1 P2 ∧
  P1.Turn = White ∧ P2.Turn = Black ∧
  LegalPosition P1 ∧ LegalPosition P2

def LegalWhiteMove {N} (P1 P2: Position N) :=
  LegalMoveWhiteKing P1 P2 ∨ LegalMoveWhiteRook P1 P2

def MoveBlackKing {N} (P1 P2: Position N) :=
  P1.BKx ≤ P2.BKx + 1 ∧ P2.BKx ≤ P1.BKx + 1 ∧
  P1.BKy ≤ P2.BKy + 1 ∧ P2.BKy ≤ P1.BKy + 1 ∧
  (P1.BKx ≠ P2.BKx ∨ P1.BKy ≠ P2.BKy)

def OtherAfterMoveBlackKing {N} (P1 P2: Position N) :=
  P1.WKx = P2.WKx ∧ P1.WKy = P2.WKy ∧ P1.WRx = P2.WRx ∧ P1.WRy = P2.WRy

def LegalBlackMove {N} (P1 P2: Position N) :=
  MoveBlackKing P1 P2 ∧ OtherAfterMoveBlackKing P1 P2 ∧
  P1.Turn = Black ∧ P2.Turn = White ∧
  LegalPosition P1 ∧ LegalPosition P2

def Checkmate {N} (P: Position N) :=
  LegalPosition P ∧ BlackKingAttacked P ∧ P.Turn = Black ∧ ∀ P', ¬ LegalBlackMove P P'

def Stalemate {N} (P: Position N) :=
  LegalPosition P ∧ ¬ BlackKingAttacked P ∧ P.Turn = Black ∧ ∀ P', ¬ LegalBlackMove P P'

def InsufficientMaterial {N} (P: Position N) :=
  LegalPosition P ∧ P.Turn = White ∧ P.BKx = P.WRx ∧ P.BKy = P.WRy/\ P.BKx = P.WRx /\ P.BKy = P.WRy

def Draw {N} (P: Position N) := InsufficientMaterial P ∨ Stalemate P


inductive CheckmateInAtMostXMoves {N}: Position N → Nat → Prop where
| checkmate_done: ∀ P, Checkmate P → CheckmateInAtMostXMoves P 0
| checkmate_S: ∀ P P0 n, LegalWhiteMove P P0 → (∀ P1, LegalBlackMove P0 P1 → CheckmateInAtMostXMoves P1 n) →
               CheckmateInAtMostXMoves P (n + 1)

def CheckmateInXMoves {N} (P: Position N) (n: Nat) :=
  if n = 0
  then Checkmate P
  else CheckmateInAtMostXMoves P n ∧ ¬ CheckmateInAtMostXMoves P (n - 1)
