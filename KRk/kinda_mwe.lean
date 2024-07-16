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

def MirrorX {N} (P: Position N): Position N :=
  Position.mk (N - 1 - P.WKx) P.WKy (N - 1 - P.WRx) P.WRy (N - 1 - P.BKx) P.BKy P.Turn
  (by cases P
      simp
      omega)

def MirrorY {N} (P: Position N): Position N :=
  Position.mk P.WKx (N - 1 - P.WKy) P.WRx (N - 1 - P.WRy) P.BKx (N - 1 - P.BKy) P.Turn
  (by cases P
      simp
      omega)

def MirrorDiag {N} (P: Position N): Position N :=
  Position.mk P.WKy P.WKx P.WRy P.WRx P.BKy P.BKx P.Turn
  (by cases P
      simp
      omega)

def SamePosition {N} (P1 P2: Position N) :=
  P1 = P2 ∨ P1 = MirrorX P2 ∨ P1 = MirrorY P2 ∨ P1 = MirrorY (MirrorX P2) ∨
  P1 = MirrorDiag P2 ∨ P1 = MirrorDiag (MirrorX P2) ∨
  P1 = MirrorDiag (MirrorY P2) ∨ P1 = MirrorDiag (MirrorY (MirrorX P2))

def NormalizeX {N} (P: Position N): Position N :=
  if P.BKx < N - 1 - P.BKx ∨ P.BKx = N - 1 - P.BKx ∧ (P.WKx < N - 1 - P.WKx ∨ P.WKx = N - 1 - P.WKx ∧ P.WRx <= N - 1 - P.WRx)
  then P
  else MirrorX P

def NormalizeY {N} (P: Position N): Position N :=
  if P.BKy < N - 1 - P.BKy ∨ P.BKy = N - 1 - P.BKy ∧ (P.WKy < N - 1 - P.WKy ∨ P.WKy = N - 1 - P.WKy ∧ P.WRy <= N - 1 - P.WRy)
  then P
  else MirrorY P

def NormalizeDiag {N} (P: Position N): Position N :=
  if P.BKy < P.BKx ∨ P.BKy = P.BKx ∧ (P.WKy < P.WKx ∨ P.WKy = P.WKx ∧ P.WRy ≤ P.WRx)
  then P
  else MirrorDiag P

def Normalize {N} (P: Position N): Position N := NormalizeDiag (NormalizeY (NormalizeX P))

theorem Thm {N} (P1 P2: Position N): SamePosition P1 P2 ↔ Normalize P1 = Normalize P2 := by
  constructor <;> intros H
  . unfold Normalize
    obtain H | H | H | H | H | H | H | H := H <;> rw [H] <;> clear H P1 <;> cases P2
    . congr 2
      unfold NormalizeX
      unfold MirrorX
      split <;> split <;> simp at *
      . omega
      . omega
      . omega
    . congr 1
      unfold NormalizeX
      split <;> split <;> simp at *
      . unfold NormalizeY
        split <;> split <;> simp at *
        . unfold MirrorY at *
          simp at *
          omega
        . unfold MirrorY at *
          simp at *
          omega
        . unfold MirrorY at *
          simp at *
          omega
      . unfold NormalizeY
        split <;> split
        . unfold MirrorY at *
          simp at *
          unfold MirrorX at *
          simp at *
          omega
        . unfold MirrorY at *
          simp at *
          unfold MirrorX at *
          simp at *
          omega
          sorry
        . sorry
        . sorry
      . sorry
      . sorry
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry
  . sorry
