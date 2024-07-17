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


theorem tiny_omega (N A: Nat): A < N → N - 1 - (N - 1 - A) = A := by omega
theorem tiny_omega_0 (A B: Nat): A = B → B = A := by omega

theorem Thm {N} (P1 P2: Position N): SamePosition P1 P2 ↔ Normalize P1 = Normalize P2 := by
  constructor
  . intro H
    unfold SamePosition at H
    obtain H | H | H | H | H | H | H | H := H <;> rw [H] <;> clear H P1
    . sorry
    . cases P2; rename_i WKx WKy WRx WRy BKx BKy Turn DC
      obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
      unfold Normalize
      congr 1
      unfold NormalizeY
      unfold MirrorY
      simp
      split <;> rename_i H
      . sorry
      . simp at *
        unfold NormalizeX at *
        simp at *
        split at H <;> rename_i H1
        . simp at *
          split <;> rename_i H2
          . simp at *
            split -- doesn't work :(
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
