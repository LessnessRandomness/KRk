import KRk.Definitions

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

def MirrorXTwice {N} (P: Position N): MirrorX (MirrorX P) = P := by
  cases P
  unfold MirrorX
  simp
  omega

def MirrorYTwice {N} (P: Position N): MirrorY (MirrorY P) = P := by
  cases P
  unfold MirrorY
  simp
  omega

def MirrorDiagTwice {N} (P: Position N): MirrorDiag (MirrorDiag P) = P := by
  cases P
  unfold MirrorDiag
  simp at *

def SamePositionSymmAux {N} (P1 P2: Position N): SamePosition P1 P2 → SamePosition P2 P1 := by
  intro h
  obtain h | h | h | h | h | h | h | h := h
  . cases h
    left
    simp
  . cases h
    right; left
    rw [MirrorXTwice]
  . cases h
    right; right; left
    rw [MirrorYTwice]
  . cases h
    right; right; right; left
    unfold MirrorX at *
    unfold MirrorY at *
    cases P2
    simp at *
    omega
  . cases h
    right; right; right; right; left
    rw [MirrorDiagTwice]
  . cases h
    right; right; right; right; right; right; left
    unfold MirrorX at *
    unfold MirrorY at *
    unfold MirrorDiag at *
    cases P2
    simp at *
    omega
  . cases h
    right; right; right; right; right; left
    unfold MirrorX at *
    unfold MirrorY at *
    unfold MirrorDiag at *
    cases P2
    simp at *
    omega
  . cases h
    right; right; right; right; right; right; right
    unfold MirrorX at *
    unfold MirrorY at *
    unfold MirrorDiag at *
    cases P2
    simp at *
    omega

def SamePositionSymm {N} (P1 P2: Position N): SamePosition P1 P2 ↔ SamePosition P2 P1 := by
  constructor
  . apply SamePositionSymmAux
  . apply SamePositionSymmAux



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

theorem NormalizeXMirrorX {N} (P: Position N): NormalizeX (MirrorX P) = NormalizeX P := by
  unfold NormalizeX
  unfold MirrorX at *
  split <;> split
  . cases P
    simp at *
    omega
  . cases P
    simp at *
  . cases P
    simp at *
    omega
  . cases P
    simp at *
    omega

theorem NormalizeYMirrorY {N} (P: Position N): NormalizeY (MirrorY P) = NormalizeY P := by
  unfold NormalizeY
  unfold MirrorY at *
  split <;> split
  . cases P
    simp at *
    omega
  . cases P
    simp at *
  . cases P
    simp at *
    omega
  . cases P
    simp at *
    omega

theorem NormalizeDiagMirrorDiag {N} (P: Position N): NormalizeDiag (MirrorDiag P) = NormalizeDiag P := by
  unfold NormalizeDiag
  unfold MirrorDiag at *
  split <;> split
  . cases P
    simp at *
    omega
  . cases P
    simp at *
  . cases P
    simp at *
  . cases P
    simp at *
    omega

theorem SwapNormalizeXAndNormalizeY {N} (P: Position N): NormalizeY (NormalizeX P) = NormalizeX (NormalizeY P) := by
  unfold NormalizeX
  unfold NormalizeY
  split
  . split
    . simp
    . split
      . simp
      . exfalso
        unfold MirrorY at *
        cases P
        simp at *
        omega
  . split
    . split
      . simp
      . exfalso
        unfold MirrorX at *
        cases P
        simp at *
        omega
    . split
      . exfalso
        unfold MirrorX at *
        cases P
        simp at *
        omega
      . split
        . exfalso
          unfold MirrorY at *
          cases P
          simp at *
          omega
        . unfold MirrorX at *
          unfold MirrorY at *
          cases P
          simp at *

theorem NormalizeXTwice {N} (P: Position N): NormalizeX (NormalizeX P) = NormalizeX P := by
  unfold NormalizeX
  split
  . simp
  . split
    . simp
    . exfalso
      unfold MirrorX at *
      cases P
      simp at *
      omega

theorem NormalizeYTwice {N} (P: Position N): NormalizeY (NormalizeY P) = NormalizeY P := by
  unfold NormalizeY
  split
  . simp
  . split
    . simp
    . exfalso
      unfold MirrorY at *
      cases P
      simp at *
      omega

theorem NormalizeDiagTwice {N} (P: Position N): NormalizeDiag (NormalizeDiag P) = NormalizeDiag P := by
  unfold NormalizeDiag
  split
  . simp
  . split
    . simp
    . exfalso
      unfold MirrorDiag at *
      cases P
      simp at *
      omega



theorem Thm {N} (P1 P2: Position N): SamePosition P1 P2 ↔ Normalize P1 = Normalize P2 := by
  constructor
  . intro H
    unfold SamePosition at H
    obtain H | H | H | H | H | H | H | H := H
    . cases H
      simp
    . unfold Normalize

      rw [NormalizeX_thm _ _ H]
    . unfold Normalize
      rw [SwapNormalizeXAndNormalizeY P1, SwapNormalizeXAndNormalizeY P2]
      rw [NormalizeY_thm _ _ H]
    . unfold Normalize
      rw [H]
      rw [SwapNormalizeXAndNormalizeY]
      rw [NormalizeYMirrorY]
      rw [<- SwapNormalizeXAndNormalizeY]
      rw [NormalizeXMirrorX]
    . rw [H]
      clear H P1
      unfold Normalize
      unfold NormalizeX
      unfold NormalizeY
      unfold NormalizeDiag
      split
      . split
        . split
          . split
            . split
              . split
                . unfold MirrorDiag at *
                  cases P2
                  simp at *
                  omega
                . simp
              . split
                . unfold MirrorDiag at *
                  unfold MirrorY at *
                  cases P2
                  simp at *
                  omega
                . sorry
            . sorry
          . sorry
        . sorry
      . sorry
    . sorry
    . sorry
    . sorry
  . sorry
