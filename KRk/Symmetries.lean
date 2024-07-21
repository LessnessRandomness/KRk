import KRk.Definitions
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs

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

def MirrorXYSwap {N} (P: Position N): MirrorX (MirrorY P) = MirrorY (MirrorX P) := by
  cases P
  unfold MirrorX
  unfold MirrorY
  simp

def MirrorDiagXSwap {N} (P: Position N): MirrorDiag (MirrorX P) = MirrorY (MirrorDiag P) := by
  cases P
  unfold MirrorX
  unfold MirrorY
  unfold MirrorDiag
  simp

def MirrorDiagYSwap {N} (P: Position N): MirrorDiag (MirrorY P) = MirrorX (MirrorDiag P) := by
  cases P
  unfold MirrorX
  unfold MirrorY
  unfold MirrorDiag
  simp

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
    rw [MirrorXYSwap]
    rw [MirrorYTwice]
    rw [MirrorXTwice]
  . cases h
    right; right; right; right; left
    rw [MirrorDiagTwice]
  . cases h
    right; right; right; right; right; right; left
    rw [MirrorDiagYSwap]
    rw [MirrorDiagTwice]
    rw [MirrorXTwice]
  . cases h
    right; right; right; right; right; left
    rw [MirrorDiagXSwap]
    rw [MirrorDiagTwice]
    rw [MirrorYTwice]
  . cases h
    right; right; right; right; right; right; right
    rw [MirrorDiagYSwap]
    rw [MirrorDiagXSwap]
    rw [MirrorDiagTwice]
    rw [MirrorYTwice]
    rw [MirrorXTwice]

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
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 <;> unfold MirrorX at * <;> simp at *
  . omega
  . omega
  . omega

theorem NormalizeYMirrorY {N} (P: Position N): NormalizeY (MirrorY P) = NormalizeY P := by
  unfold NormalizeY
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 <;> unfold MirrorY at * <;> simp at *
  . omega
  . omega
  . omega

theorem NormalizeDiagMirrorDiag {N} (P: Position N): NormalizeDiag (MirrorDiag P) = NormalizeDiag P := by
  unfold NormalizeDiag
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 <;> unfold MirrorDiag at * <;> simp at *
  . omega
  . omega

theorem NormalizeXMirrorY {N} (P: Position N): NormalizeX (MirrorY P) = MirrorY (NormalizeX P) := by
  unfold NormalizeX
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 H1 <;> unfold MirrorY at * <;> simp at *
  · unfold MirrorX; simp at *
    omega
  · unfold MirrorX; simp at *
    omega
  · unfold MirrorX; simp at *

theorem NormalizeXMirrorDiag {N} (P: Position N): NormalizeX (MirrorDiag P) = MirrorDiag (NormalizeY P) := by
  unfold NormalizeX NormalizeY
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 H1 <;> unfold MirrorDiag at * <;> simp at *
  . unfold MirrorY; simp at *
    omega
  . unfold MirrorX; simp at *
    omega
  . unfold MirrorY; simp at *
    unfold MirrorX; simp at *

theorem NormalizeYMirrorDiag {N} (P: Position N): NormalizeY (MirrorDiag P) = MirrorDiag (NormalizeX P) := by
  unfold NormalizeX NormalizeY
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 H1 <;> unfold MirrorDiag at * <;> simp at *
  . unfold MirrorX; simp at *
    omega
  . unfold MirrorY; simp at *
    omega
  . unfold MirrorX; simp at *
    unfold MirrorY; simp at *

theorem NormalizeXNormalizeY {N} (P: Position N): NormalizeX (NormalizeY P) = NormalizeY (NormalizeX P) := by
  unfold NormalizeX NormalizeY
  cases P; rename_i WKx WKy WRx WRy BKx BKy Turn DC
  obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
  split_ifs with H H0 H1 H2 H3 H4 H5 H6 <;> simp at *
  · unfold MirrorX MirrorY at *; simp at *
    clear H0
    omega
  . unfold MirrorX MirrorY at *; simp at *
    have H5: WKx = N - 1 - WKx ∧ WRx = N - 1 - WRx ∧ BKx = N - 1 - BKx := by
      clear H H4
      omega
    have H6: N - 1 - WKy = WKy ∧ N - 1 - WRy = WRy ∧ N - 1 - BKy = BKy := by
      clear H2 H3 H5
      omega
    clear H2 H4 H H3
    tauto
  · unfold MirrorX MirrorY at *; simp at *
    clear H H4
    omega
  · unfold MirrorX MirrorY at *; simp at *
    clear H
    omega
  . unfold MirrorX MirrorY at *; simp at *
    clear H2 H5
    omega
  · unfold MirrorX MirrorY at *; simp at *


theorem SamePositionAndNormalize {N} (P1 P2: Position N): SamePosition P1 P2 ↔ Normalize P1 = Normalize P2 := by
  constructor
  . intro H
    unfold SamePosition at H
    obtain H | H | H | H | H | H | H | H := H <;> rw [H] <;> clear H P1
    . unfold Normalize
      congr 2
      apply NormalizeXMirrorX
    . unfold Normalize
      congr 1
      rw [NormalizeXMirrorY]
      rw [NormalizeYMirrorY]
    . unfold Normalize
      congr 1
      rw [<- MirrorXYSwap]
      rw [NormalizeXMirrorX]
      rw [NormalizeXMirrorY]
      rw [NormalizeYMirrorY]
    . unfold Normalize
      rw [NormalizeXMirrorDiag]
      rw [NormalizeYMirrorDiag]
      rw [NormalizeDiagMirrorDiag]
      rw [NormalizeXNormalizeY]
    . unfold Normalize
      rw [NormalizeXMirrorDiag]
      rw [NormalizeYMirrorDiag]
      rw [NormalizeDiagMirrorDiag]
      rw [NormalizeXNormalizeY]
      rw [NormalizeXMirrorX]
    . unfold Normalize
      rw [NormalizeXMirrorDiag]
      rw [NormalizeYMirrorDiag]
      rw [NormalizeDiagMirrorDiag]
      rw [NormalizeYMirrorY]
      rw [NormalizeXNormalizeY]
    . unfold Normalize
      rw [NormalizeXMirrorDiag]
      rw [NormalizeYMirrorDiag]
      rw [NormalizeDiagMirrorDiag]
      rw [NormalizeYMirrorY]
      rw [NormalizeXNormalizeY]
      rw [NormalizeXMirrorX]
  . intro H
    unfold SamePosition
    unfold Normalize at *
    unfold NormalizeX at *
    unfold NormalizeY at *
    unfold NormalizeDiag at *
    split at H <;> (rename_i H0; clear H0) <;>
    split at H <;> (rename_i H0; clear H0) <;>
    split at H <;> (rename_i H0; clear H0) <;>
    split at H <;> (rename_i H0; clear H0) <;>
    split at H <;> (rename_i H0; clear H0) <;>
    split at H <;> (rename_i H0; clear H0)
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorDiagTwice P1, <- MirrorDiagTwice P2]
        rw [H]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorDiagTwice P1]
        rw [H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- MirrorDiagTwice P1]
        rw [H]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- MirrorDiagTwice P1]
        rw [H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- MirrorDiagTwice P1]
        rw [H]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- MirrorDiagTwice P1]
        rw [H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorYTwice P1]
        rw [H]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- MirrorYTwice P1]
        rw [H]
        rw [MirrorDiagXSwap]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorYTwice P1]
        rw [H]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- MirrorYTwice P1]
        rw [H]
        rw [MirrorDiagYSwap (MirrorX P2)]
        rw [MirrorDiagXSwap]
        rw [MirrorXYSwap]
        rw [MirrorDiagYSwap]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- MirrorYTwice P1]
        rw [H]
      tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- MirrorYTwice P1]
        rw [H]
        rw [MirrorDiagXSwap]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- MirrorYTwice P1]
        rw [H]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- MirrorYTwice P1]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- H]
        rw [MirrorDiagYSwap]
        rw [MirrorXTwice]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorYTwice P1]
        rw [<- MirrorDiagTwice (MirrorY P1)]
        rw [H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- MirrorYTwice P1]
        rw [<- MirrorDiagTwice (MirrorY P1)]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [MirrorXYSwap]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorYTwice P1]
        rw [<- MirrorDiagTwice (MirrorY P1)]
        rw [H]
        rw [MirrorDiagTwice]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- MirrorXTwice P2]
        rw [<- H]
        rw [MirrorDiagYSwap]
        rw [MirrorXTwice]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- MirrorYTwice P1]
        rw [<- MirrorDiagTwice (MirrorY P1)]
        rw [H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- MirrorYTwice P1]
        rw [<- MirrorDiagTwice (MirrorY P1)]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- MirrorYTwice P1]
        rw [<- MirrorDiagTwice (MirrorY P1)]
        rw [H]
        rw [MirrorDiagTwice]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- H]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [MirrorDiagYSwap]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [MirrorXYSwap]
      tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [MirrorDiagYSwap]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [<- MirrorDiagYSwap (MirrorX P2)]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- MirrorXTwice P1]
        rw [H]
        rw [<- MirrorDiagYSwap]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorDiagTwice (MirrorX P1)]
        rw [H]
        rw [MirrorDiagYSwap]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorDiagTwice (MirrorX P1)]
        rw [H]
        rw [MirrorDiagTwice]
      tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- MirrorYTwice P2]
        rw [<- H]
        rw [MirrorDiagYSwap]
        rw [MirrorDiagTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorDiagTwice (MirrorX P1)]
        rw [H]
        rw [MirrorDiagTwice]
        rw [MirrorXYSwap]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- H]
        rw [MirrorDiagYSwap]
        rw [MirrorDiagTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorDiagTwice (MirrorX P1)]
        rw [H]
        rw [MirrorDiagTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorDiagTwice (MirrorX P1)]
        rw [H]
        rw [<- MirrorDiagYSwap]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorDiagTwice (MirrorX P1)]
        rw [H]
        rw [MirrorDiagTwice]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- H]
        rw [MirrorXYSwap]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorYTwice (MirrorX P1)]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [<- MirrorDiagYSwap]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- MirrorYTwice P2]
        rw [<- H]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorYTwice (MirrorX P1)]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [<- MirrorDiagYSwap]
        rw [MirrorXYSwap]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorXTwice P2]
        rw [<- H]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorYTwice (MirrorX P1)]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [<- MirrorDiagYSwap]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorYTwice (MirrorX P1)]
        rw [H]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorYTwice (MirrorX P1)]
        rw [H]
        rw [<- MirrorDiagXSwap]
        rw [<- MirrorDiagYSwap]
        rw [MirrorXYSwap]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY (MirrorX P2)) := by
        rw [<- H]
        rw [MirrorDiagYSwap]
        rw [MirrorDiagYSwap]
        rw [MirrorXTwice]
        rw [MirrorDiagTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorY (MirrorX P2) := by
        rw [<- MirrorDiagTwice P2]
        rw [<- H]
        rw [MirrorDiagTwice]
        rw [MirrorXYSwap]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorX P2) := by
        rw [<- MirrorYTwice P2]
        rw [<- H]
        rw [MirrorDiagXSwap]
        rw [MirrorDiagYSwap]
        rw [MirrorDiagTwice]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = MirrorX P2 := by
        rw [<- MirrorYTwice P2]
        rw [<- MirrorDiagTwice (MirrorY P2)]
        rw [<- H]
        rw [MirrorDiagTwice]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag (MirrorY P2) := by
        rw [<- MirrorXTwice P2]
        rw [<- H]
        rw [<- MirrorDiagYSwap]
        rw [<- MirrorDiagXSwap]
        rw [MirrorDiagTwice]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorY P2 := by
        rw [<- MirrorXTwice P2]
        rw [<- MirrorDiagTwice (MirrorX P2)]
        rw [<- H]
        rw [MirrorDiagTwice]
        rw [MirrorXYSwap]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto
    . have H0: P1 = MirrorDiag P2 := by
        rw [<- MirrorXTwice P2]
        rw [<- MirrorYTwice (MirrorX P2)]
        rw [<- H]
        rw [MirrorDiagXSwap]
        rw [MirrorDiagYSwap]
        rw [MirrorDiagTwice]
        rw [MirrorXYSwap]
        rw [MirrorXTwice]
        rw [MirrorYTwice]
      tauto
    . have H0: P1 = P2 := by
        rw [<- MirrorXTwice P1]
        rw [<- MirrorYTwice (MirrorX P1)]
        rw [<- MirrorDiagTwice (MirrorY (MirrorX P1))]
        rw [H]
        rw [MirrorDiagTwice]
        rw [MirrorYTwice]
        rw [MirrorXTwice]
      tauto


theorem NormalizedPositionIsSamePosition {N} (P: Position N):
  SamePosition (Normalize P) P := by
  unfold SamePosition
  unfold Normalize NormalizeX NormalizeY NormalizeDiag
  split <;> (rename_i H0; clear H0) <;>
  split <;> (rename_i H0; clear H0) <;>
  split <;> (rename_i H0; clear H0) <;>
  tauto
