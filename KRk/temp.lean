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
    . cases P2; rename_i WKx WKy WRx WRy BKx BKy Turn DC
      obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
      unfold MirrorX
      unfold Normalize
      congr 2
      unfold NormalizeX
      simp at *
      split <;> rename_i H
      . split <;> rename_i H0
        . simp at *
          obtain H | H := H
          . rw [tiny_omega _ _ DC5] at H
            obtain H0 | H0 := H0
            . exfalso
              omega
            . obtain ⟨H1, H2⟩ := H0
              exfalso
              clear H2
              omega
          . obtain ⟨H1, H2⟩ := H
            rw [tiny_omega _ _ DC5] at H1
            rw [tiny_omega _ _ DC1] at H2
            rw [tiny_omega _ _ DC3] at H2
            obtain H0 | H0 := H0
            . clear H2
              exfalso
              omega
            . obtain ⟨H3, H4⟩ := H0; clear H3
              obtain H2 | H2 := H2
              . obtain H4 | H4 := H4
                . clear H1
                  exfalso
                  omega
                . obtain ⟨H5, H6⟩ := H4
                  clear H1 H6
                  exfalso
                  omega
              . obtain ⟨H5, H6⟩ := H2
                obtain H4 | H4 := H4
                . clear H1 H6
                  exfalso
                  omega
                . obtain ⟨H7, H8⟩ := H4
                  omega
        . unfold MirrorX
          simp at *
      . split <;> rename_i H0
        . unfold MirrorX
          simp at *
          rw [tiny_omega _ _ DC1]
          rw [tiny_omega _ _ DC3]
          rw [tiny_omega _ _ DC5]
          simp
        . unfold MirrorX
          simp at *
          rw [tiny_omega _ _ DC5] at *
          rw [tiny_omega _ _ DC1] at *
          rw [tiny_omega _ _ DC3] at *
          obtain ⟨H1, H2⟩ := H
          obtain ⟨H3, H4⟩ := H0
          have H5: BKx = N - 1 - BKx := by
            clear H2 H4
            omega
          clear H1 H3
          have H6 := H4 H5; clear H4
          have H7: N - 1 - BKx = BKx := by (apply tiny_omega_0; assumption)
          have H8 := H2 H7; clear H2 H7
          obtain ⟨H9, H10⟩ := H6
          obtain ⟨H11, H12⟩ := H8
          have H13: WKx = N - 1 - WKx := by (clear H5 H10 H12; omega)
          clear H9 H11
          have H14 := H10 H13; clear H10
          have H15: N - 1 - WKx = WKx := by (apply tiny_omega_0; assumption)
          have H16 := H12 H15; clear H12
          clear H5 H13 H15
          exfalso
          omega
    . cases P2; rename_i WKx WKy WRx WRy BKx BKy Turn DC
      obtain ⟨DC1, DC2, DC3, DC4, DC5, DC6⟩ := DC
      unfold Normalize
      congr 1
      unfold NormalizeY
      unfold MirrorY
      simp
      split <;> rename_i H
      . split <;> rename_i H0
        . unfold NormalizeX at *
          unfold MirrorX at *
          simp at *
          split <;> rename_i H1
          . simp at *
            split at H <;> rename_i H2
            . split at H0 <;> rename_i H3
              . simp at *
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC2] at H
                rw [tiny_omega _ _ DC4] at H
                clear H1 H2 H3
                obtain H | H := H
                . obtain H0 | H0 := H0
                  . exfalso
                    omega
                  . obtain ⟨H1, H2⟩ := H0
                    clear H2
                    exfalso
                    omega
                . obtain ⟨H1, H2⟩ := H
                  obtain H0 | H0 := H0
                  . clear H2
                    exfalso
                    omega
                  . obtain ⟨H3, H4⟩ := H0
                    clear H3
                    obtain H2 | H2 := H2
                    . obtain H4 | H4 := H4
                      . clear H1
                        exfalso
                        omega
                      . obtain ⟨H5, H6⟩ := H4
                        clear H1 H6
                        exfalso
                        omega
                    . obtain H4 | H4 := H4
                      . obtain ⟨H5, H6⟩ := H2
                        clear H1 H6
                        exfalso
                        omega
                      . obtain ⟨H5, H6⟩ := H2
                        obtain ⟨H7, H8⟩ := H4
                        clear H7
                        have H9: N - 1 - WRy = WRy := by
                          clear H1 H5
                          omega
                        trivial
              . simp at *
                clear H1
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC2] at H
                rw [tiny_omega _ _ DC4] at H
                obtain ⟨H4, H5⟩ := H3
                obtain H2 | H2 := H2
                . clear H H0 H5
                  exfalso
                  omega
                . obtain ⟨H6, H7⟩ := H2
                  have H8 := H5 H6; clear H5
                  obtain ⟨H9, H10⟩ := H8
                  obtain H7 | H7 := H7
                  . clear H H0 H10 H4 H6
                    exfalso
                    omega
                  . clear H4
                    obtain ⟨H11, H12⟩ := H7
                    have H13 := H10 H11; clear H10
                    clear H H0 H6 H9 H11
                    exfalso
                    omega
            . split at H0 <;> rename_i H3
              . simp at *
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC4] at H
                rw [tiny_omega _ _ DC2] at H
                obtain ⟨H4, H5⟩ := H2
                obtain H1 | H1 := H1
                . clear H H3 H0 H5
                  exfalso
                  omega
                . obtain ⟨H6, H7⟩ := H1
                  have H8 := H5 H6; clear H5
                  obtain ⟨H9, H10⟩ := H8
                  obtain H7 | H7 := H7
                  . clear H H3 H0 H4 H6 H10
                    exfalso
                    omega
                  . obtain ⟨H11, H12⟩ := H7
                    have H13 := H10 H11; clear H10
                    clear H11 H9 H6 H4 H0 H3 H
                    exfalso
                    omega
              . simp at *
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC4] at H
                rw [tiny_omega _ _ DC2] at H
                clear H2
                obtain ⟨H4, H5⟩ := H3
                obtain H1 | H1 := H1
                . clear H H0 H5
                  exfalso
                  omega
                . obtain ⟨H6, H7⟩ := H1
                  have H8 := H5 H6; clear H5
                  obtain ⟨H9, H10⟩ := H8
                  clear H4
                  obtain H7 | H7 := H7
                  . clear H10 H6 H H0
                    exfalso
                    omega
                  . obtain ⟨H11, H12⟩ := H7
                    clear H9
                    have H13 := H10 H11; clear H10
                    clear H H0 H6 H11
                    exfalso
                    omega
          . split at H <;> rename_i H2
            . split at H0 <;> rename_i H3
              . simp at *
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC4] at H
                rw [tiny_omega _ _ DC2] at H
                clear H3
                obtain ⟨H3, H4⟩ := H1
                obtain H2 | H2 := H2
                . clear H H0 H4
                  exfalso
                  omega
                . obtain ⟨H5, H6⟩ := H2
                  have H7 := H4 H5; clear H4
                  clear H3
                  obtain ⟨H8, H9⟩ := H7
                  obtain H6 | H6 := H6
                  . clear H9 H5 H0 H
                    exfalso
                    omega
                  . obtain ⟨H10, H11⟩ := H6
                    have H12 := H9 H10; clear H9
                    clear H10 H8 H5 H0 H
                    exfalso
                    omega
              . simp at *
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC4] at H
                rw [tiny_omega _ _ DC2] at H
                clear H3
                obtain ⟨H3, H4⟩ := H1
                obtain H2 | H2 := H2
                . clear H H0 H4
                  exfalso
                  omega
                . obtain ⟨H5, H6⟩ := H2
                  have H7 := H4 H5; clear H4
                  clear H3
                  obtain ⟨H8, H9⟩ := H7
                  obtain H6 | H6 := H6
                  . clear H9 H5 H0 H
                    exfalso
                    omega
                  . obtain ⟨H10, H11⟩ := H6
                    have H12 := H9 H10; clear H9
                    clear H10 H8 H5 H0 H
                    exfalso
                    omega
            . split at H0 <;> rename_i H3
              . simp at *
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC4] at H
                rw [tiny_omega _ _ DC2] at H
                clear H2
                obtain ⟨H4, H5⟩ := H1
                obtain H3 | H3 := H3
                . clear H H0 H5
                  exfalso
                  omega
                . obtain ⟨H6, H7⟩ := H3
                  clear H4
                  have H8 := H5 H6; clear H5
                  obtain ⟨H9, H10⟩ := H8
                  obtain H7 | H7 := H7
                  . clear H H0 H6 H10
                    exfalso
                    omega
                  . obtain ⟨H11, H12⟩ := H7
                    have H13 := H10 H11; clear H10
                    clear H H0 H6 H9 H11
                    exfalso
                    omega
              . simp at *
                clear H1 H2 H3
                rw [tiny_omega _ _ DC6] at H
                rw [tiny_omega _ _ DC4] at H
                rw [tiny_omega _ _ DC2] at H
                obtain H | H := H
                . obtain H0 | H0 := H0
                  . exfalso
                    omega
                  . obtain ⟨H1, H2⟩ := H0
                    clear H2
                    exfalso
                    omega
                . obtain ⟨H1, H2⟩ := H
                  obtain H0 | H0 := H0
                  . exfalso
                    clear H2
                    omega
                  . obtain ⟨H3, H4⟩ := H0
                    clear H3
                    obtain H2 | H2 := H2
                    . obtain H4 | H4 := H4
                      . clear H1
                        exfalso
                        omega
                      . obtain ⟨H5, H6⟩ := H4
                        clear H1 H6
                        exfalso
                        omega
                    . obtain ⟨H5, H6⟩ := H2
                      obtain H4 | H4 := H4
                      . clear H1 H6
                        exfalso
                        omega
                      . obtain ⟨H7, H8⟩ := H4
                        have H9: N - 1 - WRy = WRy := by
                          clear H1 H5 H7
                          omega
                        trivial
        . simp at *
          unfold NormalizeX at *
          simp at *
          split <;> rename_i H1
          . simp at *
          . split at H <;> rename_i H2
            . simp at *
              split at H0 <;> rename_i H3
              . unfold MirrorX
                simp at *
              . unfold MirrorX
                simp at *
            . split at H0 <;> rename_i H3
              . unfold MirrorX at *
                simp at *
              . unfold MirrorX at *
                simp at *
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
