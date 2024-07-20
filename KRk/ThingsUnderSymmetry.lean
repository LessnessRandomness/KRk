import KRk.Symmetries
import KRk.MoveGeneration

namespace SamePosition

  theorem NotOnSameSquareAux {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    NotOnSameSquare P1 → NotOnSameSquare P2 := by
    unfold NotOnSameSquare
    intro H0
    obtain H | H | H | H | H | H | H | H := H <;> cases H
    . omega
    . cases P2; unfold MirrorX at *; simp at *
      omega
    . cases P2; unfold MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorX MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorDiag at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorX at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorY MirrorX at *; simp at *
      omega

  theorem NotOnSameSquareIff {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    NotOnSameSquare P1 ↔ NotOnSameSquare P2 := by
    constructor
    . apply (NotOnSameSquareAux _ _ H)
    . rw [SamePositionSymm] at H
      apply (NotOnSameSquareAux _ _ H)

  theorem NotKingNextToKingAux {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    NotKingNextToKing P1 → NotKingNextToKing P2 := by
    unfold NotKingNextToKing
    intro H0
    obtain H | H | H | H | H | H | H | H := H <;> cases H
    . omega
    . cases P2; unfold MirrorX at *; simp at *
      omega
    . cases P2; unfold MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorX MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorDiag at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorX at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorY MirrorX at *; simp at *
      omega

  theorem NotKingNextToKingIff {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    NotKingNextToKing P1 ↔ NotKingNextToKing P2 := by
    constructor
    . apply (NotKingNextToKingAux _ _ H)
    . rw [SamePositionSymm] at H
      apply (NotKingNextToKingAux _ _ H)

  theorem BlackKingAttackedAux {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    BlackKingAttacked P1 → BlackKingAttacked P2 := by
    unfold BlackKingAttacked Between
    intro H0
    obtain H | H | H | H | H | H | H | H := H <;> cases H
    . omega
    . cases P2; unfold MirrorX at *; simp at *
      omega
    . cases P2; unfold MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorX MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorDiag at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorX at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorY at *; simp at *
      omega
    . cases P2; unfold MirrorDiag MirrorY MirrorX at *; simp at *
      omega

  theorem BlackKingAttackedIff {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    BlackKingAttacked P1 ↔ BlackKingAttacked P2 := by
    constructor
    . apply (BlackKingAttackedAux _ _ H)
    . rw [SamePositionSymm] at H
      apply (BlackKingAttackedAux _ _ H)

  theorem TurnEq {N} (P1 P2: Position N) (H: SamePosition P1 P2): P1.Turn = P2.Turn := by
    obtain H | H | H | H | H | H | H | H := H <;> cases H
    . simp
    . cases P2
      unfold MirrorX
      simp
    . cases P2
      unfold MirrorY
      simp
    . cases P2
      unfold MirrorX MirrorY
      simp
    . cases P2
      unfold MirrorDiag
      simp
    . cases P2
      unfold MirrorDiag MirrorX
      simp
    . cases P2
      unfold MirrorDiag MirrorY
      simp
    . cases P2
      unfold MirrorDiag MirrorY MirrorX
      simp

  theorem LegalPositionIff {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    LegalPosition P1 ↔ LegalPosition P2 := by
    unfold LegalPosition
    rw [NotOnSameSquareIff _ _ H]
    rw [NotKingNextToKingIff _ _ H]
    rw [TurnEq _ _ H]
    rw [BlackKingAttackedIff _ _ H]

  theorem MoveBlackKingMirrorX {N} (P1 P2: Position N):
    MoveBlackKing P1 P2 → MoveBlackKing (MirrorX P1) (MirrorX P2) := by
    intros H
    cases P1
    cases P2
    unfold MoveBlackKing MirrorX at *
    simp at *
    omega

  theorem MoveBlackKingMirrorY {N} (P1 P2: Position N):
    MoveBlackKing P1 P2 → MoveBlackKing (MirrorY P1) (MirrorY P2) := by
    intros H
    cases P1
    cases P2
    unfold MoveBlackKing MirrorY at *
    simp at *
    omega

  theorem MoveBlackKingMirrorDiag {N} (P1 P2: Position N):
    MoveBlackKing P1 P2 → MoveBlackKing (MirrorDiag P1) (MirrorDiag P2) := by
    intros H
    cases P1
    cases P2
    unfold MoveBlackKing MirrorDiag at *
    simp at *
    omega

  theorem OtherAfterMoveBlackKingMirrorX {N} (P1 P2: Position N):
    OtherAfterMoveBlackKing P1 P2 → OtherAfterMoveBlackKing (MirrorX P1) (MirrorX P2) := by
    intros H
    cases P1
    cases P2
    unfold OtherAfterMoveBlackKing MirrorX at *
    simp at *
    omega

  theorem OtherAfterMoveBlackKingMirrorY {N} (P1 P2: Position N):
    OtherAfterMoveBlackKing P1 P2 → OtherAfterMoveBlackKing (MirrorY P1) (MirrorY P2) := by
    intros H
    cases P1
    cases P2
    unfold OtherAfterMoveBlackKing MirrorY at *
    simp at *
    omega

  theorem OtherAfterMoveBlackKingMirrorDiag {N} (P1 P2: Position N):
    OtherAfterMoveBlackKing P1 P2 → OtherAfterMoveBlackKing (MirrorDiag P1) (MirrorDiag P2) := by
    intros H
    cases P1
    cases P2
    unfold OtherAfterMoveBlackKing MirrorDiag at *
    simp at *
    omega

  theorem LegalBlackMoveMirrorX {N} (P1 P2: Position N):
    LegalBlackMove P1 P2 → LegalBlackMove (MirrorX P1) (MirrorX P2) := by
    intros H
    obtain ⟨H1, H2, H3, H4, H5, H6⟩ := H
    have H: ∀ (P: Position N), SamePosition P (MirrorX P) := by
      intro P
      rw [SamePositionSymm]
      unfold SamePosition
      tauto
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    . apply MoveBlackKingMirrorX
      assumption
    . apply OtherAfterMoveBlackKingMirrorX
      assumption
    . cases P1; unfold MirrorX; simp at *
      assumption
    . cases P2; unfold MirrorX; simp at *
      assumption
    . rw [<- LegalPositionIff _ _ (H P1)]
      assumption
    . rw [<- LegalPositionIff _ _ (H P2)]
      assumption

   theorem LegalBlackMoveMirrorY {N} (P1 P2: Position N):
    LegalBlackMove P1 P2 → LegalBlackMove (MirrorY P1) (MirrorY P2) := by
    intros H
    obtain ⟨H1, H2, H3, H4, H5, H6⟩ := H
    have H: ∀ (P: Position N), SamePosition P (MirrorY P) := by
      intro P
      rw [SamePositionSymm]
      unfold SamePosition
      tauto
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    . apply MoveBlackKingMirrorY
      assumption
    . apply OtherAfterMoveBlackKingMirrorY
      assumption
    . cases P1; unfold MirrorY; simp at *
      assumption
    . cases P2; unfold MirrorY; simp at *
      assumption
    . rw [<- LegalPositionIff _ _ (H P1)]
      assumption
    . rw [<- LegalPositionIff _ _ (H P2)]
      assumption

  theorem LegalBlackMoveMirrorDiag {N} (P1 P2: Position N):
    LegalBlackMove P1 P2 → LegalBlackMove (MirrorDiag P1) (MirrorDiag P2) := by
    intros H
    obtain ⟨H1, H2, H3, H4, H5, H6⟩ := H
    have H: ∀ (P: Position N), SamePosition P (MirrorDiag P) := by
      intro P
      rw [SamePositionSymm]
      unfold SamePosition
      tauto
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    . apply MoveBlackKingMirrorDiag
      assumption
    . apply OtherAfterMoveBlackKingMirrorDiag
      assumption
    . cases P1; unfold MirrorDiag; simp at *
      assumption
    . cases P2; unfold MirrorDiag; simp at *
      assumption
    . rw [<- LegalPositionIff _ _ (H P1)]
      assumption
    . rw [<- LegalPositionIff _ _ (H P2)]
      assumption

  theorem CheckmateAux {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    Checkmate P1 → Checkmate P2 := by
    unfold Checkmate
    intro H0
    obtain ⟨H1, H2, H3, H4⟩ := H0
    refine ⟨?_, ?_, ?_, ?_⟩
    . rw [LegalPositionIff _ _ H] at H1
      assumption
    . rw [BlackKingAttackedIff _ _ H] at H2
      assumption
    . rw [TurnEq _ _ H] at H3
      assumption
    . clear H1 H2 H3
      intros P'
      obtain H | H | H | H | H | H | H | H := H <;> cases H
      . apply H4
      . have H5 := H4 (MirrorX P')
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorX
        assumption
      . have H5 := H4 (MirrorY P')
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorY
        assumption
      . have H5 := H4 (MirrorY (MirrorX P'))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorY
        apply LegalBlackMoveMirrorX
        assumption
      . have H5 := H4 (MirrorDiag P')
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        assumption
      . have H5 := H4 (MirrorDiag (MirrorX P'))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        apply LegalBlackMoveMirrorX
        assumption
      . have H5 := H4 (MirrorDiag (MirrorY P'))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        apply LegalBlackMoveMirrorY
        assumption
      . have H5 := H4 (MirrorDiag (MirrorY (MirrorX P')))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        apply LegalBlackMoveMirrorY
        apply LegalBlackMoveMirrorX
        assumption

  theorem CheckmateIff {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    Checkmate P1 ↔ Checkmate P2 := by
    constructor
    . apply (CheckmateAux _ _ H)
    . rw [SamePositionSymm] at H
      apply (CheckmateAux _ _ H)

  theorem StalemateAux {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    Stalemate P1 → Stalemate P2 := by
    unfold Stalemate
    intro H0
    obtain ⟨H1, H2, H3, H4⟩ := H0
    refine ⟨?_, ?_, ?_, ?_⟩
    . rw [LegalPositionIff _ _ H] at H1
      assumption
    . rw [BlackKingAttackedIff _ _ H] at H2
      assumption
    . rw [TurnEq _ _ H] at H3
      assumption
    . clear H1 H2 H3
      intros P'
      obtain H | H | H | H | H | H | H | H := H <;> cases H
      . apply H4
      . have H5 := H4 (MirrorX P')
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorX
        assumption
      . have H5 := H4 (MirrorY P')
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorY
        assumption
      . have H5 := H4 (MirrorY (MirrorX P'))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorY
        apply LegalBlackMoveMirrorX
        assumption
      . have H5 := H4 (MirrorDiag P')
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        assumption
      . have H5 := H4 (MirrorDiag (MirrorX P'))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        apply LegalBlackMoveMirrorX
        assumption
      . have H5 := H4 (MirrorDiag (MirrorY P'))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        apply LegalBlackMoveMirrorY
        assumption
      . have H5 := H4 (MirrorDiag (MirrorY (MirrorX P')))
        clear H4; intro H; apply H5; clear H5
        apply LegalBlackMoveMirrorDiag
        apply LegalBlackMoveMirrorY
        apply LegalBlackMoveMirrorX
        assumption

  theorem StalemateIff {N} (P1 P2: Position N) (H: SamePosition P1 P2):
    Stalemate P1 ↔ Stalemate P2 := by
    constructor
    . apply (StalemateAux _ _ H)
    . rw [SamePositionSymm] at H
      apply (StalemateAux _ _ H)

end SamePosition
