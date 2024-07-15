import KRk.MoveGeneration

instance: ∀ {N} (P: Position N) (H: LegalPosition P) (H0: P.Turn = Black), Decidable (Checkmate P) := by
  intros N P H H0
  unfold Checkmate
  have dec: Decidable (∀ P', ¬ LegalBlackMove P P') := by
    have dec0: Decidable (AllBlackKingMoves P = List.nil) := by
      generalize (AllBlackKingMoves P) = W
      cases W
      . right
        simp
      . left
        simp
    by_cases H1:(AllBlackKingMoves P = List.nil)
    . have H2: ∀ P', P' ∉ AllBlackKingMoves P := by
        rw [H1]
        simp
      have H3: ∀ P', ¬ LegalBlackMove P P' := by
        intros P' H3
        rw [AllBlackKingMovesCorrect P H H0] at H3
        apply (H2 P' H3)
      right
      assumption
    . have H2: ¬ ∀ P', P' ∉ AllBlackKingMoves P := by
        intro H2
        apply H1
        clear H1
        generalize (AllBlackKingMoves P) = W at *
        cases W
        . simp
        . exfalso
          apply H2
          . simp
            left
            rfl
      clear H1
      have H3: ¬ ∀ P', ¬ LegalBlackMove P P' := by
        intro H3
        apply H2
        clear H2
        intros P' H4
        apply (H3 P')
        rw [AllBlackKingMovesCorrect P H H0]
        assumption
      left
      assumption
  infer_instance

instance: ∀ {N} (P: Position N) (H: LegalPosition P) (H0: P.Turn = Black), Decidable (Stalemate P) := by
  intros N P H H0
  unfold Stalemate
  have dec: Decidable (∀ P', ¬ LegalBlackMove P P') := by
    have dec0: Decidable (AllBlackKingMoves P = List.nil) := by
      generalize (AllBlackKingMoves P) = W
      cases W
      . right
        simp
      . left
        simp
    by_cases H1:(AllBlackKingMoves P = List.nil)
    . have H2: ∀ P', P' ∉ AllBlackKingMoves P := by
        rw [H1]
        simp
      have H3: ∀ P', ¬ LegalBlackMove P P' := by
        intros P' H3
        rw [AllBlackKingMovesCorrect P H H0] at H3
        apply (H2 P' H3)
      right
      assumption
    . have H2: ¬ ∀ P', P' ∉ AllBlackKingMoves P := by
        intro H2
        apply H1
        clear H1
        generalize (AllBlackKingMoves P) = W at *
        cases W
        . simp
        . exfalso
          apply H2
          . simp
            left
            rfl
      clear H1
      have H3: ¬ ∀ P', ¬ LegalBlackMove P P' := by
        intro H3
        apply H2
        clear H2
        intros P' H4
        apply (H3 P')
        rw [AllBlackKingMovesCorrect P H H0]
        assumption
      left
      assumption
  infer_instance
