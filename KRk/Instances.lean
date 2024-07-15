import KRk.Definitions

instance: ∀ {N} (P: Position N), Decidable (NotOnSameSquare P) := by
  unfold NotOnSameSquare
  infer_instance

instance: ∀ {N} (P: Position N), Decidable (NotKingNextToKing P) := by
  unfold NotKingNextToKing
  infer_instance

instance: ∀ x y z, Decidable (Between x y z) := by
  unfold Between
  infer_instance

instance: ∀ {N} (P: Position N), Decidable (BlackKingAttacked P) := by
  unfold BlackKingAttacked
  infer_instance

instance: ∀ {N} (P: Position N), Decidable (LegalPosition P) := by
  unfold LegalPosition
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (MoveWhiteKing P1 P2) := by
  unfold MoveWhiteKing
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (OtherAfterMoveWhiteKing P1 P2) := by
  unfold OtherAfterMoveWhiteKing
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (LegalMoveWhiteKing P1 P2) := by
  unfold LegalMoveWhiteKing
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (MoveWhiteRook P1 P2) := by
  unfold MoveWhiteRook
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (OtherAfterMoveWhiteRook P1 P2) := by
  unfold OtherAfterMoveWhiteRook
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (LegalMoveWhiteRook P1 P2) := by
  unfold LegalMoveWhiteRook
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (LegalWhiteMove P1 P2) := by
  unfold LegalWhiteMove
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (MoveBlackKing P1 P2) := by
  unfold MoveBlackKing
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (OtherAfterMoveBlackKing P1 P2) := by
  unfold OtherAfterMoveBlackKing
  infer_instance

instance: ∀ {N} (P1 P2: Position N), Decidable (LegalBlackMove P1 P2) := by
  unfold LegalBlackMove
  infer_instance

instance: ∀ {N} (P: Position N), Decidable (InsufficientMaterial P) := by
  unfold InsufficientMaterial
  infer_instance
