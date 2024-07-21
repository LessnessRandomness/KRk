import KRk.Definitions
import KRk.ThingsUnderSymmetry

def StalemateType1 {N} (P: Position N) (Hn: 3 ≤ N) :=
  P.Turn = Black ∧
  P.BKx = 0 ∧ P.BKy = 0 ∧
  P.WRx = 1 ∧ P.WRy = 1 ∧
  P.WKx = 2 ∧ (P.WKy = 0 ∨ P.WKy = 1 ∨ P.WKy = 2)

def StalemateType2 {N} (P: Position N) (Hn: 3 ≤ N) :=
  P.Turn = Black ∧
  P.BKx = 0 ∧ P.BKy = 0 ∧
  P.WKx = 2 ∧ P.WKy = 0 ∧
  2 ≤ P.WRx ∧ P.WRy = 1

def NormalizeProp {N} (P: Position N) :=
  P.BKx ≤ N - 1 - P.BKx ∧ P.BKy ≤ N - 1 - P.BKy ∧
  (P.BKy < P.BKx ∨ P.BKy = P.BKx ∧ (P.WKy < P.WKx ∨ P.WKy = P.WKx ∧ P.WRy ≤ P.WRx))

theorem NormalizePropThm {N} (P: Position N): NormalizeProp (Normalize P) := by
  cases P
  unfold Normalize
  unfold NormalizeProp
  unfold NormalizeX
  split_ifs at *
  · unfold NormalizeY
    split_ifs at *
    . unfold NormalizeDiag
      split_ifs at *
      . simp at *; omega
      . unfold MirrorDiag at *; simp at *; omega
    . unfold NormalizeDiag
      split_ifs at *
      . unfold MirrorY at *; simp at *; omega
      . unfold MirrorY MirrorDiag at *; simp at *; omega
  · unfold NormalizeY
    split_ifs at *
    . unfold NormalizeDiag
      split_ifs at *
      . unfold MirrorX at *; simp at *; omega
      . unfold MirrorX MirrorDiag at *; simp at *; omega
    . unfold NormalizeDiag
      split_ifs at *
      . unfold MirrorX MirrorY at *; simp at *; omega
      . unfold MirrorX MirrorY MirrorDiag at *; simp at *; omega

syntax "BKmove" term:max term:max term:max : tactic

macro_rules
| `(tactic| BKmove $H:term $BKx:term $BKy:term) => set_option hygiene false in `(tactic|
          exfalso;
          apply ($H (Position.mk WKx WKy WRx WRy $BKx $BKy White (by omega)));
          unfold LegalBlackMove; simp at *;
          refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩⟩ <;>
          [ (unfold MoveBlackKing; simp at *; omega);
            (unfold OtherAfterMoveBlackKing; simp at *);
            assumption;
            (unfold NotOnSameSquare BlackKingAttacked Between at *; simp at *; omega);
            (unfold NotKingNextToKing; simp at *; omega);
            (simp at *; omega);
            (unfold BlackKingAttacked Between at *; simp at *; omega);
            (unfold NotOnSameSquare at *; simp at *; unfold White Black; omega);
            (unfold NotKingNextToKing; simp at *; omega);
            (unfold White; simp at *);
            (unfold BlackKingAttacked Between at *; simp at *; omega)])


theorem StalemateAllTypes {N} (P: Position N) (Hn: 3 ≤ N):
  Stalemate P ↔ (StalemateType1 (Normalize P) Hn ∨ StalemateType2 (Normalize P) Hn) := by
  have H: SamePosition P (Normalize P) := by
    rw [SamePositionSymm]
    apply NormalizedPositionIsSamePosition
  constructor
  . intros H0
    rw [SamePosition.StalemateIff _ _ H] at H0
    clear H
    have H := NormalizePropThm P
    unfold NormalizeProp at H
    revert H H0
    generalize (Normalize P) = W
    cases W; rename_i WKx WKy WRx WRy BKx BKy Turn DC; simp at *
    intros H H0 H1 H2
    unfold Stalemate at H
    obtain ⟨⟨H3, H4, H5, H6⟩, H8, H9, H10⟩ := H; simp at *
    have H11: BKx = 0 ∨ 1 ≤ BKx := by omega
    have H12: BKy = 0 ∨ 1 ≤ BKy := by omega
    obtain H11 | H11 := H11 <;> obtain H12 | H12 := H12
    . have H13: WKx = 2 ∧ (WKy = 0 ∨ WKy = 1 ∨ WKy = 2) ∨ 3 ≤ WKx := by
        unfold NotKingNextToKing at H4; simp at H4
        omega
      obtain ⟨H13, (H14 | H14 | H14)⟩ | H13 := H13
      . have H15: WRy = 0 ∧ 3 ≤ WRx ∨ WRy = 1 ∧ 1 ≤ WRx ∨ 2 ≤ WRy ∧ 1 ≤ WRx := by
          clear H6; unfold BlackKingAttacked Between NotOnSameSquare at *
          simp at *
          clear H4 H10
          omega
        obtain H15 | H15 | H15 := H15
        . BKmove H10 BKx (BKy + 1)
        . unfold StalemateType1 StalemateType2; simp; omega
        . BKmove H10 BKx (BKy + 1)
      . have H15: WRy = 1 ∧ (WRx = 1 ∨ 3 ≤ WRx) ∨ 2 ≤ WRy ∧ 1 ≤ WRx := by
          clear H6; unfold BlackKingAttacked Between NotOnSameSquare at *
          simp at *
          clear H4 H10
          omega
        obtain ⟨H16, H17 | H17⟩ | H15 := H15
        . unfold StalemateType1; simp at *; omega
        . BKmove H10 BKx (BKy + 1)
        . BKmove H10 BKx (BKy + 1)
      . have H15: WRy = 1 ∧ (WRx = 1 ∨ 2 ≤ WRx) ∨
                  WRy = 2 ∧ (WRx = 1 ∨ 3 ≤ WRx) ∨
                  3 ≤ WRy ∧ 1 ≤ WRx := by
          clear H6; unfold BlackKingAttacked NotOnSameSquare at *
          simp at *
          clear H4 H10
          omega
        obtain ⟨H16, H17 | H17⟩ | ⟨H16, H17 | H17⟩ | H15 := H15
        · unfold StalemateType1; simp at *; omega
        · BKmove H10 (BKx + 1) BKy
        · BKmove H10 BKx (BKy + 1)
        · BKmove H10 BKx (BKy + 1)
        · BKmove H10 BKx (BKy + 1)
      . have H15: (WRx = 1 ∨ WRx = 2) ∧ (WRy = 1 ∨ 2 ≤ WRy) ∨ 3 ≤ WRx := by
          unfold BlackKingAttacked Between NotOnSameSquare at *; simp at *; omega
        obtain ⟨H16 | H16, H17 | H17⟩| H15 := H15
        . BKmove H10 (BKx + 1) (BKy + 1)
        . BKmove H10 BKx (BKy + 1)
        . BKmove H10 (BKx + 1) BKy
        . BKmove H10 (BKx + 1) BKy
        . BKmove H10 (BKx + 1) BKy
    · sorry
    · sorry
    · sorry
  . sorry
