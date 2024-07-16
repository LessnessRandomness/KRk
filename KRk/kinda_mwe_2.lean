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

def NormalizeX {N} (P: Position N): Position N :=
  if P.BKx < N - 1 - P.BKx ∨ P.BKx = N - 1 - P.BKx ∧ (P.WKx < N - 1 - P.WKx ∨ P.WKx = N - 1 - P.WKx ∧ P.WRx <= N - 1 - P.WRx)
  then P
  else MirrorX P

def NormalizeY {N} (P: Position N): Position N :=
  if P.BKy < N - 1 - P.BKy ∨ P.BKy = N - 1 - P.BKy ∧ (P.WKy < N - 1 - P.WKy ∨ P.WKy = N - 1 - P.WKy ∧ P.WRy <= N - 1 - P.WRy)
  then P
  else MirrorY P

theorem aux {N} (P: Position N): NormalizeY (NormalizeX (MirrorY P)) = NormalizeY (NormalizeX P) := by
  unfold NormalizeX
  split <;> split <;> try simp at *
  . sorry
  . unfold MirrorY at *
    simp at *
    unfold MirrorX at *
    unfold NormalizeY at *
    split <;> split <;> simp at *
    . omega
    . cases P
      simp at *
      omega
    . cases P
      simp at *
      omega
    . sorry
  . sorry
  . sorry
