/-
Tests of the TCP extension's trusted semantics (`Impl.lean`, `Deploy.lean`), outside the trust base:
for each row of `examples/net/semantics/doc.go`, an `example` that the outcome relations allow (or
exclude) the outcome the row's Go test measured (or the source it cites documents, or the row
assumes); the comment names the Go test. Excluded outcomes are tested as well: a timeout without a
deadline, a short successful write, data after the end's own close, a read past what was written.
-/
module

public import GooseLang.Ext.Tcp.Deploy

namespace Perennial
namespace Tcp

set_option linter.unusedSimpArgs false

/-! ## States -/

private def st0 : TcpEnd := TcpEnd.fresh
private def stR : TcpEnd := { TcpEnd.fresh with rdl := true }
private def stW : TcpEnd := { TcpEnd.fresh with wdl := true }
private def stC : TcpEnd := { TcpEnd.fresh with closed := true }
private def b3 : List w8 := [97, 98, 99]

/-! ## Laws the negative tests use -/

private theorem readAvail_bytes {st : TcpEnd} {d d' : TcpDir} {n : Nat} {bs : List w8}
    (h : ReadAvail st d n (.bytes bs) d') : bs.length ≤ n ∧ bs <+: d.bytes ∧ bs ≠ [] := by
  rcases h with ⟨k, h1, h2, h3, h4, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
    try cases h
  cases h4
  refine ⟨by rw [List.length_take]; omega, List.take_prefix _ _, ?_⟩
  intro he
  have := congrArg List.length he
  rw [List.length_take, List.length_nil] at this; omega

/-- What a read returns is a prefix of the unread bytes, at most `n` of them (no byte invented,
none past the oldest unread: in order, once). -/
private theorem readOutcome_bytes {st : TcpEnd} {d d' : TcpDir} {n : Nat} {bs : List w8}
    (h : ReadOutcome st d n (.bytes bs) d') : bs.length ≤ n ∧ bs <+: d.bytes := by
  unfold ReadOutcome at h
  split at h
  · cases h.1
  · split at h
    · obtain ⟨h, -⟩ := h; cases h; simp
    · rcases h with h | ⟨k, hk, h⟩
      · exact (readAvail_bytes h).imp_right And.left
      · obtain ⟨h1, h2, -⟩ := readAvail_bytes h
        exact ⟨h1, h2.trans (List.take_prefix _ _)⟩

private theorem readOutcome_timeout {st : TcpEnd} {d d' : TcpDir} {n : Nat}
    (h : ReadOutcome st d n (.err .timeout) d') : st.rdl = true := by
  unfold ReadOutcome at h
  split at h
  · cases h.1
  · split at h
    · cases h.1
    · rcases h with h | ⟨k, -, h⟩ <;>
      rcases h with ⟨_, _, _, _, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -, -⟩ <;>
        first | exact h | cases h

/-! ## Reads (D1) -/

/-- `TestReadPartial`: a read returns what arrived, the rest stays. -/
example : ReadOutcome st0 ⟨b3, .open⟩ 2 (.bytes [97]) ⟨[98, 99], .open⟩ := by
  unfold ReadOutcome
  simp only [st0, TcpEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (2 : Nat) ≠ 0 by decide]
  exact .inl (.inl ⟨1, by decide, by decide, by decide, rfl, rfl⟩)

/-- `TestReadPartial` (excluded): more than asked for. -/
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 1 (.bytes [97, 98]) ⟨[99], .open⟩ := fun h => by
  have := (readOutcome_bytes h).1; simp at this

/-- In-order delivery, no corruption (assumed): a read's bytes are the oldest unread ones. -/
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 3 (.bytes [98]) ⟨[97, 99], .open⟩ := fun h => by
  have := (readOutcome_bytes h).2; simp [b3] at this

/-- `TestReadEmptyBuffer`: an empty read returns nothing at once, even with a deadline set. -/
example : ReadOutcome stR ⟨b3, .open⟩ 0 (.bytes []) ⟨b3, .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, TcpEnd.fresh, b3]

/-- `TestReadEmptyBuffer` (excluded): an empty read does not time out or wait. -/
example : ¬ ReadOutcome stR ⟨b3, .open⟩ 0 (.err .timeout) ⟨b3, .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, TcpEnd.fresh, b3]
example : ¬ ReadOutcome st0 ⟨[], .open⟩ 0 .wait ⟨[], .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, TcpEnd.fresh, b3]

/-- `TestReadEOFAfterFin`, `TestKilledWriterFin`: EOF once nothing is unread after a FIN or a
break. -/
example : ReadOutcome st0 ⟨[], .fin⟩ 4 .eof ⟨[], .fin⟩ := by
  unfold ReadOutcome ReadAvail; simp [st0, TcpEnd.fresh]
example : ReadOutcome st0 ⟨b3, .open⟩ 4 .eof ⟨[], .cut⟩ := by
  unfold ReadOutcome
  simp only [st0, TcpEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (4 : Nat) ≠ 0 by decide]
  exact .inr ⟨0, by simp, .inr (.inl ⟨rfl, by decide, rfl, rfl⟩)⟩

/-- `TestResetCloseUnreadInput`, `TestResetLingerZero`, `TestKilledWithUnreadInput`: after a
reset, the bytes received, then an error (`sys`), then EOF. -/
example : ReadOutcome st0 ⟨[], .cut⟩ 4 (.err .sys) ⟨[], .cut⟩ := by
  unfold ReadOutcome ReadAvail; simp [st0, TcpEnd.fresh]

/-- `TestCloseTwice`, `TestCloseUnblocksRead`: a read on one's own closed end is `closed`, never
data. -/
example : ReadOutcome stC ⟨b3, .open⟩ 4 (.err .closed) ⟨b3, .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, TcpEnd.fresh, b3]
example : ¬ ReadOutcome stC ⟨b3, .open⟩ 4 (.bytes [97]) ⟨[98, 99], .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, TcpEnd.fresh, b3]

/-- `TestErrClosed`: a read of a live end is never `closed`. -/
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 4 (.err .closed) ⟨b3, .open⟩ := by
  unfold ReadOutcome ReadAvail
  simp [st0, TcpEnd.fresh]

/-- `TestReadDeadlineLosesNothing`: a timeout, with a read deadline, keeps the bytes; never
without a deadline. -/
example : ReadOutcome stR ⟨b3, .open⟩ 4 (.err .timeout) ⟨b3, .open⟩ := by
  unfold ReadOutcome ReadAvail; simp [stR, TcpEnd.fresh]
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 4 (.err .timeout) ⟨b3, .open⟩ := fun h => by
  have := readOutcome_timeout h; simp [st0, TcpEnd.fresh] at this

/-! ## Writes (D2, D15)

`WriteOutcome` is one step of a `Write` (one `write(2)`, with its wait); `conn.Write.impl` loops
over the steps and returns `(nn, nil)` only once they have counted every byte
(`net.Conn.Write.spec`'s post: `res = none → w = bs`), so a short successful `Write` is excluded
there, not here. -/

private theorem writeOutcome_timeout {st : TcpEnd} {d d' : TcpDir} {rs : List w8} {k : Nat}
    (h : WriteOutcome st d rs k (some .timeout) d') : st.wdl = true := by
  unfold WriteOutcome at h
  split at h
  · cases h.2.1
  · split at h
    · rcases h.2.2 with h | ⟨h, -⟩
      · cases h
      · exact h
    · rcases h.2 with ⟨-, h⟩ | ⟨-, h | ⟨h, -⟩⟩
      · cases h
      · cases h
      · exact h
    · rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
      · cases h
      · cases h
      · exact h

private theorem writeOutcome_closed {st : TcpEnd} {d d' : TcpDir} {rs : List w8} {k : Nat}
    (h : WriteOutcome st d rs k (some .closed) d') : st.closed = true := by
  unfold WriteOutcome at h
  split at h
  · assumption
  · split at h
    · rcases h.2.2 with h | ⟨-, h⟩ <;> cases h
    · rcases h.2 with ⟨-, h⟩ | ⟨-, h | ⟨-, h⟩⟩ <;> cases h
    · rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

private theorem writeOutcome_fail {st : TcpEnd} {d d' : TcpDir} {rs : List w8} {k : Nat}
    {e : TcpErr} (h : WriteOutcome st d rs k (some e) d') : k = 0 := by
  unfold WriteOutcome at h
  split at h
  · exact h.1
  · split at h
    · exact h.1
    · rcases h.2 with ⟨-, h⟩ | ⟨h, -⟩
      · cases h
      · exact h
    · rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
      · cases h
      · exact h
      · exact h

/-- `TestEmptyWrite`: an empty write (one step) succeeds on a live end, times out with a deadline,
fails after a reset or one's own `CloseWrite`. -/
example : WriteOutcome st0 ⟨[], .open⟩ [] 0 none ⟨[], .open⟩ := by unfold WriteOutcome; decide
example : WriteOutcome stW ⟨[], .open⟩ [] 0 (some .timeout) ⟨[], .open⟩ := by
  unfold WriteOutcome; decide
example : WriteOutcome st0 ⟨[], .cut⟩ [] 0 (some .sys) ⟨[], .cut⟩ := by unfold WriteOutcome; decide
example : WriteOutcome st0 ⟨[], .fin⟩ [] 0 (some .sys) ⟨[], .fin⟩ := by unfold WriteOutcome; decide

/-- A step appends the first `k` bytes, any `k` up to all of them (none: a wait), with no failure;
never more than it was given, never others. -/
example : WriteOutcome st0 ⟨[], .open⟩ b3 3 none ⟨b3, .open⟩ := by unfold WriteOutcome; decide
example : WriteOutcome st0 ⟨[], .open⟩ b3 1 none ⟨[97], .open⟩ := by unfold WriteOutcome; decide
example : WriteOutcome st0 ⟨[], .open⟩ b3 0 none ⟨[], .open⟩ := by unfold WriteOutcome; decide
example : ¬ WriteOutcome st0 ⟨[], .open⟩ [97] 2 none ⟨[97], .open⟩ := by
  unfold WriteOutcome; decide
example : ¬ WriteOutcome st0 ⟨[], .open⟩ b3 1 none ⟨[98], .open⟩ := by
  unfold WriteOutcome; decide

/-- `TestPartialWriteOnReset`: a `Write` cut by a reset counts what its earlier steps wrote, with
`sys`: a step appends `[97]`, the next fails, the connection broken. A failing step appends
nothing. -/
example : WriteOutcome st0 ⟨[], .open⟩ b3 1 none ⟨[97], .open⟩ ∧
    WriteOutcome st0 ⟨[97], .open⟩ [98, 99] 0 (some .sys) ⟨[97], .cut⟩ := by
  unfold WriteOutcome; decide
example : ¬ WriteOutcome st0 ⟨[], .open⟩ b3 1 (some .sys) ⟨[97], .cut⟩ := by
  unfold WriteOutcome; decide
example (st : TcpEnd) (d d' : TcpDir) (rs : List w8) (k : Nat) (e : TcpErr)
    (h : WriteOutcome st d rs k (some e) d') : k = 0 := writeOutcome_fail h

/-- `TestWriteDeadlinePrefix`: past a write deadline, a step appends some bytes, the next times
out, the direction open; a step with no write deadline set never times out. -/
example : WriteOutcome stW ⟨[], .open⟩ b3 2 none ⟨[97, 98], .open⟩ ∧
    WriteOutcome stW ⟨[97, 98], .open⟩ [99] 0 (some .timeout) ⟨[97, 98], .open⟩ := by
  unfold WriteOutcome; decide
example (d d' : TcpDir) (rs : List w8) (k : Nat) :
    ¬ WriteOutcome st0 d rs k (some .timeout) d' := fun h => by
  have := writeOutcome_timeout h; simp [st0, TcpEnd.fresh] at this

/-- `TestWriteDeadlineSetDuring` (D15, the v3 review's R1): a step with no deadline set appends
`[97]` (which the peer may read), another goroutine sets the write deadline, the next step times
out. -/
example : WriteOutcome st0 ⟨[], .open⟩ b3 1 none ⟨[97], .open⟩ ∧
    DeadlineOutcome st0 (W64 2) true none stW ∧
    WriteOutcome stW ⟨[97], .open⟩ [98, 99] 0 (some .timeout) ⟨[97], .open⟩ := by
  unfold WriteOutcome DeadlineOutcome; decide

/-- `TestWriteCloseRace` (D15): a step appends `[97, 98]`, another goroutine closes the end (the
direction shut after those bytes), the next step fails `closed`; `closed` never on a live end, and a
step on a closed end writes nothing. -/
example : WriteOutcome st0 ⟨[], .open⟩ b3 2 none ⟨[97, 98], .open⟩ ∧
    CloseOutcome st0 ⟨[97, 98], .open⟩ none stC ⟨[97, 98], .fin⟩ ∧
    WriteOutcome stC ⟨[97, 98], .fin⟩ [99] 0 (some .closed) ⟨[97, 98], .fin⟩ := by
  unfold WriteOutcome CloseOutcome; decide
example (d d' : TcpDir) (rs : List w8) (k : Nat) :
    ¬ WriteOutcome st0 d rs k (some .closed) d' := fun h => by
  have := writeOutcome_closed h; simp [st0, TcpEnd.fresh] at this
example : ¬ WriteOutcome stC ⟨[], .open⟩ b3 1 none ⟨[97], .open⟩ := by
  unfold WriteOutcome; decide

/-- `TestWriteAfterPeerClose`, `TestWriteToKilledPeer`, `TestResetErrorTakenByWrite`: into a cut
direction, the bytes are lost, counted, or the step fails `sys`. -/
example : WriteOutcome st0 ⟨[], .cut⟩ b3 3 none ⟨[], .cut⟩ := by unfold WriteOutcome; decide
example : WriteOutcome st0 ⟨[], .cut⟩ b3 0 (some .sys) ⟨[], .cut⟩ := by unfold WriteOutcome; decide

/-- `TestCloseWrite`: after one's own `CloseWrite`, a step fails (`EPIPE`), writing nothing. -/
example : ¬ WriteOutcome st0 ⟨[], .fin⟩ b3 3 none ⟨b3, .fin⟩ := by unfold WriteOutcome; decide
example : ¬ WriteOutcome st0 ⟨[], .fin⟩ b3 0 none ⟨[], .fin⟩ := by unfold WriteOutcome; decide

/-! ## Close, CloseWrite (D3, D4, D17) -/

/-- `TestCloseTwice`, `TestCloseAfterReset` (D17): `Close` of an open end succeeds (and only
succeeds), shutting its direction; a second `Close` is `closed`. -/
example : CloseOutcome st0 ⟨b3, .open⟩ none stC ⟨b3, .fin⟩ := by unfold CloseOutcome; decide
example : CloseOutcome st0 ⟨[], .cut⟩ none stC ⟨[], .cut⟩ := by unfold CloseOutcome; decide
example : ¬ CloseOutcome st0 ⟨b3, .open⟩ (some .sys) stC ⟨b3, .fin⟩ := by
  unfold CloseOutcome; decide
example : CloseOutcome stC ⟨b3, .fin⟩ (some .closed) stC ⟨b3, .fin⟩ := by
  unfold CloseOutcome; decide

/-- `TestCloseWrite`, `TestCloseWriteAfterReset`: `CloseWrite` shuts the direction, or fails with
`sys` (`ENOTCONN`); `closed` on a closed end. -/
example : CloseWriteOutcome st0 ⟨b3, .open⟩ none ⟨b3, .fin⟩ := by
  unfold CloseWriteOutcome; decide
example : CloseWriteOutcome st0 ⟨[], .cut⟩ (some .sys) ⟨[], .cut⟩ := by
  unfold CloseWriteOutcome; decide
example : CloseWriteOutcome stC ⟨[], .fin⟩ (some .closed) ⟨[], .fin⟩ := by
  unfold CloseWriteOutcome; decide

/-! ## Deadlines (D5) -/

/-- `TestCloseAfterReset`, `TestReadDeadlineLosesNothing`: `SetDeadline` succeeds on an end not
closed; `closed` after `Close` (`TestCloseTwice`). -/
example : DeadlineOutcome st0 (W64 1) true none stR := by unfold DeadlineOutcome; decide
example : DeadlineOutcome stR (W64 0) false none st0 := by unfold DeadlineOutcome; decide
example : DeadlineOutcome stC (W64 0) true (some .closed) stC := by unfold DeadlineOutcome; decide
example : timeIsZero 0 0 = true ∧ timeIsZero 1 0 = false := by decide

/-! ## Listeners, Dial (D6-D9, D16, D21) -/

private def planA : GMap GoString GoString := GMap.ofList [(go!"127.0.0.1:7101", go!"h")]

private theorem planA_lookup : planA !! go!"127.0.0.1:7101" = some go!"h" := by
  unfold planA GMap.ofList; exact GMap.lookup_insert _ _ _

/-- `TestAddressAliases` (D21): `":7101"` listens at the plan's only address with port 7101, at
this node's host. -/
example : ListenAt planA go!"h" go!":7101" go!"127.0.0.1:7101" := by
  refine ⟨planA_lookup, .inr ⟨?_, go!"7101", by decide, by decide, fun x hx hp => ?_⟩⟩
  · unfold planA GMap.ofList; exact GMap.lookup_insert_ne _ _ (by decide)
  simp only [planA, GMap.ofList] at hx
  by_cases h : go!"127.0.0.1:7101" = x
  · exact h.symm
  · rw [GMap.lookup_insert_ne _ _ h] at hx; cases hx
example : wildPort go!"0.0.0.0:7101" = some go!"7101" ∧ wildPort go!"[::]:7101" = some go!"7101" ∧
    wildPort go!"127.0.0.1:7101" = none := by decide

/-- (excluded) a listen at another host's address. -/
example : ¬ ListenAt planA go!"g" go!"127.0.0.1:7101" go!"127.0.0.1:7101" := by
  intro h; have := h.1; rw [planA_lookup] at this; simp at this

/-- `TestAcceptAfterListenerClose` (D9, D17): `LisClose` of an open listener succeeds, of a closed
one is `closed`. -/
example : LisCloseOutcome true none false := by unfold LisCloseOutcome; decide
example : LisCloseOutcome false (some .closed) false := by unfold LisCloseOutcome; decide
example : ¬ LisCloseOutcome true (some .sys) false := by unfold LisCloseOutcome; decide

/-- `TestDialTimeoutAccepted` (D16): an abandoned dial's connection is pending, its dialer's end
closed, its direction shut and empty: the acceptor reads EOF. -/
example : (TcpConn.abandoned go!"a").accepted = false ∧
    ReadOutcome st0 ((TcpConn.abandoned go!"a").out false) 4 .eof
      ((TcpConn.abandoned go!"a").out false) := by
  refine ⟨rfl, ?_⟩
  unfold ReadOutcome ReadAvail; simp [st0, TcpEnd.fresh, TcpConn.abandoned, TcpConn.out]
/-- ... and never data. -/
example : ¬ ReadOutcome st0 ((TcpConn.abandoned go!"a").out false) 4 (.bytes [97])
    ⟨[], .fin⟩ := fun h => by
  have := (readOutcome_bytes h).2; simp [TcpConn.abandoned, TcpConn.out] at this

/-! ## Errors (D14) -/

/-- `TestErrClosed`, `TestDeadlineErrors`, `TestSyscallErrors`: the three kinds have distinct codes,
none of them success's. -/
example : [errCode none, TcpErr.closed.code, TcpErr.timeout.code, TcpErr.sys.code] =
    [W64 0, W64 1, W64 2, W64 3] := rfl

/-! ## The deployment (D13, D20): `Deploy.lean`'s examples. -/

end Tcp
end Perennial
