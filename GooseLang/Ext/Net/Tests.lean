/-
Tests of the net extension's trusted semantics (`Impl.lean`, `Deploy.lean`), outside the trust base:
for each row of `examples/net/semantics/doc.go`, an `example` that the outcome relations allow (or
exclude) the outcome the row's Go test measured (or the source it cites documents, or the row
assumes); the comment names the Go test. Excluded outcomes are tested as well: a timeout without a
deadline, a short successful write, data after the end's own close, a read past what was written.
And D22 (v3.2): every operation may stutter in every state, every state has an outcome that is not a
stutter (`isNetStep_total`, `isNetStep_result`; v3.3: but a `Write`'s first step while another
`Write` of the end holds its write lock, D25), invalid uses panic, and the waits v3.1's relations
had (a blocked `Read`, `Accept`, a `Write` step counting nothing) are stutters. v3.3: socket options
(D24), the write lock (D25). v3.4: no plan and no hosts: any machine may listen at a valid address
or wildcard (D6, D21), a wildcard listener takes any address with its port, an invalid address
panics (D20, D22), and a crash leaves a machine in its initial state.
-/
module

public import GooseLang.Ext.Net.Deploy
public import Perennial.Golang.Defn.PostLang

namespace Perennial
namespace Net

set_option linter.unusedSimpArgs false

/-! ## States -/

private def st0 : NetEnd := NetEnd.fresh
private def stR : NetEnd := { NetEnd.fresh with rdl := true }
private def stW : NetEnd := { NetEnd.fresh with wdl := true }
private def stC : NetEnd := { NetEnd.fresh with closed := true }
private def b3 : List w8 := [97, 98, 99]

/-! ## Laws the negative tests use -/

private theorem readAvail_bytes {st : NetEnd} {d d' : NetDir} {n : Nat} {bs : List w8}
    (h : ReadAvail st d n (.bytes bs) d') : bs.length ≤ n ∧ bs <+: d.bytes ∧ bs ≠ [] := by
  rcases h with ⟨k, h1, h2, h3, h4, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩ <;>
    try cases h
  cases h4
  refine ⟨by rw [List.length_take]; omega, List.take_prefix _ _, ?_⟩
  intro he
  have := congrArg List.length he
  rw [List.length_take, List.length_nil] at this; omega

/-- A `sys` read error (D1 v3.5): only from a cut direction with nothing unread, which it keeps. -/
private theorem readAvail_sys {st : NetEnd} {d d' : NetDir} {n : Nat}
    (h : ReadAvail st d n (.err .sys) d') : d.status = .cut ∧ d.bytes = [] ∧ d' = d := by
  rcases h with ⟨_, _, _, _, h, -⟩ | ⟨-, -, h, -⟩ | ⟨hs, hb, -, rfl⟩ | ⟨-, h, -⟩
  · cases h
  · cases h
  · exact ⟨hs, hb, rfl⟩
  · cases h

/-- What a read returns is a prefix of the unread bytes, at most `n` of them (no byte invented,
none past the oldest unread: in order, once). -/
private theorem readOutcome_bytes {st : NetEnd} {d d' : NetDir} {n : Nat} {bs : List w8}
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

private theorem readOutcome_timeout {st : NetEnd} {d d' : NetDir} {n : Nat}
    (h : ReadOutcome st d n (.err .timeout) d') : st.rdl = true := by
  unfold ReadOutcome at h
  split at h
  · cases h.1
  · split at h
    · cases h.1
    · rcases h with h | ⟨k, -, h⟩ <;>
      rcases h with ⟨_, _, _, _, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -, -⟩ <;>
        first | exact h | cases h

/-! ## Reads (D1) -/

/-- `TestReadPartial`: a read returns what arrived, the rest stays. -/
example : ReadOutcome st0 ⟨b3, .open⟩ 2 (.bytes [97]) ⟨[98, 99], .open⟩ := by
  unfold ReadOutcome
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (2 : Nat) ≠ 0 by decide]
  exact .inl (.inl ⟨1, by decide, by decide, by decide, rfl, rfl⟩)

/-- `TestReadPartial` (excluded): more than asked for. -/
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 1 (.bytes [97, 98]) ⟨[99], .open⟩ := fun h => by
  have := (readOutcome_bytes h).1; simp at this

/-- In-order delivery, no corruption (assumed): a read's bytes are the oldest unread ones. -/
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 3 (.bytes [98]) ⟨[97, 99], .open⟩ := fun h => by
  have := (readOutcome_bytes h).2; simp [b3] at this

/-- `TestReadEmptyBuffer`: an empty read returns nothing at once, even with a deadline set. -/
example : ReadOutcome stR ⟨b3, .open⟩ 0 (.bytes []) ⟨b3, .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, NetEnd.fresh, b3]

/-- `TestReadEmptyBuffer` (excluded): an empty read does not time out (nor wait: it has its
outcome at once, `isNetStep_total`). -/
example : ¬ ReadOutcome stR ⟨b3, .open⟩ 0 (.err .timeout) ⟨b3, .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, NetEnd.fresh, b3]

/-- `TestReadEOFAfterFin`, `TestKilledWriterFin`: EOF once nothing is unread after a FIN or a
break. -/
example : ReadOutcome st0 ⟨[], .fin⟩ 4 .eof ⟨[], .fin⟩ := by
  unfold ReadOutcome ReadAvail; simp [st0, NetEnd.fresh]
example : ReadOutcome st0 ⟨b3, .open⟩ 4 .eof ⟨[], .cut⟩ := by
  unfold ReadOutcome
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (4 : Nat) ≠ 0 by decide]
  exact .inr ⟨0, by simp, .inr (.inl ⟨rfl, by decide, rfl, rfl⟩)⟩

/-- `TestResetCloseUnreadInput`, `TestResetLingerZero`, `TestKilledWithUnreadInput`: after a
reset, the bytes received, then an error (`sys`), then EOF. -/
example : ReadOutcome st0 ⟨[], .cut⟩ 4 (.err .sys) ⟨[], .cut⟩ := by
  unfold ReadOutcome ReadAvail; simp [st0, NetEnd.fresh]

/-- `TestStickyReset`, `TestStickyKilledPeer`, `TestStickyTimedOut` (excluded, v3.5): no `sys`
error while a byte is unread, so no byte after one (Linux returns an error from `read(2)` only when
it copied nothing). -/
example : ¬ ReadOutcome st0 ⟨b3, .cut⟩ 4 (.err .sys) ⟨b3, .cut⟩ := fun h => by
  unfold ReadOutcome at h
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (4 : Nat) ≠ 0 by decide] at h
  rcases h with h | ⟨k, -, h⟩
  · have := (readAvail_sys h).2.1; simp [b3] at this
  · obtain ⟨-, hb, he⟩ := readAvail_sys h
    simp only [NetDir.mk.injEq, and_true] at hb he
    rw [← he] at hb; simp [b3] at hb

/-- `TestStickyResetBlockedRead`, `TestResetInNetwork` (v3.5): a read may break the connection and
fail `sys`, the cut keeping nothing (the unread bytes are lost, as a reset that arrives before
them loses them). -/
example : ReadOutcome st0 ⟨b3, .open⟩ 4 (.err .sys) ⟨[], .cut⟩ := by
  unfold ReadOutcome
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (4 : Nat) ≠ 0 by decide]
  exact .inr ⟨0, by simp, .inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))⟩

/-- `TestStickyReset`, `TestStickyResetBlockedRead`, `TestStickyKilledPeer`, `TestStickyTimedOut`
(v3.5): after a `sys` error the direction is dead (`⟨[], .cut⟩`), and every later read, without a
deadline, is EOF or `sys` again, with no byte, the direction staying dead (Linux: EOF). -/
example (r : ReadRes) (d' : NetDir) (h : ReadOutcome st0 ⟨[], .cut⟩ 4 r d') :
    d' = ⟨[], .cut⟩ ∧ (r = .eof ∨ r = .err .sys) := by
  unfold ReadOutcome at h
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte,
    show (4 : Nat) ≠ 0 by decide] at h
  rcases h with h | ⟨k, -, h⟩
  · rcases h with ⟨k, h1, -, hk, -⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
    · simp at hk; omega
    · exact ⟨rfl, .inl rfl⟩
    · exact ⟨rfl, .inr rfl⟩
    · simp at h
  · rcases h with ⟨k, h1, -, hk, -⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
    · simp at hk; omega
    · exact ⟨by simp, .inl rfl⟩
    · exact ⟨by simp, .inr rfl⟩
    · simp at h

/-- `TestCloseTwice`, `TestCloseUnblocksRead`: a read on one's own closed end is `closed`, never
data. -/
example : ReadOutcome stC ⟨b3, .open⟩ 4 (.err .closed) ⟨b3, .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, NetEnd.fresh, b3]
example : ¬ ReadOutcome stC ⟨b3, .open⟩ 4 (.bytes [97]) ⟨[98, 99], .open⟩ := by
  simp [ReadOutcome, st0, stR, stC, NetEnd.fresh, b3]

/-- `TestErrClosed`: a read of a live end is never `closed`. -/
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 4 (.err .closed) ⟨b3, .open⟩ := by
  unfold ReadOutcome ReadAvail
  simp [st0, NetEnd.fresh]

/-- `TestReadDeadlineLosesNothing`: a timeout, with a read deadline, keeps the bytes; never
without a deadline. -/
example : ReadOutcome stR ⟨b3, .open⟩ 4 (.err .timeout) ⟨b3, .open⟩ := by
  unfold ReadOutcome ReadAvail; simp [stR, NetEnd.fresh]
example : ¬ ReadOutcome st0 ⟨b3, .open⟩ 4 (.err .timeout) ⟨b3, .open⟩ := fun h => by
  have := readOutcome_timeout h; simp [st0, NetEnd.fresh] at this

/-! ## Writes (D2, D15)

`WriteOutcome` is one step of a `Write` (one `write(2)`, with its wait); `conn.Write.impl` loops
over the steps and returns `(nn, nil)` only once they have counted every byte
(`net.Conn.Write.spec`'s post: `res = none → w = bs`), so a short successful `Write` is excluded
there, not here. -/

private theorem writeOutcome_timeout {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    (h : WriteOutcome st d rs k (some .timeout) d') : st.wdl = true := by
  unfold WriteOutcome at h
  split at h
  · cases h.2.1
  · split at h
    · rcases h.2.2 with h | ⟨h, -⟩
      · cases h
      · exact h
    · rcases h.2 with ⟨-, -, h⟩ | ⟨-, h | ⟨h, -⟩⟩
      · cases h
      · cases h
      · exact h
    · rcases h with ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
      · cases h
      · cases h
      · exact h

private theorem writeOutcome_closed {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    (h : WriteOutcome st d rs k (some .closed) d') : st.closed = true := by
  unfold WriteOutcome at h
  split at h
  · assumption
  · split at h
    · rcases h.2.2 with h | ⟨-, h⟩ <;> cases h
    · rcases h.2 with ⟨-, -, h⟩ | ⟨-, h | ⟨-, h⟩⟩ <;> cases h
    · rcases h with ⟨-, -, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

private theorem writeOutcome_fail {st : NetEnd} {d d' : NetDir} {rs : List w8} {k : Nat}
    {e : NetErr} (h : WriteOutcome st d rs k (some e) d') : k = 0 := by
  unfold WriteOutcome at h
  split at h
  · exact h.1
  · split at h
    · exact h.1
    · rcases h.2 with ⟨-, -, h⟩ | ⟨h, -⟩
      · cases h
      · exact h
    · rcases h with ⟨-, -, h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
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

/-- A step appends the first `k` bytes, any `k` from one up to all of them, with no failure; never
more than it was given, never others; one that would count none of a non-empty `rs` is a wait, a
stutter (D22), not an outcome (below, `write_wait`). -/
example : WriteOutcome st0 ⟨[], .open⟩ b3 3 none ⟨b3, .open⟩ := by unfold WriteOutcome; decide
example : WriteOutcome st0 ⟨[], .open⟩ b3 1 none ⟨[97], .open⟩ := by unfold WriteOutcome; decide
example : ¬ WriteOutcome st0 ⟨[], .open⟩ b3 0 none ⟨[], .open⟩ := by unfold WriteOutcome; decide
example : ¬ WriteOutcome st0 ⟨[], .cut⟩ b3 0 none ⟨[], .cut⟩ := by unfold WriteOutcome; decide
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
example (st : NetEnd) (d d' : NetDir) (rs : List w8) (k : Nat) (e : NetErr)
    (h : WriteOutcome st d rs k (some e) d') : k = 0 := writeOutcome_fail h

/-- `TestWriteDeadlinePrefix`: past a write deadline, a step appends some bytes, the next times
out, the direction open; a step with no write deadline set never times out. -/
example : WriteOutcome stW ⟨[], .open⟩ b3 2 none ⟨[97, 98], .open⟩ ∧
    WriteOutcome stW ⟨[97, 98], .open⟩ [99] 0 (some .timeout) ⟨[97, 98], .open⟩ := by
  unfold WriteOutcome; decide
example (d d' : NetDir) (rs : List w8) (k : Nat) :
    ¬ WriteOutcome st0 d rs k (some .timeout) d' := fun h => by
  have := writeOutcome_timeout h; simp [st0, NetEnd.fresh] at this

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
example (d d' : NetDir) (rs : List w8) (k : Nat) :
    ¬ WriteOutcome st0 d rs k (some .closed) d' := fun h => by
  have := writeOutcome_closed h; simp [st0, NetEnd.fresh] at this
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

/-- `TestAddressAliases`, `TestWildcardListen` (D21): `":7101"`, `"0.0.0.0:7101"` and
`"[::]:7101"` are valid `Listen` addresses, and take a connection dialed to any address with the
port 7101; a listener at a valid address takes only its own. -/
example : listenOk go!":7101" = true ∧ listenOk go!"0.0.0.0:7101" = true ∧
    listenOk go!"[::]:7101" = true ∧ listenOk go!"127.0.0.1:7101" = true := by decide
example : lisAccepts go!":7101" go!"127.0.0.1:7101" ∧ lisAccepts go!"[::]:7101" go!"10.0.0.2:7101" :=
  ⟨.inr ⟨go!"7101", by decide, by decide⟩, .inr ⟨go!"7101", by decide, by decide⟩⟩
example : ¬ lisAccepts go!"127.0.0.1:7101" go!"127.0.0.2:7101" := by
  rw [lisAccepts_addrOk (by decide)]; decide
example : ¬ lisAccepts go!":7101" go!"127.0.0.1:7102" := by
  rintro (h | ⟨p, hw, hp⟩)
  · cases h
  · have : wildPort go!":7101" = some go!"7101" := by decide
    rw [this] at hw; cases hw; revert hp; decide
example : wildPort go!"0.0.0.0:7101" = some go!"7101" ∧ wildPort go!"[::]:7101" = some go!"7101" ∧
    wildPort go!"127.0.0.1:7101" = none := by decide

/-- (excluded, D20) a `Listen` of a hostname, a non-canonical spelling, an ephemeral or zero port, a
wildcard whose port is not canonical: not valid. -/
example : listenOk go!"localhost:7101" = false ∧ listenOk go!"127.0.0.01:7101" = false ∧
    listenOk go!"127.0.0.1:40000" = false ∧ listenOk go!":0" = false ∧
    listenOk go!":07101" = false := by decide

section
variable [GooseExts] [GoGlobalContext]

/-- (v3.4) `TestListenNotLocal`: a `Listen` at an address that is not this machine's fails
(`EADDRNOTAVAIL`), which the model allows of every `Listen`; and any machine may listen at a valid
address (the model does not know the owner). -/
example (L : NetLocal) : ListenStep go!"10.0.0.2:7101" L (Val (failV .sys)) L := .inl ⟨rfl, rfl⟩
example : ListenStep go!"10.0.0.2:7101" ⟨∅⟩ (Val (PairV (#(W64 1)) (#(W64 0))))
    ⟨(∅ : GMap w64 (GoString × Bool)).insert (W64 1) (go!"10.0.0.2:7101", true)⟩ :=
  .inr ⟨fun l h => by simp at h, W64 1, by decide, rfl, rfl, rfl⟩
/-- (excluded) `TestListenTwice`: a second `Listen` at an address this machine listens at only
fails (`EADDRINUSE`). -/
example (e' : Expr) (L' : NetLocal)
    (h : ListenStep go!"127.0.0.1:7101"
      ⟨(∅ : GMap w64 (GoString × Bool)).insert (W64 1) (go!"127.0.0.1:7101", true)⟩ e' L') :
    e' = Val (failV .sys) := by
  rcases h with ⟨rfl, -⟩ | ⟨hno, -⟩
  · rfl
  · exact absurd (GMap.lookup_insert _ _ _) (hno (W64 1))

/-- D10 (v3.4): a crash leaves a machine in its initial state. -/
example (L L' : NetLocal) (h : net_semantics.crash L L') : L'.init := crash_init L L' h

end

/-- `TestAcceptAfterListenerClose` (D9, D17): `LisClose` of an open listener succeeds, of a closed
one is `closed`. -/
example : LisCloseOutcome true none false := by unfold LisCloseOutcome; decide
example : LisCloseOutcome false (some .closed) false := by unfold LisCloseOutcome; decide
example : ¬ LisCloseOutcome true (some .sys) false := by unfold LisCloseOutcome; decide

/-- `TestDialTimeoutAccepted` (D16): an abandoned dial's connection is pending, its dialer's end
closed, its direction shut and empty: the acceptor reads EOF. -/
example : (NetConn.abandoned go!"a").accepted = false ∧
    ReadOutcome st0 ((NetConn.abandoned go!"a").out false) 4 .eof
      ((NetConn.abandoned go!"a").out false) := by
  refine ⟨rfl, ?_⟩
  unfold ReadOutcome ReadAvail; simp [st0, NetEnd.fresh, NetConn.abandoned, NetConn.out]
/-- ... and never data. -/
example : ¬ ReadOutcome st0 ((NetConn.abandoned go!"a").out false) 4 (.bytes [97])
    ⟨[], .fin⟩ := fun h => by
  have := (readOutcome_bytes h).2; simp [NetConn.abandoned, NetConn.out] at this

/-! ## Errors (D14) -/

/-- `TestErrClosed`, `TestDeadlineErrors`, `TestSyscallErrors`: the three kinds have distinct codes,
none of them success's. -/
example : [errCode none, NetErr.closed.code, NetErr.timeout.code, NetErr.sys.code] =
    [W64 0, W64 1, W64 2, W64 3] := rfl

/-! ## Steps (D22): stutters, every state's outcome, panics

Every operation may stutter in every state; every state has an outcome rule that is not a stutter
(`isNetStep_total`, and `isNetStep_result`: an outcome rule returns a value or panics), so no
program can stutter where Go would go on; an invalid use panics; the waits of v3.1's relations are
stutters, followed by the outcome that ends them. -/

section steps
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj]

private theorem readOutcome_total (st : NetEnd) (d : NetDir) (n : Nat) :
    ∃ r d', ReadOutcome st d n r d' := by
  unfold ReadOutcome
  split
  · exact ⟨_, _, rfl, rfl⟩
  · split
    · exact ⟨_, _, rfl, rfl⟩
    · exact ⟨.eof, ⟨d.bytes.take 0, .cut⟩,
        .inr ⟨0, Nat.zero_le _, .inr (.inl ⟨by simp, by simp, rfl, rfl⟩)⟩⟩

private theorem writeOutcome_total (st : NetEnd) (d : NetDir) (bs : List w8) :
    ∃ k res d', WriteOutcome st d bs k res d' := by
  unfold WriteOutcome
  split
  · exact ⟨_, _, _, rfl, rfl, rfl⟩
  · split
    · exact ⟨0, some .sys, _, rfl, rfl, .inl rfl⟩
    · exact ⟨0, some .sys, _, rfl, .inr ⟨rfl, .inl rfl⟩⟩
    · exact ⟨0, some .sys, _, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩

private theorem orInvalid_total {valid : Prop} {step : Expr → NetLocal → NetGlobal → Prop}
    {L : NetLocal} {g : NetGlobal} (h : valid → ∃ e' L' g', step e' L' g') :
    ∃ e' L' g', OrInvalid valid (step e' L' g') L g e' L' g' := by
  by_cases hv : valid
  · obtain ⟨e', L', g', hs⟩ := h hv
    exact ⟨e', L', g', .inl hs⟩
  · exact ⟨_, _, _, .inr ⟨hv, rfl, rfl, rfl⟩⟩

/-- D25: the one state with no outcome rule besides the stutter: a `Write`'s first step at an end
whose write lock another `Write` holds (it waits for the lock, as Go's `fd.writeLock()` does; the
holder's own steps have outcomes, `isNetStep_total`). -/
def WriteWaits (op : String) (v : val) (g : NetGlobal) : Prop :=
  op = "Write" ∧ ∃ (e : w64) (bs : List w8) (c : Nat) (s : Bool) (cn : NetConn),
    v = PairV (#e) (PairV (#bs) (#true)) ∧ IsEnd e c s ∧ g.conns !! c = some cn ∧ cn.lock s = true

/-- D22: every operation, in every state and on every argument, has an outcome rule (besides the
stutter): a step, or a panic; but a `Write`'s first step waiting for the write lock (D25,
`WriteWaits`). -/
theorem isNetStep_total (op : String) (v : val) (L : NetLocal) (g : NetGlobal)
    (hw : ¬ WriteWaits op v g) : ∃ e' L' g', IsNetStep op v L g e' L' g' := by
  unfold IsNetStep
  split
  · apply orInvalid_total
    rintro ⟨a, rfl, hla⟩
    exact ⟨_, _, _, a, rfl, hla, .inl ⟨rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨l, ⟨a, o⟩, rfl, hl⟩
    cases o
    · exact ⟨_, _, _, l, a, false, rfl, hl, .inl ⟨rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨_, _, _, l, a, true, rfl, hl, .inr (.inl ⟨rfl, rfl, rfl⟩), rfl⟩
  · apply orInvalid_total
    rintro ⟨l, ⟨a, o⟩, rfl, hl⟩
    exact ⟨_, _, _, l, a, o, if o then none else some .closed, false, rfl, hl, rfl,
      by cases o <;> simp [LisCloseOutcome], rfl, rfl⟩
  · apply orInvalid_total
    rintro ⟨a, rfl, ha⟩
    exact ⟨_, _, _, a, rfl, ⟨ha, .inl ⟨rfl, rfl⟩⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨e, n, c, s, rfl, hE, hc⟩
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨r, d', hr⟩ := readOutcome_total (cn.endSt s) (cn.out (!s)) n.toNat
    exact ⟨_, _, _, e, n, c, s, rfl, hE, ⟨cn, r, d', hcn, hr, rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨e, bs, first, c, s, rfl, ⟨hE, hc⟩, hfl⟩
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
    have hl : cn.lock s = !first := by
      cases first
      · simpa [hcn] using hfl
      · cases h : cn.lock s
        · rfl
        · exact absurd ⟨rfl, e, bs, c, s, cn, rfl, hE, hcn, h⟩ hw
    obtain ⟨k, res, d', hwo⟩ := writeOutcome_total (cn.endSt s) (cn.out s) bs
    exact ⟨_, _, _, e, bs, first, c, s, rfl, hE, ⟨cn, k, res, d', hcn, hl, hwo, rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨e, kind, x, c, s, rfl, hE, hc⟩
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
    have : ∃ res, SockOptOutcome (cn.endSt s) (sockOptValid kind x) res := by
      unfold SockOptOutcome
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
    obtain ⟨res, hr⟩ := this
    exact ⟨_, _, _, e, kind, x, c, s, rfl, hE, ⟨cn, res, hcn, hr, rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨e, c, s, rfl, hE, hc⟩
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
    have : CloseOutcome (cn.endSt s) (cn.out s)
        (if (cn.endSt s).closed then some .closed else none)
        (if (cn.endSt s).closed then cn.endSt s else { cn.endSt s with closed := true })
        (if (cn.endSt s).closed then cn.out s else (cn.out s).shut) := by
      unfold CloseOutcome; split <;> simp_all
    exact ⟨_, _, _, e, c, s, rfl, hE, ⟨cn, _, _, _, hcn, this, rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨e, c, s, rfl, hE, hc⟩
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
    have : CloseWriteOutcome (cn.endSt s) (cn.out s)
        (if (cn.endSt s).closed then some .closed else none)
        (if (cn.endSt s).closed then cn.out s else (cn.out s).shut) := by
      unfold CloseWriteOutcome; split <;> simp_all
    exact ⟨_, _, _, e, c, s, rfl, hE, ⟨cn, _, _, hcn, this, rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨e, kind, wall, ext, c, s, rfl, hE, hc⟩
    obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
    have : ∃ res st', DeadlineOutcome (cn.endSt s) kind (!timeIsZero wall ext) res st' := by
      unfold DeadlineOutcome; split
      · exact ⟨_, _, rfl, rfl⟩
      · exact ⟨_, _, rfl, rfl⟩
    obtain ⟨res, st', hd⟩ := this
    exact ⟨_, _, _, e, kind, wall, ext, c, s, rfl, hE, ⟨cn, res, st', hcn, hd, rfl, rfl⟩, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨true, rfl⟩, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨[], rfl⟩, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨W64 0, rfl⟩, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨W64 1, by decide, rfl⟩, rfl, rfl⟩
  · exact ⟨_, _, _, rfl, rfl, rfl⟩

/-- The panic of an invalid use. -/
private abbrev panicE : Expr := Panic "net: invalid use of the net extension"

private theorem orInvalid_result {valid step : Prop} {L L' : NetLocal} {g g' : NetGlobal}
    {e' : Expr} (hs : step → ∃ w, e' = Val w) (h : OrInvalid valid step L g e' L' g') :
    (∃ w, e' = Val w) ∨ e' = panicE := by
  rcases h with h | ⟨-, rfl, -, -⟩
  · exact .inl (hs h)
  · exact .inr rfl

/-- D22: an outcome rule returns a value, or panics: it is never a stutter (whose expression is the
call, an `ExternalOp`), so a state's outcome (`isNetStep_total`) decides the call. -/
theorem isNetStep_result {op : String} {v : val} {L L' : NetLocal} {g g' : NetGlobal} {e' : Expr}
    (h : IsNetStep op v L g e' L' g') : (∃ w, e' = Val w) ∨ e' = panicE := by
  unfold IsNetStep at h
  split at h
  · refine orInvalid_result ?_ h
    rintro ⟨a, -, -, ⟨rfl, -⟩ | ⟨-, l, -, -, rfl, -⟩, -⟩ <;> exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨l, a, o, -, -, ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, c, cn, -, -, -, -, rfl, -⟩, -⟩ <;>
      exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨l, a, o, res, o', -, -, -, -, rfl, -⟩; exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨a, -, ⟨-, ⟨rfl, -⟩ | ⟨c, -, rfl, -⟩ | ⟨c, -, rfl, -⟩⟩, -⟩ <;> exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨e, n, c, s, -, -, ⟨cn, r, d', -, -, rfl, -⟩, -⟩; exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨e, bs, first, c, s, -, -, ⟨cn, k, res, d', -, -, -, rfl, -⟩, -⟩; exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨e, kind, x, c, s, -, -, ⟨cn, res, -, -, rfl, -⟩, -⟩; exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨e, c, s, -, -, ⟨cn, res, st', d', -, -, rfl, -⟩, -⟩; exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨e, c, s, -, -, ⟨cn, res, d', -, -, rfl, -⟩, -⟩; exact ⟨_, rfl⟩
  · refine orInvalid_result ?_ h
    rintro ⟨e, kind, wall, ext, c, s, -, -, ⟨cn, res, st', -, -, rfl, -⟩, -⟩; exact ⟨_, rfl⟩
  · exact orInvalid_result (fun ⟨_, ⟨_, hb⟩, _⟩ => ⟨_, hb⟩) h
  · exact orInvalid_result (fun ⟨_, ⟨_, hb⟩, _⟩ => ⟨_, hb⟩) h
  · exact orInvalid_result (fun ⟨_, ⟨_, hb⟩, _⟩ => ⟨_, hb⟩) h
  · exact orInvalid_result (fun ⟨_, ⟨_, _, hb⟩, _⟩ => ⟨_, hb⟩) h
  · exact .inr h.1

/-- D22: every operation stutters, in every state, on every argument. -/
example (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (L : NetLocal) (g : NetGlobal) :
    NetStep op v h L g (ExternalOp netExt.name op (Val v)) h L g := ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩

private def gA : NetGlobal := ⟨∅⟩
private def LA : NetLocal := ⟨∅⟩

/-- D22, D20: `Listen` or `Dial` of an invalid address panics, and only panics (besides the
stutter): a hostname, a wildcard `Dial`. -/
example (e' : Expr) (L' : NetLocal) (g' : NetGlobal)
    (h : IsNetStep "Listen" (#go!"localhost:7101") LA gA e' L' g') : e' = panicE := by
  rcases h with ⟨a, ha, hok, -⟩ | ⟨-, h, -⟩
  · obtain rfl := go.intoVal_inj (V := GoString) ha
    exact absurd hok (by decide)
  · exact h
example (e' : Expr) (L' : NetLocal) (g' : NetGlobal)
    (h : IsNetStep "Dial" (#go!":7101") LA gA e' L' g') : e' = panicE := by
  rcases h with ⟨a, ha, ⟨hp, -⟩, -⟩ | ⟨-, h, -⟩
  · obtain rfl := go.intoVal_inj (V := GoString) ha
    exact absurd hp (by decide)
  · exact h
/-- (v3.4) a valid address at any machine does not panic. -/
example : IsNetStep "Listen" (#go!"10.0.0.2:7101") LA gA (Val (failV .sys)) LA gA :=
  .inl ⟨go!"10.0.0.2:7101", rfl, by decide, .inl ⟨rfl, rfl⟩, rfl⟩

/-- D22: an operation on an id that names nothing (here `0`, the zero value's, which the models
never pass: they return `syscall.EINVAL` first, `Net/TrustedCode/net.lean`'s `model.einval`)
panics, and only panics; so does a listener id with no listener. -/
example (n : w64) (e' : Expr) (L' : NetLocal) (g' : NetGlobal)
    (h : IsNetStep "Read" (PairV (#(W64 0)) (#n)) LA gA e' L' g') : e' = panicE := by
  rcases h with ⟨e, n', c, s, -, -, ⟨cn, -, -, hcn, -⟩, -⟩ | ⟨-, h, -⟩
  · simp [gA] at hcn
  · exact h
example (e' : Expr) (L' : NetLocal) (g' : NetGlobal)
    (h : IsNetStep "Accept" (#(W64 0)) LA gA e' L' g') : e' = panicE := by
  rcases h with ⟨l, a, o, -, hl, -⟩ | ⟨-, h, -⟩
  · simp [LA] at hl
  · exact h

/-- D22: an operation the extension does not have panics. -/
example (v : val) (e' : Expr) (L' : NetLocal) (g' : NetGlobal)
    (h : IsNetStep "Send" v LA gA e' L' g') : e' = panicE := h.1
/-- D22: a blocked `Accept` (D7) stutters, then accepts the connection when it is pending (the
behavior of v3.1's wait clause). -/
example (cn : NetConn) (hca : cn.addr = go!"127.0.0.1:7101") (hacc : cn.accepted = false)
    (h0 : GMap Loc (NonAtomic val)) :
    let L : NetLocal := ⟨(∅ : GMap w64 (GoString × Bool)).insert (W64 5)
      (go!"127.0.0.1:7101", true)⟩
    let g : NetGlobal := ⟨(∅ : GMap Nat NetConn).insert 1 cn⟩
    NetStep "Accept" (#(W64 5)) h0 L g (ExternalOp netExt.name "Accept" (Val (#(W64 5)))) h0 L g ∧
    NetStep "Accept" (#(W64 5)) h0 L g (Val (PairV (#(endId 1 true)) (#(W64 0)))) h0 L
      (g.setConn 1 { cn with accepted := true }) := by
  refine ⟨⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩, rfl, .inr (.inl ⟨W64 5, go!"127.0.0.1:7101", true, rfl,
    GMap.lookup_insert _ _ _, .inr (.inr ⟨rfl, 1, cn, GMap.lookup_insert _ _ _, .inl hca.symm, hacc,
      by decide, rfl, rfl⟩), rfl⟩)⟩

/-- D22: a blocked `Read` (D1, nothing unread, the writer open) stutters, then returns the bytes
once they are written; it has no outcome of its own while it waits but a break (EOF or an error)
or, with a read deadline, a timeout. -/
example : ReadOutcome st0 ⟨b3, .open⟩ 3 (.bytes b3) ⟨[], .open⟩ := by
  unfold ReadOutcome
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte, show (3 : Nat) ≠ 0 by decide]
  exact .inl (.inl ⟨3, by decide, by decide, by decide, rfl, rfl⟩)
example (r : ReadRes) (d' : NetDir) (h : ReadOutcome st0 ⟨[], .open⟩ 3 r d') :
    d'.status = .cut ∧ (r = .eof ∨ r = .err .sys) := by
  unfold ReadOutcome at h
  simp only [st0, NetEnd.fresh, Bool.false_eq_true, ↓reduceIte,
    show (3 : Nat) ≠ 0 by decide] at h
  rcases h with h | ⟨k, hk, h⟩
  · rcases h with ⟨k, h1, -, hk, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all
  · obtain rfl : k = 0 := by simpa using hk
    rcases h with ⟨k, h1, -, hk, -⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨h, -⟩
    · simp at hk; omega
    · exact ⟨rfl, .inl rfl⟩
    · exact ⟨rfl, .inr rfl⟩
    · simp [st0, NetEnd.fresh] at h

/-- D22: a `Write` step that would count none of its bytes (a full buffer) is a stutter, not an
outcome; an empty one finishes with `0`. -/
example (h0 : GMap Loc (NonAtomic val)) (cn : NetConn) (hd : cn.up = ⟨[], .open⟩)
    (he : cn.dEnd = st0) :
    let g : NetGlobal := ⟨(∅ : GMap Nat NetConn).insert 1 cn⟩
    NetStep "Write" (PairV (#(endId 1 false)) (PairV (#b3) (#true))) h0 LA g
        (ExternalOp netExt.name "Write" (Val (PairV (#(endId 1 false)) (PairV (#b3) (#true))))) h0
        LA g ∧
      ¬ WriteOutcome (cn.endSt false) (cn.out false) b3 0 none (cn.out false) ∧
      WriteOutcome (cn.endSt false) (cn.out false) [] 0 none (cn.out false) := by
  refine ⟨⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩, ?_, ?_⟩ <;>
    simp only [NetConn.endSt, NetConn.out, hd, he] <;> unfold WriteOutcome <;> decide

/-- `TestWriteLock` (D25): a `Write`'s first step that does not end it (one byte of three) takes
the end's write lock; while it is held, another `Write`'s first step has no outcome (it waits), so
the bytes of two `Write`s of one end never interleave. -/
example (cn : NetConn) (hl : cn.lock false = false) (hd : cn.up = ⟨[], .open⟩)
    (he : cn.dEnd = st0) :
    let g : NetGlobal := ⟨(∅ : GMap Nat NetConn).insert 1 cn⟩
    WriteStep 1 false b3 true g (Val (PairV (#(BitVec.ofNat 64 1)) (#(errCode none))))
      (g.setConn 1 ((cn.setOut false ⟨[97], .open⟩).setLock false true)) := by
  refine ⟨cn, 1, none, ⟨[97], .open⟩, GMap.lookup_insert _ _ _, by simp [hl], ?_, rfl, ?_⟩
  · simp only [NetConn.endSt, NetConn.out, hd, he]; unfold WriteOutcome; decide
  · simp [writeLast, b3]
example (cn : NetConn) (hl : cn.lock false = true) (bs : List w8) (e' : Expr) (g' : NetGlobal) :
    ¬ WriteStep 1 false bs true ⟨(∅ : GMap Nat NetConn).insert 1 cn⟩ e' g' := by
  rintro ⟨cn', k, res, d', hcn, hl', -⟩
  simp only [GMap.lookup_insert, Option.some.injEq] at hcn
  subst hcn
  simp_all
/-- ... the holder's later steps need the lock (a later step without it is an invalid use), and
its last step (every byte written, or a failure) frees it. -/
example : writeLast b3 1 none = false ∧ writeLast [98, 99] 2 none = true ∧
    writeLast [98, 99] 0 (some .closed) = true ∧ writeLast [] 0 none = true := by decide
example (cn : NetConn) (hl : cn.lock false = false) (bs : List w8) (e' : Expr) (g' : NetGlobal) :
    ¬ WriteStep 1 false bs false ⟨(∅ : GMap Nat NetConn).insert 1 cn⟩ e' g' := by
  rintro ⟨cn', k, res, d', hcn, hl', -⟩
  simp only [GMap.lookup_insert, Option.some.injEq] at hcn
  subst hcn
  simp_all

end steps

/-! ## Socket options (D24) -/

/-- `TestSockOpts`: an option succeeds on an end not closed, fails `closed` on a closed one, and
changes nothing (`SockOptOutcome` has no state after). -/
private theorem sockOptValid_0 : sockOptValid 0 0 = some true := by decide
example : SockOptOutcome st0 (sockOptValid 0 0) none := by
  rw [sockOptValid_0]; simp [SockOptOutcome, st0, NetEnd.fresh]
example : SockOptOutcome stC (sockOptValid 0 0) (some .closed) := by
  rw [sockOptValid_0]; simp [SockOptOutcome, stC, NetEnd.fresh]
example : ¬ SockOptOutcome stC (sockOptValid 0 0) none := by
  rw [sockOptValid_0]; simp [SockOptOutcome, stC, NetEnd.fresh]
example : ¬ SockOptOutcome st0 (sockOptValid 0 0) (some .sys) := by
  rw [sockOptValid_0]; simp [SockOptOutcome, st0, NetEnd.fresh]
/-- ... `SetKeepAlivePeriod`: 32767 s accepted, 32768 s refused (`EINVAL`), `(2^32 + 10) s`
accepted (`int32`), `0` (Go's 15 s) accepted, a negative duration no system call (success even on a
closed end). -/
example : keepIdleValid (BitVec.ofInt 64 32767000000000) = some true ∧
    keepIdleValid (BitVec.ofInt 64 32768000000000) = some false ∧
    keepIdleValid (BitVec.ofInt 64 32767000000001) = some false ∧
    keepIdleValid (BitVec.ofInt 64 ((2 ^ 32 + 10) * 1000000000)) = some true ∧
    keepIdleValid 0 = some true ∧ keepIdleValid (BitVec.ofInt 64 (-1000000000)) = none ∧
    keepIdleValid (BitVec.ofInt 64 9223372036854775807) = some false := by decide
example : SockOptOutcome stC (sockOptValid 1 (BitVec.ofInt 64 (-1))) none := by
  rw [show sockOptValid 1 (BitVec.ofInt 64 (-1)) = none by decide]; rfl
example : SockOptOutcome st0 (sockOptValid 1 (BitVec.ofInt 64 32768000000000)) (some .sys) := by
  rw [show sockOptValid 1 (BitVec.ofInt 64 32768000000000) = some false by decide]
  simp [SockOptOutcome, st0, NetEnd.fresh]

/-! ## The deployment (D13, D20): `Deploy.lean`'s examples. -/

end Net
end Perennial
