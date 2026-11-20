/-
Sanity checks of the TCP extension's semantics (`Impl.lean`): outcomes it allows and excludes,
stated on single operations. Not part of the trust base; they are here so that a reviewer can
see the definitions do what their docstrings say.
-/
module

public import Harness.GooseLang.Ext.NetConn.Impl

namespace Perennial.NetConn

/-- A connection whose stream from the dialer holds `bs` with status `st`, both ends open. -/
def withIncoming (bs : List w8) (st : StreamStatus) : Conn :=
  Conn.fresh.setStream false ⟨bs, st⟩

/-- Excluded: a Read with a non-empty buffer never returns no bytes and no error. -/
example (c c' : Conn) (side : Side) (n : Nat) (hn : n ≠ 0) :
    ¬ ReadOutcome c side n [] errNone c' := by
  intro h
  simp only [ReadOutcome, hn, ite_false] at h
  by_cases hc : (c.ends side).closed = true
  · simp [hc] at h
  · simp [hc] at h

/-- Allowed: after the peer closed, with everything read, `io.EOF`. -/
example : ReadOutcome (withIncoming [] .fin) true 8 [] errEOF (withIncoming [] .fin) := by
  simp [ReadOutcome, withIncoming, Conn.setStream, Conn.fresh]

/-- Excluded: on a live empty stream with no deadline, a Read neither returns EOF nor fails
(it waits: `NetConnStep`'s first `Read` case). -/
example (code : w64) (c' : Conn) :
    ¬ ReadOutcome (withIncoming [] .live) true 8 [] code c' := by
  simp [ReadOutcome, withIncoming, Conn.setStream, Conn.fresh]

/-- Allowed: a break that keeps the first byte of `[1, 2, 3]` and cuts both streams. -/
example : (withIncoming [1, 2, 3] .live).Breaks
    ⟨fun s => if s = false then ⟨[1], .cut⟩ else ⟨[], .cut⟩,
     (withIncoming [1, 2, 3] .live).ends⟩ := by
  refine ⟨rfl, ?_⟩
  intro s
  cases s <;> simp [withIncoming, Conn.setStream, Conn.fresh]

/-- Excluded: on a cut stream that still holds a byte, a Read does not fail (without a further
break, which `BreakOrNot` would apply first): the surviving bytes come first. -/
example : ¬ ReadOutcome (withIncoming [1] .cut) true 8 [] errBroken (withIncoming [1] .cut) := by
  simp [ReadOutcome, withIncoming, Conn.setStream, Conn.fresh]

/-- Allowed: a `Write` of 3 bytes at an open end returns 2 with `errClosed` (another goroutine
closed the end while the `Write` waited), and the 2 bytes are in the stream
[netsem: WriteCloseRace]. -/
example : WriteOutcome Conn.fresh false [1, 2, 3] 2 errClosed
    (Conn.fresh.setStream false ⟨[1, 2], .live⟩) :=
  ⟨by decide, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩

/-- Excluded: the same `Write` with bytes past the reported count in the stream. -/
example : ¬ WriteOutcome Conn.fresh false [1, 2, 3] 2 errClosed
    (Conn.fresh.setStream false ⟨[1, 2, 3], .live⟩) := by
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · have := congrArg (fun c : Conn => (c.stream false).bytes) h
    simp [Conn.setStream, Conn.fresh] at this
  · exact absurd h (by decide)

/-- Excluded: on a closed end, a `Write` returns no count. -/
example (c' : Conn) : ¬ WriteOutcome ⟨fun _ => ⟨[], .fin⟩, fun _ => ⟨true, false, false⟩⟩
    false [1, 2, 3] 2 errClosed c' := by
  simp [WriteOutcome]

/-- Allowed: a `Write` of 3 bytes returns 2 with a break's error, and the break kept both bytes:
the reader may read them [netsem: WriteBreakPartial]. -/
example : WriteOutcome Conn.fresh false [1, 2, 3] 2 errBroken
    ⟨fun s => if s = false then ⟨[1, 2], .cut⟩ else ⟨[], .cut⟩, Conn.fresh.ends⟩ := by
  refine ⟨by decide, .inr (.inr (.inr ⟨rfl, rfl, fun s => ?_⟩))⟩
  cases s <;> simp [Conn.fresh, Conn.setStream]

/-- A failed `Dial` may leave a connection pending (`Conn.abandoned`); its acceptor reads
`io.EOF` [netsem: DialTimeoutAccepted] ... -/
example : ReadOutcome Conn.abandoned true 8 [] errEOF Conn.abandoned := by
  simp [ReadOutcome, Conn.abandoned]

/-- ... and never data, with or without a break. -/
example (n : Nat) (data : List w8) (code : w64) (c₁ c' : Conn)
    (hb : BreakOrNot Conn.abandoned c₁) (h : ReadOutcome c₁ true n data code c') : data = [] := by
  have hbytes : (c₁.stream false).bytes = [] := by
    rcases hb with rfl | ⟨_, hb⟩
    · rfl
    · exact List.prefix_nil.mp (hb false).2
  unfold ReadOutcome at h
  simp only [Bool.not_true, hbytes] at h
  split at h
  · exact h.1
  split at h
  · exact h.1
  rcases h with ⟨_, rfl, _⟩ | ⟨_, _, hp, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩
  · rfl
  · exact List.prefix_nil.mp hp
  · rfl
  · rfl

/-- A wildcard host resolves to the node's own IP, port as spelled [netsem: NodeIdentity]. -/
example : listenAddr go!"10.0.0.1" go!":7000" = go!"10.0.0.1:7000" := by decide
example : listenAddr go!"10.0.0.1" go!"0.0.0.0:7000" = go!"10.0.0.1:7000" := by decide
example : listenAddr go!"10.0.0.1" go!"[::]:7000" = go!"10.0.0.1:7000" := by decide

/-- Any other address is bound as spelled: a literal address (the node's or another node's), and
other host spellings (which are then stuck unless configured). -/
example : listenAddr go!"10.0.0.1" go!"10.0.0.2:7000" = go!"10.0.0.2:7000" := by decide
example : listenAddr go!"10.0.0.1" go!"localhost:7000" = go!"localhost:7000" := by decide
example : listenAddr go!"10.0.0.1" go!"[0::0]:7000" = go!"[0::0]:7000" := by decide

/-- The address a listener is bound to here (its identity, `listenAddr`) is not what Go's
`ln.Addr().String()` reports for a wildcard `Listen`: Go 1.27.3 reports `"[::]:7000"` for each of
the three spellings (measured in a private netns; `TrustedCode/net.lean`). So the `net` model's
`(*TCPListener).Addr` spec (`Proof/net/TCPListener__Addr.lean`) leaves the string arbitrary rather
than equal to the bound address. -/
example : listenAddr go!"10.0.0.1" go!":7000" ≠ go!"[::]:7000" := by decide
example : listenAddr go!"10.0.0.1" go!"0.0.0.0:7000" ≠ go!"[::]:7000" := by decide
example : listenAddr go!"10.0.0.1" go!"[::]:7000" ≠ go!"[::]:7000" := by decide
/-- Nor, for a named host, the spelled string: `Listen("localhost:7000")` reports
`"127.0.0.1:7000"`. -/
example : listenAddr go!"10.0.0.1" go!"localhost:7000" ≠ go!"127.0.0.1:7000" := by decide

end Perennial.NetConn
