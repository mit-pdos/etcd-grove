/-
# kvudp's datagrams, pure (2026-11-24, `notes/kvudp-proof-plan.md`)

The pure models of `udptransport.go`'s datagram format and of its address parsing, which the specs of
`putHeader`, `putFragment`, `putAck`, `getDatagram`, `fragments`, `parseAddr` and `udpAddr` are stated
in, and the laws the transport's proofs use (stated here, proved in phase 2: `sorry` until then).

* `headerBytes`, `fragBytes`, `ackBytes`: what `putHeader`, `putFragment`, `putAck` write.
* `DgM`, `parseDg b`: what `getDatagram(b)` reads back (`none`: `ok` false). `DgM.key`: the message a
  fragment names, `(from, boot, seq)`.
* `nChunks body`, `chunkAt body i`, `fragsOf src dst boot seq body`: `fragments`' chunking (`[]`: Go's
  `nil`, a body that is empty or needs more than `maxFragmentsN` chunks).
* `FragOf body dg`: the fragment `dg` is the `dg.index`-th chunk of `body`, of `nChunks body`.
* `bootVal v n`: the boot counter's file contents `v` (`durable`'s, `none`: no file) hold `n`.
* `parseAddrM a`: `parseAddr(a)`: the IPv4 bytes and port of an address `Net.addrOk` accepts.

The laws: `parseDg_fragBytes`/`parseDg_ackBytes` (round trips), `parseDg_length` (whatever parses is
at most `maxDatagramN` bytes: what arrives intact, `Udp.intactMax`), `fragsOf_ok` (every fragment of a
body parses as one of its chunks, and is short enough), `chunks_flatten` (the chunks, in order, are
the body), `parseAddrM_ok` (`ValidDest` from `addrOk`).
-/
module

public import GooseLang.Ext.Udp.Impl
public import Perennial.Std.Word.LittleEndian

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Net Udp

/-! ## The format's constants (`udptransport.go`) -/

/-- `maxDatagram`: the largest datagram sent (`Udp.intactMax`: it arrives intact). -/
def maxDatagramN : Nat := 524
/-- `chunkSize`: a fragment's largest chunk. -/
def chunkSizeN : Nat := 479
/-- `ackLen`: the header's length, an ack's. -/
def ackLenN : Nat := 37
/-- `fragHeaderLen`: a fragment's length before its chunk. -/
def fragHeaderLenN : Nat := 45
/-- `maxFragments`: the most fragments of a message. -/
def maxFragmentsN : Nat := 2 ^ 14
/-- `udpMagic`. -/
def udpMagicW : w32 := W32 0x4455564b
/-- `kindFragment`. -/
def kindFragmentB : w8 := W8 1
/-- `kindAck`. -/
def kindAckB : w8 := W8 2

theorem maxDatagramN_intact : maxDatagramN = intactMax := rfl

/-! ## Writing -/

/-- `putHeader`'s bytes. -/
def headerBytes (kind : w8) (src dst boot seq : w64) : List w8 :=
  u32Le udpMagicW ++ [kind] ++ u64Le src ++ u64Le dst ++ u64Le boot ++ u64Le seq

/-- `putFragment`'s bytes. -/
def fragBytes (src dst boot seq : w64) (index total : w32) (chunk : List w8) : List w8 :=
  headerBytes kindFragmentB src dst boot seq ++ u32Le index ++ u32Le total ++ chunk

/-- `putAck`'s bytes. -/
def ackBytes (src dst boot seq : w64) : List w8 := headerBytes kindAckB src dst boot seq

/-! ## Reading -/

/-- A datagram read back (`getDatagram`'s `datagram`; `src` is Go's `from`, `dst` its `to`). An ack's
`index`, `total` are 0 and its `chunk` empty (Go's nil). -/
structure DgM where
  kind : w8
  src : w64
  dst : w64
  boot : w64
  seq : w64
  index : w32
  total : w32
  chunk : List w8

/-- The message a datagram names: its sender, boot and sequence numbers. -/
def DgM.key (d : DgM) : w64 × w64 × w64 := (d.src, d.boot, d.seq)

/-- The 8 bytes of `b` at `off`, as a little-endian word. -/
def u64At (b : List w8) (off : Nat) : w64 := leToU64 ((b.drop off).take 8)

/-- The 4 bytes of `b` at `off`, as a little-endian word. -/
def u32At (b : List w8) (off : Nat) : w32 := leToU32 ((b.drop off).take 4)

/-- **`getDatagram(b)`** (see the file header): the datagram, or `none` for anything `putFragment` or
`putAck` did not write (a fragment's chunk empty or longer than `chunkSizeN`, its index not below its
total, its total 0 or above `maxFragmentsN`). -/
def parseDg (b : List w8) : Option DgM :=
  if b.length < ackLenN ∨ u32At b 0 ≠ udpMagicW then none
  else
    let kind := b.getD 4 0
    let src := u64At b 5
    let dst := u64At b 13
    let boot := u64At b 21
    let seq := u64At b 29
    if kind = kindAckB then
      if b.length = ackLenN then some ⟨kind, src, dst, boot, seq, 0, 0, []⟩ else none
    else if kind ≠ kindFragmentB ∨ b.length ≤ fragHeaderLenN ∨
        fragHeaderLenN + chunkSizeN < b.length then none
    else
      let index := u32At b ackLenN
      let total := u32At b (ackLenN + 4)
      if total.toNat = 0 ∨ maxFragmentsN < total.toNat ∨ total.toNat ≤ index.toNat then none
      else some ⟨kind, src, dst, boot, seq, index, total, b.drop fragHeaderLenN⟩

/-! ## Chunking -/

/-- How many chunks `body` is cut into. -/
def nChunks (body : List w8) : Nat := (body.length + chunkSizeN - 1) / chunkSizeN

/-- The `i`-th chunk of `body`. -/
def chunkAt (body : List w8) (i : Nat) : List w8 := (body.drop (i * chunkSizeN)).take chunkSizeN

/-- **`fragments(src, dst, boot, seq, body)`**: the fragments of the message, `[]` (Go's nil) if
`body` is empty or needs more than `maxFragmentsN` of them. -/
def fragsOf (src dst boot seq : w64) (body : List w8) : List (List w8) :=
  if nChunks body = 0 ∨ maxFragmentsN < nChunks body then []
  else (List.range (nChunks body)).map fun (i : Nat) =>
    fragBytes src dst boot seq (W32 (i : Int)) (W32 ((nChunks body : Nat) : Int)) (chunkAt body i)

/-- **The fragment `dg` is a chunk of `body`** (see the file header). -/
def FragOf (body : List w8) (dg : DgM) : Prop :=
  dg.kind = kindFragmentB ∧ dg.total.toNat = nChunks body ∧
    dg.index.toNat < nChunks body ∧ dg.chunk = chunkAt body dg.index.toNat

/-! ## The boot counter's file -/

/-- **The boot counter's file contents `v` hold `n`** (`nextBoot`): no file and `n = 0`, or the 8
bytes of `n`. -/
def bootVal (v : Option GoString) (n : w64) : Prop :=
  (v = none ∧ n = W64 0) ∨ v = some (u64Le n)

/-! ## Addresses -/

/-- **`parseAddr(a)`**: the IPv4 bytes and the port of `a`, if `Net.addrOk` accepts it; Go's `ok` is
`(parseAddrM a).isSome`. The bytes are the address's four numerals, the port its fifth. -/
def parseAddrM (a : GoString) : Option (List w8 × w64) :=
  if addrOk a = true then
    match (splitBy 58 a []) with
    | [h, p] =>
      match (splitBy 46 h []).map decNat, decNat p with
      | [some b1, some b2, some b3, some b4], some pt =>
        some ([W8 b1, W8 b2, W8 b3, W8 b4], W64 pt)
      | _, _ => none
    | _ => none
  else none

/-! ## The laws (phase 2) -/

theorem fragBytes_length (src dst boot seq : w64) (index total : w32) (chunk : List w8) :
    (fragBytes src dst boot seq index total chunk).length = fragHeaderLenN + chunk.length := by
  sorry

theorem ackBytes_length (src dst boot seq : w64) :
    (ackBytes src dst boot seq).length = ackLenN := by
  sorry

/-- What `putFragment` writes, `getDatagram` reads back. -/
theorem parseDg_fragBytes (src dst boot seq : w64) (index total : w32) (chunk : List w8)
    (hc : chunk ≠ []) (hcl : chunk.length ≤ chunkSizeN) (ht : 0 < total.toNat)
    (htm : total.toNat ≤ maxFragmentsN) (hi : index.toNat < total.toNat) :
    parseDg (fragBytes src dst boot seq index total chunk) =
      some ⟨kindFragmentB, src, dst, boot, seq, index, total, chunk⟩ := by
  sorry

/-- What `putAck` writes, `getDatagram` reads back. -/
theorem parseDg_ackBytes (src dst boot seq : w64) :
    parseDg (ackBytes src dst boot seq) = some ⟨kindAckB, src, dst, boot, seq, 0, 0, []⟩ := by
  sorry

/-- What parses is short enough to arrive intact. -/
theorem parseDg_length {b : List w8} {dg : DgM} (h : parseDg b = some dg) :
    b.length ≤ maxDatagramN := by
  sorry

/-- What parses is an ack or a fragment. -/
theorem parseDg_kind {b : List w8} {dg : DgM} (h : parseDg b = some dg) :
    dg.kind = kindAckB ∨ (dg.kind = kindFragmentB ∧ dg.index.toNat < dg.total.toNat) := by
  sorry

/-- Every fragment of a body is short enough and parses as one of its chunks, under the message's
name. -/
theorem fragsOf_ok (src dst boot seq : w64) (body : List w8) :
    ∀ d ∈ fragsOf src dst boot seq body, d.length ≤ maxDatagramN ∧
      ∃ dg, parseDg d = some dg ∧ dg.key = (src, boot, seq) ∧ dg.dst = dst ∧ FragOf body dg := by
  sorry

/-- `fragments` gives nil only for an empty body or one too long. -/
theorem fragsOf_nil (src dst boot seq : w64) (body : List w8) :
    fragsOf src dst boot seq body = [] ↔ (body = [] ∨ maxFragmentsN < nChunks body) := by
  sorry

/-- The chunks, in order, are the body. -/
theorem chunks_flatten (body : List w8) :
    ((List.range (nChunks body)).map (chunkAt body)).flatten = body := by
  sorry

/-- A chunk of a body is nonempty and at most `chunkSizeN` bytes. -/
theorem chunkAt_length (body : List w8) (i : Nat) (hi : i < nChunks body) :
    chunkAt body i ≠ [] ∧ (chunkAt body i).length ≤ chunkSizeN := by
  sorry

/-- `parseAddr` accepts exactly what `AddrOk` does, and its bytes and port make the address. -/
theorem parseAddrM_ok (a : GoString) :
    (parseAddrM a).isSome = addrOk a ∧
      ∀ ip port, parseAddrM a = some (ip, port) → ValidDest ip port a ∧ ip.length = 4 := by
  sorry

end raft_kvnet
end EtcdGrove
end Perennial
