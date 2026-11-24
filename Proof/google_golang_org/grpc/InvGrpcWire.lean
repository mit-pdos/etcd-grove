/-
**grpc's wire as net-library protocols** (phase 7 S2's core; `notes/phase7-plan.md`, "S2 draft
signatures", §1.2, as amended in §0a): what the grpc model (`models/grpc`) writes on a connection,
as Lean functions of its Go code's bytes, and the protocols (`Net.Proto`) of a connection to an
address that serves a table of unary methods `Svc`, with the unary call's deposit in the
connection's slot (`GooseLang/Ext/Net/Slot.lean`). Definitions and their laws; no axiom (two opaques, `grpcCliPI`/`grpcSrvPI`, below).

**The model's bytes** (`models/grpc/model_wire.go`; one stream per connection). A frame is a kind
byte and a body. `be32 n` is `binary.BigEndian.AppendUint32(nil, uint32(n))`; `headerBlock kind fs`
is `appendHeaderBlock(nil, kind, fs)` (its length and count as `uint32`s, then each field as two
length-prefixed strings); `grpcMsgHdr bs` the 5-byte gRPC message header of an uncompressed
message (`msgHeader`: flag `0`, the length); `dataFrame bs` `appendData(nil, grpcMsgHdr bs, bs)`.
The client writes `clientPrefaceBytes` (`clientPreface`), then `headFrame fs`
(`newClientTransportStream`, one write), then `dataFrame bs ++ closeFrame` (`csAttempt.sendMsg` of
a unary call: `Write(hdr, payld, Last: true)`, one write), and maybe `cancelFrame` (a `Close` with
an error). The server writes `settingsBytes` (`handleRawConn`), then header, data, trailer and reset
frames (`SrvFrame`).

**Header fields.** `pathOf fs`: the method (`operateHeaders`' last `:path`); `fieldLast fs k`, the
last value of `k`; `fieldVals fs k`, all of `k`'s values in order. `grpcFieldsMd fs md`: the
incoming metadata `md` the server's `operateHeaders` makes of `fs`, on every key grpc does not set
itself (`grpcReservedKey`), as `grpcAttemptMd` states it on the client's side: the values of the
key's fields, base64-decoded for a `-bin` key (stated through the encoder: the field values are the
raw standard encodings `b64Raw` of the metadata's, which is what grpc's client writes,
`encodeBinHeader`); and no key with no values. `grpcMsgDecode` is `decodeGrpcMessage` (the
`grpc-message` field's percent-decoding, `model_http_util.go`).

**The protocols.** `grpcCliP Svc` (what a dialer writes): a prefix of the preface; or the preface,
a head `fs`, and a rest that, if `fs` names a unary method of `Svc` (`grpcUnaryOf Svc fs`), is empty,
a cancel, or one data frame of bytes `bs` carrying the attempt's slot (`grpcAttemptSlot Svc cn fs
bs`), then anything. The slot holds the deposit, `▷` the method's spec at every metadata the server
may make of `fs` (`grpcDeposit`), claimable once the server read the whole data frame (`msgReady fs
bs`: correction 1 of §0a, the deposit rides with the message, to the server's `dec`), and its
outcome `GrpcOut` (`.ok bs'`: a reply some `m'` encodes to, with `Φ m'`; `.err d`: a handler's
description's `Ψe d`, `grpcSlotCont`). `grpcSrvP Svc` (what an acceptor writes): a prefix of its
preface, or its preface and whole frames, each meeting `srvFrameOk`: a data frame answers the slot
`.ok` with its bytes, a trailer whose decoded `grpc-message` is a handler's description answers it
`.err`, unless the connection's head is no unary method of `Svc` (`streamConn`); a `REFUSED_STREAM`
reset (code 7) says the server refused the connection (`connRefused`).

**Addresses.** `grpcAddrAt a Svc` (persistent): `a`'s protocols are grpc's for `Svc` as the S2
interface states them, the **opaque** `grpcCliPI Svc`/`grpcSrvPI Svc` (trusted text with no law,
`notes/audit.md`; their intended reading is `grpcCliP Svc`/`grpcSrvP Svc`, which take their place
once S2 proves `ClientConn.Invoke` and `Server.Serve` over the model: over the defined protocols,
a raw Go program could dial or listen on a grpc address and write or read the model's frames, a
head with no data frame or a reader expecting `settingsBytes` of real HTTP/2, so an axiom over
`grpcAddrAt` would be unsound), and the slot map exists; until then `grpcCliP`/`grpcSrvP` and the
parse laws below are a library no address uses; set once from `addrUnset a` (`grpc_addr_set`). `grpcSvcAt a name Wq Wp Spec`
(persistent, heap-free): the table `a` serves has an entry for `name` at the wire parts `Wq`, `Wp`,
and a caller of `Spec` meets it after an update (`grpcSvcAt_of_addr`, `grpcSvcAt_mono_upd`).

**Parsing.** A well-formed head (`headOk`: its block's length fits its `uint32`; the model's
check before it writes a block, `headerListOk`, gives it: `headOk_of_listOk`, F1 of §0a) and a data
frame of a message below `2 ^ 32` bytes are determined by their bytes (`head_prefix_inj`,
`dataFrame_prefix_inj`), so: a server that read the preface, a unary head and a data frame has the
attempt's slot (`cli_read_slot`); a client on its unary attempt's connection that reads a server's
data frame or a trailer with a handler's description has its slot's answer
(`srv_data_answered`, `srv_trailer_answered`; `streamConn_unary`).

**Not yet** (S2's later steps): the parse of the server's frame sequence (a client's read of
`settingsBytes` and whole frames gives each frame's `srvFrameOk`; the server's blocks are within
the limit, or the marker `.oversized`, since F1's fix), the client attempt's proof (`newClientTransportStream`,
`createHeaderFields`), and the codec's laws for `protoEncodes` (O7: a message's wire part is its
tree, `ProtoMsg.wire`, O3, and its bytes are any `protoEncodes` relates to the tree, an opaque
relation in `Store.lean` with no law yet).
-/
module

public import GooseLang.Ext.Net.Slot
public import Proof.google_golang_org.grpc.InvGrpcBase
public import Proof.google_golang_org.grpc.InvGrpcCall
public import Proof.encoding.base64.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

/-! ## The model's bytes -/

/-- `binary.BigEndian.AppendUint32(nil, uint32(n))`. -/
def be32 (n : Nat) : List w8 :=
  [BitVec.ofNat 8 (n / 2 ^ 24), BitVec.ofNat 8 (n / 2 ^ 16), BitVec.ofNat 8 (n / 2 ^ 8),
    BitVec.ofNat 8 n]

@[simp] theorem be32_length (n : Nat) : (be32 n).length = 4 := rfl

/-- `be32` is the reverse of the little-endian encoding (what `binary.BigEndian.AppendUint32`
appends: `Spec/encoding/binary/bigEndian__AppendUint32.lean`). -/
theorem u32Le_reverse (v : w32) : (u32Le v).reverse = be32 (uint.nat v) := by
  simp only [u32Le, u32LeDef, LittleEndian.split, be32, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, Nat.div_div_eq_div_mul]

/-- `be32` sees its argument modulo `2 ^ 32`. -/
theorem be32_mod (n : Nat) : be32 (n % 2 ^ 32) = be32 n := by
  simp only [be32, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;>
    omega

/-- HTTP/2's client connection preface (`clientPreface`). -/
def clientPrefaceBytes : List w8 := go!"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"

/-- The frame kinds (`model_wire.go`). -/
def frameHead : w8 := 1
def frameData : w8 := 2
def frameClose : w8 := 3
def frameCancel : w8 := 4
def frameHeader : w8 := 5
def frameTrailer : w8 := 6
def frameReset : w8 := 7
def frameSettings : w8 := 8

/-- The server's preface (`handleRawConn`: `rawConn.Write([]byte{frameSettings})`). -/
def settingsBytes : List w8 := [frameSettings]

/-- One header field's encoding in a header block. -/
def fieldBytes (f : GoString × GoString) : List w8 :=
  be32 f.1.length ++ f.1 ++ be32 f.2.length ++ f.2

/-- `appendHeaderBlock(nil, kind, fs)`. -/
def headerBlock (kind : w8) (fs : List (GoString × GoString)) : List w8 :=
  kind :: be32 (4 + (fs.map fun f => 8 + f.1.length + f.2.length).sum) ++ be32 fs.length ++
    (fs.map fieldBytes).flatten

/-- The client's head frame. -/
def headFrame (fs : List (GoString × GoString)) : List w8 := headerBlock frameHead fs

/-- The 5-byte header of an uncompressed gRPC message (`msgHeader`). -/
def grpcMsgHdr (bs : List w8) : List w8 := 0 :: be32 bs.length

/-- A data frame of the message `bs` (`appendData`). -/
def dataFrame (bs : List w8) : List w8 := frameData :: grpcMsgHdr bs ++ bs

def closeFrame : List w8 := [frameClose]
def cancelFrame : List w8 := [frameCancel]

/-- HTTP/2's `REFUSED_STREAM` error code (`errCodeRefusedStream`). -/
def errCodeRefusedStream : Nat := 7

/-- `maxHeaderBlock`: the receivers' limit on a header list (16 MiB). -/
def maxHeaderBlock : Nat := 16 * 2 ^ 20

/-- **A header list within the receiver's limit** (`¬ headerListTooLarge(fs)`, the model's check
before it writes a block: `model_wire.go`, F1 of `notes/phase7-plan.md` §0a), counted as HTTP/2
does: name, value and 32 per field. -/
def headerListOk (fs : List (GoString × GoString)) : Prop :=
  (fs.map fun f => 32 + f.1.length + f.2.length).sum ≤ maxHeaderBlock

/-- The fields of a slice of the model's `headerField`s. -/
def hfPairs [GooseExts] (hs : List google_golang_org.grpc.headerField) : List (GoString × GoString) :=
  hs.map fun h => (h.Name', h.Value')

/-- A frame the server writes. -/
inductive SrvFrame where
  | header (fs : List (GoString × GoString))
  | data (bs : List w8)
  | trailer (fs : List (GoString × GoString))
  | reset (code : Nat)
  /-- The marker of a header (`kind = frameHeader`) or trailer block over the client's limit, which
  the server did not send (`appendOversizedBlock`). -/
  | oversized (kind : w8)

/-- A server frame's bytes (`writeHeaderBlock`, `Write`, `WriteStatus`/`writeEarlyAbort`,
`appendReset`). -/
def srvFrameBytes : SrvFrame → List w8
  | .header fs => headerBlock frameHeader fs
  | .data bs => dataFrame bs
  | .trailer fs => headerBlock frameTrailer fs
  | .reset c => frameReset :: be32 c
  | .oversized k => k :: be32 (maxHeaderBlock + 1)

/-! ## Header fields -/

/-- All the values of the key `k`, in order. -/
def fieldVals (fs : List (GoString × GoString)) (k : GoString) : List GoString :=
  (fs.filter fun f => f.1 = k).map (·.2)

/-- The last value of the key `k`. -/
def fieldLast (fs : List (GoString × GoString)) (k : GoString) : Option GoString :=
  (fieldVals fs k).getLast?

/-- The method a head names (`operateHeaders`: the last `:path`). -/
def pathOf (fs : List (GoString × GoString)) : Option GoString := fieldLast fs go!":path"

/-- `base64.RawStdEncoding.EncodeToString` (no padding): base64's `rawStdEnc`, the definition
base64's package fact gives `RawStdEncoding.EncodeToString`. -/
abbrev b64Raw (d : List w8) : List w8 := _root_.Perennial.encoding.base64.rawStdEnc d

/-- **The incoming metadata `md` the server makes of the head `fs`** (`operateHeaders`), on every key
grpc does not set itself (see the file header). -/
def grpcFieldsMd (fs : List (GoString × GoString)) (md : GrpcMd) : Prop :=
  (∀ k, ¬ grpcReservedKey k →
    if go!"-bin" <:+ k then fieldVals fs k = (metadata.mdVals md k).map b64Raw
    else metadata.mdVals md k = fieldVals fs k) ∧
  ∀ k, mdGet md k ≠ some []

/-- A hexadecimal digit's value (`strconv.ParseUint(_, 16, 8)` on one digit). -/
def hexVal (c : w8) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

/-- `decodeGrpcMessage` (`model_http_util.go`): each `%` followed by two hexadecimal digits is the
byte they denote; everything else is kept. -/
def grpcMsgDecode : List w8 → List w8
  | c :: a :: b :: rest =>
    if c = 37 then
      match hexVal a, hexVal b with
      | some x, some y => BitVec.ofNat 8 (16 * x + y) :: grpcMsgDecode rest
      | _, _ => c :: grpcMsgDecode (a :: b :: rest)
    else c :: grpcMsgDecode (a :: b :: rest)
  | l => l
termination_by l => l.length

/-! ## Parsing: a well-formed head is determined by its bytes -/

/-- **A head grpc frames faithfully**: its block's length fits the `uint32` it is written as
(`appendHeaderBlock` truncates it otherwise: `notes/phase7-plan.md`, §0a, finding F1). -/
def headOk (fs : List (GoString × GoString)) : Prop :=
  4 + (fs.map fun f => 8 + f.1.length + f.2.length).sum < 2 ^ 32

theorem be32_inj {n m : Nat} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32) (h : be32 n = be32 m) :
    n = m := by
  simp only [be32, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  have e3 := congrArg BitVec.toNat h3
  have e4 := congrArg BitVec.toNat h4
  simp only [BitVec.toNat_ofNat] at e1 e2 e3 e4
  omega

theorem be32_append_inj {n m : Nat} {x y : List w8} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32)
    (h : be32 n ++ x = be32 m ++ y) : n = m ∧ x = y := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨be32_inj hn hm h1, h2⟩

theorem fieldBytes_append_inj {f f' : GoString × GoString} {x y : List w8}
    (h1 : f.1.length < 2 ^ 32) (h2 : f.2.length < 2 ^ 32) (h1' : f'.1.length < 2 ^ 32)
    (h2' : f'.2.length < 2 ^ 32) (h : fieldBytes f ++ x = fieldBytes f' ++ y) :
    f = f' ∧ x = y := by
  simp only [fieldBytes, List.append_assoc] at h
  obtain ⟨hl1, h⟩ := be32_append_inj h1 h1' h
  obtain ⟨hn, h⟩ := List.append_inj h hl1
  obtain ⟨hl2, h⟩ := be32_append_inj h2 h2' h
  obtain ⟨hv, h⟩ := List.append_inj h hl2
  exact ⟨Prod.ext hn hv, h⟩

/-- Each field of a well-formed head fits a `uint32`. -/
theorem headOk_field {fs : List (GoString × GoString)} (h : headOk fs) :
    ∀ f ∈ fs, f.1.length < 2 ^ 32 ∧ f.2.length < 2 ^ 32 := by
  intro f hf
  have hle : ∀ (l : List (GoString × GoString)), f ∈ l →
      8 + f.1.length + f.2.length ≤ (l.map fun f => 8 + f.1.length + f.2.length).sum := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons g l ih =>
      simp only [List.mem_cons] at hl
      simp only [List.map_cons, List.sum_cons]
      rcases hl with rfl | hl
      · omega
      · have := ih hl; omega
  have := hle fs hf
  unfold headOk at h
  omega

theorem fieldsBytes_append_inj : ∀ {fs fs' : List (GoString × GoString)} {x y : List w8},
    fs.length = fs'.length →
    (∀ f ∈ fs, f.1.length < 2 ^ 32 ∧ f.2.length < 2 ^ 32) →
    (∀ f ∈ fs', f.1.length < 2 ^ 32 ∧ f.2.length < 2 ^ 32) →
    (fs.map fieldBytes).flatten ++ x = (fs'.map fieldBytes).flatten ++ y → fs = fs' ∧ x = y
  | [], [], _, _, _, _, _, h => by simpa using h
  | f :: fs, f' :: fs', x, y, hl, hb, hb', h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    have ⟨b1, b2⟩ := hb f (by simp)
    have ⟨b1', b2'⟩ := hb' f' (by simp)
    obtain ⟨rfl, h2⟩ := fieldBytes_append_inj b1 b2 b1' b2' h
    obtain ⟨rfl, rfl⟩ := fieldsBytes_append_inj (by simpa using hl)
      (fun g hg => hb g (by simp [hg])) (fun g hg => hb' g (by simp [hg])) h2
    exact ⟨rfl, rfl⟩

/-- **The model's check makes a head well formed**: a list within the limit has a block whose
length fits its `uint32` (F1). -/
theorem headOk_of_listOk {fs : List (GoString × GoString)} (h : headerListOk fs) : headOk fs := by
  unfold headerListOk maxHeaderBlock at h
  unfold headOk
  have : (fs.map fun f => 8 + f.1.length + f.2.length).sum ≤
      (fs.map fun f => 32 + f.1.length + f.2.length).sum := by
    clear h
    induction fs with
    | nil => simp
    | cons f fs ih => simp only [List.map_cons, List.sum_cons]; omega
  omega

theorem headOk_length {fs : List (GoString × GoString)} (h : headOk fs) : fs.length < 2 ^ 32 := by
  unfold headOk at h
  have : 8 * fs.length ≤ (fs.map fun f => 8 + f.1.length + f.2.length).sum := by
    clear h
    induction fs with
    | nil => simp
    | cons f fs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  omega

/-- **A header block is determined by its bytes**: two well-formed blocks of a kind, followed by
`x` and by `y`, with the same bytes, are the same block, followed by the same bytes. -/
theorem headerBlock_append_inj {k : w8} {fs fs' : List (GoString × GoString)} {x y : List w8}
    (hok : headOk fs) (hok' : headOk fs') (h : headerBlock k fs ++ x = headerBlock k fs' ++ y) :
    fs = fs' ∧ x = y := by
  simp only [headerBlock, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  obtain ⟨-, h⟩ := be32_append_inj hok hok' h
  obtain ⟨hc, h⟩ := be32_append_inj (headOk_length hok) (headOk_length hok') h
  exact fieldsBytes_append_inj hc (headOk_field hok) (headOk_field hok') h

/-- The same, for a block that is a prefix of another followed by `y`. -/
theorem headerBlock_prefix_inj {k : w8} {fs fs' : List (GoString × GoString)} {y : List w8}
    (hok : headOk fs) (hok' : headOk fs') (h : headerBlock k fs <+: headerBlock k fs' ++ y) :
    fs = fs' := by
  obtain ⟨z, hz⟩ := h
  exact (headerBlock_append_inj hok hok' hz).1

/-- **A client's head is determined by its bytes**: a well-formed head after the preface, a prefix
of another well-formed head after the preface followed by anything, is that head. -/
theorem head_prefix_inj {fs fs' : List (GoString × GoString)} {y : List w8}
    (hok : headOk fs) (hok' : headOk fs')
    (h : clientPrefaceBytes ++ headFrame fs <+: clientPrefaceBytes ++ headFrame fs' ++ y) :
    fs = fs' := by
  rw [List.append_assoc, List.prefix_append_right_inj] at h
  exact headerBlock_prefix_inj hok hok' h

/-- **A data frame is determined by its bytes** (a message below `2 ^ 32` bytes). -/
theorem dataFrame_prefix_inj {bs bs' : List w8} {y : List w8} (h : bs.length < 2 ^ 32)
    (h' : bs'.length < 2 ^ 32) (hp : dataFrame bs <+: dataFrame bs' ++ y) : bs = bs' := by
  obtain ⟨z, hz⟩ := hp
  simp only [dataFrame, grpcMsgHdr, List.cons_append, List.cons.injEq, true_and,
    List.append_assoc] at hz
  obtain ⟨hl, hz⟩ := be32_append_inj h h' hz
  exact (List.append_inj hz hl).1

/-- What `appendData` appends, with the header of the message `bs` and `bs` itself, is
`dataFrame bs`. -/
theorem appendData_dataFrame (vs bs : List w8) :
    vs ++ frameData :: (grpcMsgHdr bs ++ bs) = vs ++ dataFrame bs := by
  simp [dataFrame]

theorem dataFrame_length (bs : List w8) : (dataFrame bs).length = 6 + bs.length := by
  simp [dataFrame, grpcMsgHdr]; omega

/-! ### What `appendHeaderBlock`'s loops build (its proof's invariants) -/

/-- The block length's sum over the first `n` fields. -/
def hbLenPre (fs : List (GoString × GoString)) (n : Nat) : Nat :=
  ((fs.take n).map fun f => 8 + f.1.length + f.2.length).sum

/-- The bytes of the first `n` fields. -/
def hbBytesPre (fs : List (GoString × GoString)) (n : Nat) : List w8 :=
  ((fs.take n).map fieldBytes).flatten

theorem hbLenPre_succ (fs : List (GoString × GoString)) (n : Nat) (h : n < fs.length) :
    hbLenPre fs (n + 1) = hbLenPre fs n + (8 + fs[n].1.length + fs[n].2.length) := by
  unfold hbLenPre
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append]
  simp

theorem hbBytesPre_succ (fs : List (GoString × GoString)) (n : Nat) (h : n < fs.length) :
    hbBytesPre fs (n + 1) = hbBytesPre fs n ++ fieldBytes fs[n] := by
  unfold hbBytesPre
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append]
  simp

/-- The sum of `8 + …` is at most the list's size (`32 + …`). -/
theorem hbLenPre_le (fs : List (GoString × GoString)) (n : Nat) :
    hbLenPre fs n ≤ (fs.map fun f => 32 + f.1.length + f.2.length).sum := by
  unfold hbLenPre
  induction fs generalizing n with
  | nil => simp
  | cons a fs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      have := ih n; omega

theorem hbLen_full (fs : List (GoString × GoString)) :
    hbLenPre fs fs.length = (fs.map fun f => 8 + f.1.length + f.2.length).sum := by
  simp [hbLenPre]

theorem hbBytes_full (fs : List (GoString × GoString)) :
    hbBytesPre fs fs.length = (fs.map fieldBytes).flatten := by
  simp [hbBytesPre]

/-- A list within the limit has at most `maxHeaderBlock / 32` fields. -/
theorem listOk_length (fs : List (GoString × GoString)) (h : headerListOk fs) :
    32 * fs.length ≤ maxHeaderBlock := by
  unfold headerListOk at h
  have : 32 * fs.length ≤ (fs.map fun f => 32 + f.1.length + f.2.length).sum := by
    clear h
    induction fs with
    | nil => simp
    | cons a fs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  omega

/-- Each field of a list within the limit is within it. -/
theorem listOk_field (fs : List (GoString × GoString)) (h : headerListOk fs) (n : Nat)
    (hn : n < fs.length) : 32 + fs[n].1.length + fs[n].2.length ≤ maxHeaderBlock := by
  unfold headerListOk at h
  have : 32 + fs[n].1.length + fs[n].2.length ≤
      (fs.map fun f => 32 + f.1.length + f.2.length).sum := by
    clear h
    induction fs generalizing n with
    | nil => simp at hn
    | cons a fs ih =>
      cases n with
      | zero => simp
      | succ n =>
        simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
        have := ih n (by simpa using hn); omega
  omega

/-! ## Outcomes, keys, readiness -/

/-- **What the server answered a unary attempt's slot**: a reply's bytes, or a handler's error
description. -/
inductive GrpcOut where
  | ok (bs : List w8)
  | err (d : GoString)
deriving DecidableEq

def GrpcOut.enc : GrpcOut → List w8 ⊕ GoString
  | .ok bs => .inl bs
  | .err d => .inr d

instance GrpcOut.countable : Pos.Countable GrpcOut :=
  .ofInjective (fun o => Pos.Countable.encode o.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    cases a <;> cases b <;> simp_all [GrpcOut.enc])

/-- A unary attempt's slot key: its head's fields and its request's bytes. -/
abbrev GrpcKey : Type := List (GoString × GoString) × List w8

/-- **The client has written its whole request message**: after this the server may claim. -/
def msgReady (fs : List (GoString × GoString)) (bs : List w8) (W : List w8) : Prop :=
  clientPrefaceBytes ++ headFrame fs ++ dataFrame bs <+: W

theorem msgReady_ready (fs : List (GoString × GoString)) (bs : List w8) :
    SlotReady (msgReady fs bs) where
  mono _ _ ha hab := ha.trans hab

/-! ## The service table -/

section svc
variable [GooseExts]
variable {GF : BundledGFunctors}

/-- **A message type's wire part** (no heap): its Go type, its model (countable: a call's queues are ghost lists of models), and its stored form (the tree `storeInto ty` writes for a
message of model `m`; its bytes are any `protoEncodes ty (tree m)` relates it to, O7). -/
structure ProtoWire where
  ty : go.GoType
  M : Type
  tree : M → VTree
  cnt : Pos.Countable M := by infer_instance

attribute [instance] ProtoWire.cnt

/-- **A message type's wire part** (no heap: its Go type, its model, its stored form). -/
abbrev ProtoMsg.wire {GF : BundledGFunctors} (T : ProtoMsg GF) : ProtoWire :=
  ⟨T.ty, T.M, T.tree, T.cnt⟩

/-- **A unary method of a service**: its messages' wire parts and its spec (no heap). -/
structure GrpcEntry (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF

/-- **A streaming method of a service** (no heap): its messages' wire
parts, the client's content `up i m` of its `i`-th request, the server's content `dn md γ j m` of its
`j`-th response at the metadata `md` the stream `γ` was dispatched with, and what a client learns of a
stream (`spec md γ Dn`, persistent where it is held). -/
structure GrpcStreamEntry (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  up : Nat → Wq.M → IProp GF
  dn : GrpcMd → StreamNames → Nat → Wp.M → IProp GF
  spec : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF

/-- **An entry of a service table**: a unary method or a streaming one (`notes/phase7-endstate.md`
§1.5 item 6: `GrpcMethod` is the start's list element). -/
inductive GrpcSvcEntry (GF : BundledGFunctors) [GooseExts] where
  | unary (e : GrpcEntry GF)
  | stream (e : GrpcStreamEntry GF)

/-- **A service table**: the methods by full name (`"/etcdserverpb.KV/Put"`), unary and streaming
(since phase 7, SW1). -/
abbrev GrpcSvc (GF : BundledGFunctors) [GooseExts] := GoString → Option (GrpcSvcEntry GF)

/-- The head `fs` names a unary method of `Svc`. -/
def grpcUnaryOf (Svc : GrpcSvc GF) (fs : List (GoString × GoString)) : Prop :=
  ∃ name e, pathOf fs = some name ∧ Svc name = some (.unary e)

/-- **What a unary attempt deposits** for the entry `e` and the head `fs`: its request's
precondition at every metadata the server may make of `fs`, a step later, after an update. -/
def grpcDeposit (e : GrpcEntry GF) (fs : List (GoString × GoString)) (m : e.Wq.M)
    (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF) : IProp GF :=
  iprop(▷ ∀ md, ⌜grpcFieldsMd fs md⌝ -∗ |==> e.spec md m Φ Ψe)

/-- **What the attempt gets back for an outcome**: a reply whose bytes are some `m'`'s, with
`Φ m'`; or, for a handler's description, its `Ψe`. -/
def grpcSlotCont (e : GrpcEntry GF) (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF) :
    GrpcOut → IProp GF
  | .ok bs => iprop(∃ m', ⌜protoEncodes e.Wp.ty (e.Wp.tree m') bs⌝ ∗ Φ m')
  | .err d => iprop(⌜d ∈ handlerDescs⌝ -∗ Ψe d)

/-- **What a dialer writes on a connection to an address serving `Svc`, as the S2 interface states
it** (opaque until S2 proves `ClientConn.Invoke` and `Server.Serve` over the model; then `grpcCliP
Svc` takes its place): the bytes grpc's own transport writes. Opaque so that no program but grpc's
transport writes or learns anything of such a connection. Trusted text, with no law
(`notes/audit.md`, beside `grpcRepliesFit`). -/
opaque grpcCliPI (Svc : GrpcSvc GF) : Net.Proto GF := fun _ _ => iprop(True)

/-- **What an acceptor writes** (opaque, as `grpcCliPI`; intended reading `grpcSrvP Svc`). Trusted
text, with no law. -/
opaque grpcSrvPI (Svc : GrpcSvc GF) : Net.Proto GF := fun _ _ => iprop(True)

end svc

/-! ## The protocols -/

section protos
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS] [σ : NetSlotGS]

/-- **The slot of a unary attempt on `cn`** (persistent): the head `fs` names `e`'s method, the
request's bytes `bs` are some `m`'s, and the slot holds the deposit at `fs`. -/
def grpcAttemptSlot (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (bs : List w8) : IProp GF :=
  iprop(∃ (name : GoString) (e : GrpcEntry GF) (γ : SlotNames) (m : e.Wq.M)
      (Φ : e.Wp.M → IProp GF) (Ψe : GoString → IProp GF),
    ⌜pathOf fs = some name ∧ Svc name = some (.unary e) ∧ protoEncodes e.Wq.ty (e.Wq.tree m) bs⌝ ∗
    depSlotOf (Gg := Gg) cn γ ((fs, bs) : GrpcKey) ∗
    depSlotInv (Gg := Gg) cn γ (msgReady fs bs) (grpcDeposit e fs m Φ Ψe) (grpcSlotCont e Φ Ψe))

/-- What a client may write after the head `fs` (see the file header). -/
def cliRest (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString)) (rest : List w8) :
    IProp GF :=
  iprop(⌜¬ grpcUnaryOf Svc fs⌝ ∨ ⌜rest = [] ∨ rest = cancelFrame⌝ ∨
    ∃ bs tl, ⌜rest = dataFrame bs ++ tl ∧ bs.length < 2 ^ 32⌝ ∗
      grpcAttemptSlot (Gg := Gg) Svc cn fs bs)

/-- **What a client writes** on a connection to an address serving `Svc`: every head well formed
(`headOk`). -/
def grpcCliP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: clientPrefaceBytes⌝ ∨
    ∃ fs rest, ⌜W = clientPrefaceBytes ++ headFrame fs ++ rest ∧ headOk fs⌝ ∗
      cliRest (Gg := Gg) Svc cn fs rest)

/-- The connection's client wrote a head that names no unary method of `Svc` (persistent). -/
def streamConn (Svc : GrpcSvc GF) (cn : Nat) : IProp GF :=
  iprop(∃ fs, sentLb (Gg := Gg) cn false (clientPrefaceBytes ++ headFrame fs) ∗
    ⌜headOk fs ∧ ¬ grpcUnaryOf Svc fs⌝)

/-- **What a server frame says** (see the file header). -/
def srvFrameOk (Svc : GrpcSvc GF) (cn : Nat) : SrvFrame → IProp GF
  | .header _ => iprop(True)
  | .data bs => iprop(streamConn (Gg := Gg) Svc cn ∨
      ∃ (γ : SlotNames) (k : GrpcKey), depSlotOf (Gg := Gg) cn γ k ∗
        slotDone (Gg := Gg) γ (GrpcOut.ok bs))
  | .trailer fs => iprop(streamConn (Gg := Gg) Svc cn ∨
      ∀ v, ⌜fieldLast fs go!"grpc-message" = some v ∧ grpcMsgDecode v ∈ handlerDescs⌝ -∗
        ∃ (γ : SlotNames) (k : GrpcKey), depSlotOf (Gg := Gg) cn γ k ∗
          slotDone (Gg := Gg) γ (GrpcOut.err (grpcMsgDecode v)))
  | .reset c => iprop(⌜c = errCodeRefusedStream⌝ -∗ connRefused (Gg := Gg) cn)
  | .oversized _ => iprop(True)

/-- **What a server writes** on a connection to an address serving `Svc`. -/
def grpcSrvP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: settingsBytes⌝ ∨
    ∃ frames : List SrvFrame, ⌜W = settingsBytes ++ (frames.map srvFrameBytes).flatten⌝ ∗
      [∗list] f ∈ frames, □ srvFrameOk (Gg := Gg) Svc cn f)

/-- **The address `a` serves `Svc`** (persistent): its protocols are grpc's for `Svc`, as the S2
interface states them (the opaque `grpcCliPI`/`grpcSrvPI`, so that a program other than grpc's
transport cannot use the address's protocols: a raw dialer writing a head and no data frame, a raw
reader expecting `settingsBytes` of real HTTP/2), and the slot map exists. -/
def grpcAddrAt (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(addrProto (Gg := Gg) a (grpcCliPI Svc) (grpcSrvPI Svc) ∗ depSlotsCtx (Gg := Gg))

/-- **The method `name` at `a` meets `Spec`** (persistent, no heap): the table `a` serves has an
entry for `name` at the wire parts `Wq`, `Wp`, and a caller of `Spec` meets that entry's spec after an
update. -/
def grpcSvcAt (a name : GoString) (Wq Wp : ProtoWire)
    (Spec : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ (Svc : GrpcSvc GF) (Spec₀ : GrpcMd → Wq.M → (Wp.M → IProp GF) →
      (GoString → IProp GF) → IProp GF),
    grpcAddrAt (Gg := Gg) a Svc ∗ ⌜Svc name = some (.unary ⟨Wq, Wp, Spec₀⟩)⌝ ∗
    □ ∀ md m Φ Ψe, Spec md m Φ Ψe ==∗ Spec₀ md m Φ Ψe)

/-- **The streaming method `name` at `a` meets `Up` and `Spec`** (persistent, no heap): the table `a`
serves has a stream entry for `name` at the wire parts `Wq`, `Wp`, whose
specification holds of every stream at its own content (`spec₀ md γ (dn₀ md γ)`), whose request
content a client of `Up` meets after an update, and whose specification gives `Spec`. -/
def grpcStreamSvcAt (a name : GoString) (Wq Wp : ProtoWire) (Up : Nat → Wq.M → IProp GF)
    (Spec : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ (Svc : GrpcSvc GF) (up₀ : Nat → Wq.M → IProp GF)
      (dn₀ : GrpcMd → StreamNames → Nat → Wp.M → IProp GF)
      (spec₀ : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF),
    grpcAddrAt (Gg := Gg) a Svc ∗ ⌜Svc name = some (.stream ⟨Wq, Wp, up₀, dn₀, spec₀⟩)⌝ ∗
    (□ ∀ md γ, spec₀ md γ (dn₀ md γ)) ∗
    (□ ∀ i m, Up i m ==∗ up₀ i m) ∗ (□ ∀ md γ Dn, spec₀ md γ Dn -∗ Spec md γ Dn))

instance grpcAttemptSlot_persistent Svc cn fs bs :
    Persistent (grpcAttemptSlot (Gg := Gg) Svc cn fs bs) := by
  unfold grpcAttemptSlot; infer_instance
instance cliRest_persistent Svc cn fs rest : Persistent (cliRest (Gg := Gg) Svc cn fs rest) := by
  unfold cliRest; infer_instance
instance grpcCliP_persistent Svc cn W : Persistent (grpcCliP (Gg := Gg) Svc cn W) := by
  unfold grpcCliP; infer_instance
instance streamConn_persistent Svc cn : Persistent (streamConn (Gg := Gg) Svc cn) := by
  unfold streamConn; infer_instance
instance grpcSrvP_persistent Svc cn W : Persistent (grpcSrvP (Gg := Gg) Svc cn W) := by
  unfold grpcSrvP; infer_instance
instance grpcAddrAt_persistent a Svc : Persistent (grpcAddrAt (Gg := Gg) a Svc) := by
  unfold grpcAddrAt; infer_instance
instance grpcSvcAt_persistent a name Wq Wp Spec :
    Persistent (grpcSvcAt (Gg := Gg) a name Wq Wp Spec) := by
  unfold grpcSvcAt; infer_instance
instance grpcStreamSvcAt_persistent a name Wq Wp Up Spec :
    Persistent (grpcStreamSvcAt (Gg := Gg) a name Wq Wp Up Spec) := by
  unfold grpcStreamSvcAt; infer_instance

end protos

/-! ## The laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS] [σ : NetSlotGS]

/-- **The start law**: an unset address is set to serve `Svc` (`addr_set_proto`). -/
theorem grpc_addr_set (E : CoPset) (a : GoString) (Svc : GrpcSvc GF) :
    ⊢ regCtx (Gg := Gg) -∗ depSlotsCtx (Gg := Gg) -∗ addrUnset (Gg := Gg) a ={E}=∗
      grpcAddrAt (Gg := Gg) a Svc := by
  iintro #Hreg #Hs Hu
  imod addr_set_proto E a (grpcCliPI Svc) (grpcSrvPI Svc) $$ Hreg Hu with #Hp
  imodintro
  unfold grpcAddrAt
  iframe Hp Hs

/-- **A unary attempt's connection is no stream connection**: its client wrote a well-formed head
naming a unary method of `Svc`, so the server's frames answer its slot. -/
theorem streamConn_unary (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (hok : headOk fs) (hu : grpcUnaryOf Svc fs) :
    sentLb (Gg := Gg) cn false (clientPrefaceBytes ++ headFrame fs) ∗ streamConn (Gg := Gg) Svc cn ⊢
      (False : IProp GF) := by
  unfold streamConn
  iintro ⟨#H1, %fs', #H2, %hfs'⟩
  icases sentLb_agree cn false (clientPrefaceBytes ++ headFrame fs)
    (clientPrefaceBytes ++ headFrame fs') $$ [H1 H2] with %h
  · iframe H1 H2
  exfalso
  obtain ⟨hok', hnu⟩ := hfs'
  rcases h with h | h
  · exact hnu (head_prefix_inj (y := []) hok hok' (by simpa using h) ▸ hu)
  · exact hnu (head_prefix_inj (y := []) hok' hok (by simpa using h) ▸ hu)

/-- **The server reads a unary request whole**: what it read, the preface, a well-formed head
naming a unary method of `Svc` and a data frame, met the client's protocol, so the data frame
carries the attempt's slot. -/
theorem cli_read_slot (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (bs : List w8) (hok : headOk fs) (hu : grpcUnaryOf Svc fs) (hbs : bs.length < 2 ^ 32) :
    protoPrefix (grpcCliP (Gg := Gg) Svc) cn (clientPrefaceBytes ++ headFrame fs ++ dataFrame bs) ⊢
      grpcAttemptSlot (Gg := Gg) Svc cn fs bs := by
  unfold protoPrefix
  iintro (%h0 | ⟨%ext, %hext, #HP⟩)
  · exfalso
    have := congrArg List.length h0
    simp [dataFrame_length] at this
  unfold grpcCliP
  icases HP with (%hpre | ⟨%fs0, %rest, ⟨%hW, %hok0⟩, #Hr⟩)
  · exfalso
    have h1 := (hext.trans hpre).length_le
    simp only [List.length_append, dataFrame_length, clientPrefaceBytes] at h1
    simp at h1
    omega
  subst hW
  have hh : clientPrefaceBytes ++ headFrame fs <+: clientPrefaceBytes ++ headFrame fs0 ++ rest :=
    (List.prefix_append _ _).trans hext
  obtain rfl := head_prefix_inj hok hok0 hh
  have hd : dataFrame bs <+: rest := (List.prefix_append_right_inj _).1 hext
  unfold cliRest
  icases Hr with (%hnu | %hr | ⟨%bs0, %tl, ⟨%hrest, %hbs0⟩, #Hs⟩)
  · exfalso; exact hnu hu
  · exfalso
    have h1 := hd.length_le
    rcases hr with rfl | rfl <;> (simp [dataFrame_length, cancelFrame] at h1 <;> omega)
  · subst hrest
    obtain rfl := dataFrame_prefix_inj hbs hbs0 hd
    iexact Hs

/-- **The client reads a reply's data frame**: on its unary attempt's connection, a server's data
frame of bytes `bs'` answered its slot `.ok bs'`. -/
theorem srv_data_answered (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString))
    (bs bs' : List w8) (γ : SlotNames) (hok : headOk fs) (hu : grpcUnaryOf Svc fs) :
    ⊢ sentLb (Gg := Gg) cn false (clientPrefaceBytes ++ headFrame fs) -∗
      depSlotOf (Gg := Gg) cn γ ((fs, bs) : GrpcKey) -∗ srvFrameOk (Gg := Gg) Svc cn (.data bs') -∗
      slotDone (Gg := Gg) γ (GrpcOut.ok bs') := by
  iintro #Hlb #Hs Hf
  unfold srvFrameOk
  icases Hf with (#Hst | ⟨%γ', %k', #Hs', #Hd⟩)
  · iexfalso
    iapply streamConn_unary Svc cn fs hok hu $$ [Hlb Hst]
    iframe Hlb Hst
  · icases depSlotOf_agree cn γ γ' ((fs, bs) : GrpcKey) k' $$ Hs Hs' with %h
    obtain ⟨rfl, -⟩ := h
    iexact Hd

/-- **The client reads a trailer**: on its unary attempt's connection, a trailer whose decoded
`grpc-message` is a handler's description answered its slot `.err` with it. -/
theorem srv_trailer_answered (Svc : GrpcSvc GF) (cn : Nat) (fs fst : List (GoString × GoString))
    (bs v : List w8) (γ : SlotNames) (hok : headOk fs) (hu : grpcUnaryOf Svc fs)
    (hv : fieldLast fst go!"grpc-message" = some v) (hd : grpcMsgDecode v ∈ handlerDescs) :
    ⊢ sentLb (Gg := Gg) cn false (clientPrefaceBytes ++ headFrame fs) -∗
      depSlotOf (Gg := Gg) cn γ ((fs, bs) : GrpcKey) -∗
      srvFrameOk (Gg := Gg) Svc cn (.trailer fst) -∗
      slotDone (Gg := Gg) γ (GrpcOut.err (grpcMsgDecode v)) := by
  iintro #Hlb #Hs Hf
  unfold srvFrameOk
  icases Hf with (#Hst | Hw)
  · iexfalso
    iapply streamConn_unary Svc cn fs hok hu $$ [Hlb Hst]
    iframe Hlb Hst
  · ihave Hx := Hw $$ %v
    ihave Hy := Hx $$ []
    · ipureintro; exact ⟨hv, hd⟩
    icases Hy with ⟨%γ', %k', #Hs', #Hd⟩
    icases depSlotOf_agree cn γ γ' ((fs, bs) : GrpcKey) k' $$ Hs Hs' with %h
    obtain ⟨rfl, -⟩ := h
    iexact Hd

/-- An entry of the table `a` serves is a registration of its method. -/
theorem grpcSvcAt_of_addr (a name : GoString) (Svc : GrpcSvc GF) (e : GrpcEntry GF)
    (h : Svc name = some (.unary e)) :
    grpcAddrAt (Gg := Gg) a Svc ⊢ grpcSvcAt (Gg := Gg) a name e.Wq e.Wp e.spec := by
  iintro #Ha
  unfold grpcSvcAt
  iexists Svc, e.spec
  iframe Ha
  isplitl []
  · ipureintro; rw [h]
  · imodintro
    iintro %md %m %Φ %Ψe HS
    imodintro
    iexact HS

/-- A registration holds of any spec whose callers meet it after an update. -/
theorem grpcSvcAt_mono_upd (a name : GoString) (Wq Wp : ProtoWire)
    (Spec Spec' : GrpcMd → Wq.M → (Wp.M → IProp GF) → (GoString → IProp GF) → IProp GF) :
    ⊢ (□ ∀ md m Φ Ψe, Spec' md m Φ Ψe ==∗ Spec md m Φ Ψe) -∗
      grpcSvcAt (Gg := Gg) a name Wq Wp Spec -∗ grpcSvcAt (Gg := Gg) a name Wq Wp Spec' := by
  iintro #Hw #Ha
  unfold grpcSvcAt
  icases Ha with ⟨%Svc, %Spec₀, #Haddr, %hS, #H0⟩
  iexists Svc, Spec₀
  iframe Haddr
  isplitl []
  · ipureintro; exact hS
  · imodintro
    iintro %md %m %Φ %Ψe HS
    imod Hw $$ HS with HS
    iapply H0 $$ HS

/-- A stream entry of the table `a` serves, whose specification holds of every stream at its own
content, is a registration of its method. -/
theorem grpcStreamSvcAt_of_addr (a name : GoString) (Svc : GrpcSvc GF) (Wq Wp : ProtoWire)
    (up : Nat → Wq.M → IProp GF) (dn : GrpcMd → StreamNames → Nat → Wp.M → IProp GF)
    (spec : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF)
    (h : Svc name = some (.stream ⟨Wq, Wp, up, dn, spec⟩)) :
    grpcAddrAt (Gg := Gg) a Svc ∗ (□ ∀ md γ, spec md γ (dn md γ)) ⊢
      grpcStreamSvcAt (Gg := Gg) a name Wq Wp up spec := by
  iintro ⟨#Ha, #Hs⟩
  unfold grpcStreamSvcAt
  iexists Svc, up, dn, spec
  iframe Ha Hs
  isplitl []
  · ipureintro; exact h
  isplitl []
  · imodintro
    iintro %i %m HU
    imodintro
    iexact HU
  · imodintro
    iintro %md %γ %Dn HS
    iexact HS

/-- A stream registration holds of any content whose clients meet it after an update, and of any
weaker specification. -/
theorem grpcStreamSvcAt_mono (a name : GoString) (Wq Wp : ProtoWire)
    (Up Up' : Nat → Wq.M → IProp GF)
    (Spec Spec' : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF) :
    ⊢ (□ ∀ i m, Up' i m ==∗ Up i m) -∗ (□ ∀ md γ Dn, Spec md γ Dn -∗ Spec' md γ Dn) -∗
      grpcStreamSvcAt (Gg := Gg) a name Wq Wp Up Spec -∗
      grpcStreamSvcAt (Gg := Gg) a name Wq Wp Up' Spec' := by
  iintro #Hu #Hw #Ha
  unfold grpcStreamSvcAt
  icases Ha with ⟨%Svc, %up₀, %dn₀, %spec₀, #Haddr, %hS, #Hs, #Hu0, #Hw0⟩
  iexists Svc, up₀, dn₀, spec₀
  iframe Haddr Hs
  isplitl []
  · ipureintro; exact hS
  isplitl []
  · imodintro
    iintro %i %m HU
    imod Hu $$ HU with HU
    iapply Hu0 $$ HU
  · imodintro
    iintro %md %γ %Dn HS
    iapply Hw $$ [HS]
    iapply Hw0 $$ HS

end laws

end EtcdGrove
end Perennial
