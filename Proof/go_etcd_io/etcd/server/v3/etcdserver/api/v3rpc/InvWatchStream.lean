/-
**The watch stream's server end** (the watch slice's unit W-S, 2026-10-14): the interface of a
gRPC bidirectional stream as the server's handler sees it, in the shape of `notes/grpc-stream-spec.md`
(§2), now grpc's generic one (`google_golang_org/grpc/InvGrpcStream.lean`, unit W-W, which
derives it from grpc's raw `ServerStream`, `srvStreamIs_of_raw`), the `Watch`
service's message models, and its stream specification. Lean-first (no Rocq counterpart); the
design is in `notes/decisions.md`, "The watch stream's server end: indexed queues, the delivery
accounted by position".

**The stream** (`srvStreamIs st γ Req Rep Up Dn ci cd`, persistent): the interface value `st`
(the generated `Watch_WatchServer`, grpc's `BidiStreamingServer[WatchRequest, WatchResponse]`),
whose `Recv`, `Send` and `Context` meet the triples of the note's §2 over two indexed queues: up
(the client's requests, `γ.up`, a mono list the client appends to; the receiver's token
`srvRecvTok γ L`, `L` the requests received so far, a prefix of the up queue: `upAt γ i m`, the
`i`th request the client sent is `m`) and down (the server's responses, `γ.down`, the sender's
token `srvSendTok γ L` holding half of its authority, its lower bounds `downLb γ L` persistent).
Each message sent down at position `j` carries the handler's content `Dn j m` (the client learns
it with the message); each request received at position `i` carries the client's `Up i m`.

**Two changes to the note's shape** (for its author; `notes/decisions.md`):
* `Recv` gives the decoded request **owned** (`StreamMsg.recv`, not a persistent `ProtoMsg.recv`):
  grpc's codec decodes each message into a fresh one the handler owns, and `watch.go`'s
  `recvLoop` writes the create request it received (`creq.Key = []byte{0}` for an empty key,
  `creq.RangeEnd = nil`/`[]byte{}`);
* the client's per-message content `Up i m` (the mirror of `Dn`): what the server learns of the
  `i`th request with it. The watch server's restrictions are stated through it (`upRestricted`:
  no create request with `prev_kv`, `fragment` or filters).

**The messages** (`pbWatchRequest`, `pbWatchResponse`): a request's model `WatchReqM` (the oneof:
a create request's fields `CreateReqM`, a cancel's watch id, a progress request, or `other`: an
empty oneof or a `nil` inner request, which the server ignores); a response's model `WatchRespM`
(every field the wire carries: the header `HdrM`, `WatchId`, `Created`, `Canceled`,
`CompactRevision`, `CancelReason`, `Fragment`, the events as mvcc's `EvM`) and, as ghost data
not on the wire, the mvcc response it carries (`src`: the watcher it is a delivery of). The
server's message (`Rep.send`) is read-only, as the unary responses'.

**The stream specification** (`watchDn`, `watchStreamSpec`): every response the server sends down
at position `j` is either a control response answering an earlier request (`ctrlOk`: a create
request's `Created` response, canceled with watch id `-1` or registered with its id; a cancel
request's `Canceled` response), or a response of the mvcc watch stream (`mvccOk`): its header's
revision is the response's, its events are a delivery of the mvcc watcher `r.w`
(`mvcc.watchRecvOk γ r.w rs`, the watcher's responses received from the stream's channel, `r`
the last), and, if it has events, the watcher's responses with events sent down before `j`
(read off the down queue's lower bound, `downLb`), then `r`, are exactly its responses with
events received (`rs`): no delivery is lost, reordered or duplicated on the way to the client.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchRecv
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.google_golang_org.grpc.InvGrpcStream
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Perennial.Proof.io

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3

export EtcdGrove (StreamMsg StreamNames srvRecvTok upAt upAt_persistent upClosed upClosed_persistent
  srvSendTok downLb downLb_persistent srvSendTok_lb streamErr streamErr_persistent eofIs
  eofIs_persistent srvStreamIs srvStreamIs_persistent streamAuxTok streamAuxIs
  streamAuxIs_persistent streamAux_set streamAuxIs_agree)

/-! ## The models (pure) -/

/-- **A `*pb.WatchCreateRequest`** as the server reads it. -/
structure CreateReqM where
  key : GoString
  rangeEnd : GoString
  startRev : w64
  progressNotify : Bool
  filters : List w32
  prevKv : Bool
  watchId : w64
  fragment : Bool
  /-- (K2e-6; ghost, not on the wire) the client's start revision was read from the store: the
  request comes with `mvcc.startRead` (`watchUp`), the watcher registered with it. -/
  sr : Bool := false

/-- **A `*pb.WatchRequest`** as the server reads it: its oneof. `other` is a request the server
ignores (an empty oneof, or a wrapper whose request is `nil`). -/
inductive WatchReqM where
  | create (c : CreateReqM)
  | cancel (id : w64)
  | progress
  | other

/-- **A `*pb.WatchResponse`** as the wire carries it, with the mvcc response it carries as ghost
data (`src`, `none` for a control response; not on the wire). -/
structure WatchRespM where
  hdr : HdrM
  watchId : w64
  created : Bool
  canceled : Bool
  compactRev : w64
  cancelReason : GoString
  fragment : Bool
  evs : List mvcc.EvM
  src : Option mvcc.RespM

instance CreateReqM.countable : Pos.Countable CreateReqM :=
  .ofInjective (fun c => Pos.Countable.encode (c.key, c.rangeEnd, c.startRev, c.progressNotify,
      c.filters, c.prevKv, c.watchId, c.fragment, c.sr))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- The oneof as a sum (for its countability). -/
def WatchReqM.enc : WatchReqM → CreateReqM ⊕ (w64 ⊕ Bool)
  | .create c => .inl c
  | .cancel id => .inr (.inl id)
  | .progress => .inr (.inr true)
  | .other => .inr (.inr false)

instance WatchReqM.countable : Pos.Countable WatchReqM :=
  .ofInjective (fun m => Pos.Countable.encode m.enc)
    (fun a b h => by
      have h' := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [WatchReqM.enc])

instance WatchRespM.countable : Pos.Countable WatchRespM :=
  .ofInjective (fun m => Pos.Countable.encode ((m.hdr.clusterId, m.hdr.memberId, m.hdr.revision,
      m.hdr.raftTerm, m.hdr.leaderId), m.watchId, m.created, m.canceled, m.compactRev,
      m.cancelReason, m.fragment, m.evs, m.src))
    (fun a b h => by
      have := Pos.encode_inj h
      rcases a with ⟨⟨_, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩
      rcases b with ⟨⟨_, _, _, _, _⟩, _, _, _, _, _, _, _, _⟩
      simp_all)

/-- **The restrictions of the watch server's proof** (`upRestricted`): a create request asks
neither for previous key-values (`prev_kv`: the send loop's `PrevKv` write and the store read
behind it are not modeled; not a bug: `newWatcherBatch` copies each event per watcher), nor for
fragments, nor filters; and no request is `other` (an empty oneof or a `nil` inner request: the translation
of `recvLoop`'s `default:` branch reads the type switch's variable `uv`, which Goose leaves
unbound there, a translator bug, `notes/STATUS.md`; etcd's client never sends one). And (the
watch slice's unit W-C) a create request asks for no watch id of its own (`WatchId = 0`,
`AutoWatchID`): this excludes clients choosing their own watch ids, which etcd's client never
does (`watch.go`'s `toPB` leaves it `0`); it is what makes the server's ids unique per stream,
the premise `srvEventIdsAssigned` of the client's watch true of the server
(`client/v3/InvWatch.lean`). -/
def watchReqOk : WatchReqM → Prop
  | .create c => c.prevKv = false ∧ c.fragment = false ∧ c.filters = [] ∧ c.watchId = W64 0
  | .other => False
  | _ => True

/-- **What a control response answers** (pure): a create request's `Created` response (no events,
no compaction, not fragmented, no ghost source): canceled with the watch id `-1` (a negative
start revision, the compacted response; the permission check failed; or mvcc's `Watch` refused:
an empty range, a duplicate id), or registered, not canceled, with the requested id if it was
not `0` (`AutoWatchID`), at a start revision at least `0`; a cancel request's `Canceled` response
with its id. -/
def ctrlAnswers (req : WatchReqM) (m : WatchRespM) : Prop :=
  m.src = none ∧ m.evs = [] ∧ m.compactRev = W64 0 ∧ m.fragment = false ∧
  match req with
  | .create c => m.created = true ∧
      ((m.canceled = true ∧ m.watchId = W64 (-1)) ∨
       (m.canceled = false ∧ 0 ≤ sint.Z c.startRev ∧
         (c.watchId ≠ W64 0 → m.watchId = c.watchId)))
  | .cancel id => m.created = false ∧ m.canceled = true ∧ m.watchId = id
  | _ => False

/-- **The range `r` a create request `c` registers** with the watch id `id` (`recvLoop`'s
normalization): an empty key is `"\x00"` (the smallest key); an empty range end is a single key
(`RangeEnd = nil`); the range end `"\x00"` is "from the key on" (`RangeEnd = []byte{}`, the end
`some []`), or, in the model only, a single key: Perennial's `wp_slice_literal` does not say that
the empty literal `[]byte{}` is not `nil` (in Go it is not; `notes/STATUS.md`, "W-M"); any other
range end is kept. -/
def createRangeOk (c : CreateReqM) (id : w64) (r : mvcc.WatchRange) : Prop :=
  r.key = (if c.key = [] then [W8 0] else c.key) ∧ r.startRev = c.startRev ∧ r.id = id ∧
  (if c.rangeEnd = [] then r.end? = none
   else if c.rangeEnd = [W8 0] then r.end? = some [] ∨ r.end? = none
   else r.end? = some c.rangeEnd)

/-- **The response the send loop makes of the mvcc response `r`** with the header `h` (its
revision `r.rev`): `r`'s watch id and events, not created, not canceled (mvcc's responses never
carry a compaction: `respIs`), no reason, not fragmented, `r` as its ghost source. -/
def mvccResp (r : mvcc.RespM) (h : HdrM) : WatchRespM :=
  { hdr := h, watchId := r.id, created := false, canceled := false, compactRev := W64 0,
    cancelReason := [], fragment := false, evs := r.evs, src := some r }

/-- **The watch id `X` is live after the responses `L`** (pure; the watch slice's unit W-C): the
last control response for `X` among `L` is a created, not canceled, one. The send loop sends an
mvcc response of an id other than `-1` only while it is (`ids`), and a client that saw `X`
canceled is sent nothing more for it. -/
def idLive (L : List WatchRespM) (X : w64) : Prop :=
  ((L.filter (fun m => decide (m.src = none ∧ m.watchId = X))).getLast?.map
    (fun m => m.created && !m.canceled)) = some true

/-- **What was forwarded before a response** `r` (pure; K2e-7d): every response queued on the
channel before `r` (`pre`) of an id live after the responses `L` sent before `r`, `r`'s own or any
for `r` of id `-1`, was sent (the send loop sends a live id's responses at once, and flushes an
id's buffered ones right after its created response). -/
def fwdCov (L : List WatchRespM) (pre : List mvcc.RespM) (r : mvcc.RespM) : Prop :=
  ∀ X, X ≠ W64 (-1) → idLive L X → (r.id = X ∨ r.id = W64 (-1)) →
    ∀ x ∈ pre, x.id = X → ∃ m' ∈ L, m'.src = some x

/-- **The responses sent before a response were queued before it** (pure; K2e-7d): those sent
while `r`'s id was live (any, for `r` of id `-1`, which is sent at once) are before `r` on the
channel (`idx`). -/
def fwdIdx (L : List WatchRespM) (r : mvcc.RespM) : Prop :=
  ∀ (i : Nat) (m' : WatchRespM) (y : mvcc.RespM), L[i]? = some m' → m'.src = some y →
    (r.id = W64 (-1) ∨ idLive (L.take i) r.id) → y.idx < r.idx

/-- The mvcc responses with events of the watcher `w` among the responses `L` sent down. -/
def sentEvsOf (L : List WatchRespM) (w : Loc) : List mvcc.RespM :=
  (L.filterMap WatchRespM.src).filter fun x => decide (x.w = w ∧ x.evs ≠ [])

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The stream (moved to `google_golang_org/grpc/InvGrpcStream.lean`, unit W-W)

The generic stream vocabulary is grpc's (`EtcdGrove.StreamMsg`, `StreamNames`, the tokens, the
position facts, `streamErr`, `eofIs`, `srvStreamIs`); exported here under the names the watch
service's proofs use (`v3rpc.srvStreamIs`, ...). -/

/-! ## The run's own ghost names (the watch slice's unit W-C) -/

/-- **The answer to the request at up position `i`** (exclusive): the receive loop mints one per
request received and hands it with the control response answering it, so a request is answered
at most once (`ansTok_excl`). -/
def ansTok (γa : GName) (i : Nat) : IProp GF := ghostMapElem γa i (DFrac.own 1) ()

/-- Two answers to one request are impossible. -/
theorem ansTok_excl (γa : GName) (i : Nat) : ansTok (GF := GF) γa i ∗ ansTok γa i ⊢ False := by
  unfold ansTok
  iintro ⟨H1, H2⟩
  ihave %H := ghostMapElem_valid_2 i γa (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2
  exfalso
  exact absurd (DFrac.valid_op_own H.1) (by simp)

/-- **The answers not yet minted**: the requests at up positions `n` and above have no answer
token yet (the receive loop's; `ansPool_mint` mints the next). -/
def ansPool (γa : GName) (n : Nat) : IProp GF :=
  iprop(∃ M : GMap Nat Unit, ghostMapAuth γa 1 M ∗ ⌜∀ k, (M !! k).isSome → k < n⌝)

theorem ansPool_alloc : ⊢ |==> ∃ γa : GName, ansPool (GF := GF) γa 0 := by
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γa, H⟩
  imodintro
  iexists γa
  unfold ansPool
  iexists ∅
  iframe H
  ipureintro
  intro k hk
  simp [GMap.lookup_empty] at hk

/-- The answer token of the request at position `n`. -/
theorem ansPool_mint (γa : GName) (n : Nat) :
    ansPool (GF := GF) γa n ⊢ |==> (ansPool γa (n + 1) ∗ ansTok γa n) := by
  unfold ansPool ansTok
  iintro ⟨%M, Ha, %Hb⟩
  have hfresh : M.lookup n = none := by
    cases hc : M.lookup n with
    | none => rfl
    | some _ =>
      have := Hb n (by show (M.lookup n).isSome; rw [hc]; rfl); omega
  imod ghost_map_insert n () hfresh $$ Ha with ⟨Ha, He⟩
  imodintro
  iframe He
  iexists _
  iframe Ha
  ipureintro
  intro k hk
  by_cases hkn : n = k
  · omega
  · have hk' : (M !! k).isSome := by
      have := hk
      rw [show (M.insert n ()) !! k = (<[n := ()]> M) !! k from rfl,
        GMap.lookup_insert_eq_iff] at this
      simpa [hkn] using this
    have := Hb k hk'; omega

/-- The ghost names a watch run publishes in its stream's auxiliary name (`streamAuxIs`): its
mvcc watch stream's (`γo`) and its answers' (`γa`). -/
def auxOf (γo : mvcc.WsStreamNames) (γa : GName) : List GName :=
  [γo.tok, γo.ids, γo.fresh, γo.prog, γo.sentl, γo.rsn, γo.regi, γa]

theorem auxOf_inj {γo γo' : mvcc.WsStreamNames} {γa γa' : GName}
    (h : auxOf γo γa = auxOf γo' γa') : γo = γo' ∧ γa = γa' := by
  unfold auxOf at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h5, h6, h7, h8, h4⟩ := h
  cases γo; cases γo'
  simp_all

/-! ## The watch service's messages -/

/-- **A create request's fields the server owns** at `cr` (`m`): `Key` and `RangeEnd` owned (the
receive loop rewrites them), their contents and the other fields read-only; the key shorter than
`2 ^ 63 - 1` bytes (a decoded message's field: the permission checks' bound, unit A2). -/
def createReqOwn (cr : Loc) (c : CreateReqM) : IProp GF :=
  iprop(⌜cr ≠ null ∧ c.key.length < 2 ^ 63 - 1⌝ ∗ ∃ ks es fs : GoSlice,
    structFieldRef etcdserverpb.WatchCreateRequest go!"Key" cr ↦ ks ∗ ks ↦*□ c.key ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" cr ↦ es ∗ es ↦*□ c.rangeEnd ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"StartRevision" cr ↦□ c.startRev ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"ProgressNotify" cr ↦□ c.progressNotify ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"Filters" cr ↦□ fs ∗ fs ↦*□ c.filters ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"PrevKv" cr ↦□ c.prevKv ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"WatchId" cr ↦□ c.watchId ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"Fragment" cr ↦□ c.fragment)

/-- The oneof `u` is a create request's wrapper holding `p` (read-only). -/
def oneofCreate (u : GoInterface) (p : Loc) : IProp GF :=
  iprop(∃ w : Loc,
    ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_CreateRequest.ty) #w⌝ ∗
    structFieldRef etcdserverpb.WatchRequest_CreateRequest go!"CreateRequest" w ↦□ p)

/-- The oneof `u` is a cancel request's wrapper holding `p` (read-only). -/
def oneofCancel (u : GoInterface) (p : Loc) : IProp GF :=
  iprop(∃ w : Loc,
    ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_CancelRequest.ty) #w⌝ ∗
    structFieldRef etcdserverpb.WatchRequest_CancelRequest go!"CancelRequest" w ↦□ p)

/-- The oneof `u` is a progress request's wrapper holding `p` (read-only). -/
def oneofProgress (u : GoInterface) (p : Loc) : IProp GF :=
  iprop(∃ w : Loc,
    ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_ProgressRequest.ty) #w⌝ ∗
    structFieldRef etcdserverpb.WatchRequest_ProgressRequest go!"ProgressRequest" w ↦□ p)

/-- **A decoded `*pb.WatchRequest`** at `l` holding `m`, owned by the server: its oneof
(`RequestUnion`, read-only) and, for a create request, the request's fields (`createReqOwn`). -/
def watchReqRecv (l : Loc) (m : WatchReqM) : IProp GF :=
  iprop(∃ u : GoInterface, structFieldRef etcdserverpb.WatchRequest go!"RequestUnion" l ↦□ u ∗
    match m with
    | .create c => ∃ cr : Loc,
        oneofCreate u cr ∗ createReqOwn cr c
    | .cancel id => ∃ cr : Loc, ⌜cr ≠ null⌝ ∗
        oneofCancel u cr ∗
        structFieldRef etcdserverpb.WatchCancelRequest go!"WatchId" cr ↦□ id
    | .progress => ∃ cr : Loc, ⌜cr ≠ null⌝ ∗
        oneofProgress u cr
    | .other => ⌜u = GoInterface.nil⌝ ∨ oneofCreate u null ∨ oneofCancel u null ∨
        oneofProgress u null)

/-- **A `*pb.WatchResponse`** at `l` holding `m` (read-only): its header (`hdrFull`, the five
fields), the flags, the reason, and its events, each an mvcc event (`mvcc.evIs`). -/
def watchRespMsg (l : Loc) (m : WatchRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.WatchResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.WatchResponse go!"WatchId" l ↦□ m.watchId ∗
    structFieldRef etcdserverpb.WatchResponse go!"Created" l ↦□ m.created ∗
    structFieldRef etcdserverpb.WatchResponse go!"Canceled" l ↦□ m.canceled ∗
    structFieldRef etcdserverpb.WatchResponse go!"CompactRevision" l ↦□ m.compactRev ∗
    structFieldRef etcdserverpb.WatchResponse go!"CancelReason" l ↦□ m.cancelReason ∗
    structFieldRef etcdserverpb.WatchResponse go!"Fragment" l ↦□ m.fragment ∗
    structFieldRef etcdserverpb.WatchResponse go!"Events" l ↦□ sl ∗ sl ↦*□ ps ∗
    ⌜ps.length = m.evs.length⌝ ∗ [∗list] x ∈ ps.zip m.evs, mvcc.evIs x.1 x.2)

instance watchRespMsg_persistent (l : Loc) (m : WatchRespM) :
    Persistent (watchRespMsg (GF := GF) l m) := by
  unfold watchRespMsg; infer_instance

/-- A response header `h` holding `m`, owned (the receiver's decoded copy). -/
def hdrOwn (h : Loc) (m : HdrM) : IProp GF :=
  iprop(⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"ClusterId" h ↦ m.clusterId ∗
    structFieldRef etcdserverpb.ResponseHeader go!"MemberId" h ↦ m.memberId ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.revision ∗
    structFieldRef etcdserverpb.ResponseHeader go!"RaftTerm" h ↦ m.raftTerm ∗
    structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦ m.leaderId)

/-- **A decoded `*pb.WatchResponse`** at `l` holding `m`, owned by the receiver (the watch
slice's unit W-C: the client's `Recv()` decodes into a fresh message): its fields and its
header's owned, its events' slice and the events read-only (`mvcc.evIs`). -/
def watchRespRecv (l : Loc) (m : WatchRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.WatchResponse go!"Header" l ↦ h ∗ hdrOwn h m.hdr ∗
    structFieldRef etcdserverpb.WatchResponse go!"WatchId" l ↦ m.watchId ∗
    structFieldRef etcdserverpb.WatchResponse go!"Created" l ↦ m.created ∗
    structFieldRef etcdserverpb.WatchResponse go!"Canceled" l ↦ m.canceled ∗
    structFieldRef etcdserverpb.WatchResponse go!"CompactRevision" l ↦ m.compactRev ∗
    structFieldRef etcdserverpb.WatchResponse go!"CancelReason" l ↦ m.cancelReason ∗
    structFieldRef etcdserverpb.WatchResponse go!"Fragment" l ↦ m.fragment ∗
    structFieldRef etcdserverpb.WatchResponse go!"Events" l ↦ sl ∗ sl ↦*□ ps ∗
    ⌜ps.length = m.evs.length⌝ ∗ [∗list] x ∈ ps.zip m.evs, mvcc.evIs x.1 x.2)

/-- **A create request's fields the client sends** at `cr` (`m`; read-only): the fields the
server reads (`createReqOwn`'s), their contents. -/
def createReqSend (cr : Loc) (c : CreateReqM) : IProp GF :=
  iprop(⌜cr ≠ null⌝ ∗ ∃ ks es fs : GoSlice,
    structFieldRef etcdserverpb.WatchCreateRequest go!"Key" cr ↦□ ks ∗ ks ↦*□ c.key ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" cr ↦□ es ∗ es ↦*□ c.rangeEnd ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"StartRevision" cr ↦□ c.startRev ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"ProgressNotify" cr ↦□ c.progressNotify ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"Filters" cr ↦□ fs ∗ fs ↦*□ c.filters ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"PrevKv" cr ↦□ c.prevKv ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"WatchId" cr ↦□ c.watchId ∗
    structFieldRef etcdserverpb.WatchCreateRequest go!"Fragment" cr ↦□ c.fragment)

instance createReqSend_persistent (cr : Loc) (c : CreateReqM) :
    Persistent (createReqSend (GF := GF) cr c) := by
  unfold createReqSend; infer_instance

/-- **A `*pb.WatchRequest` the client sends** at `l` holding `m` (read-only; unit W-W): its oneof
(`RequestUnion`) and the inner request's fields the server reads (as `watchReqRecv`, all
read-only). The codec's copy of it is one `watchReqRecv` holds at `m` (the wire model; the
decoded key's length bound, `createReqOwn`'s, is the codec's: a message is at most grpc's
receive limit, below `2 ^ 31` bytes). -/
def watchReqSend (l : Loc) (m : WatchReqM) : IProp GF :=
  iprop(∃ u : GoInterface, structFieldRef etcdserverpb.WatchRequest go!"RequestUnion" l ↦□ u ∗
    match m with
    | .create c => ∃ cr : Loc, oneofCreate u cr ∗ createReqSend cr c
    | .cancel id => ∃ cr : Loc, ⌜cr ≠ null⌝ ∗
        oneofCancel u cr ∗
        structFieldRef etcdserverpb.WatchCancelRequest go!"WatchId" cr ↦□ id
    | .progress => ∃ cr : Loc, ⌜cr ≠ null⌝ ∗
        oneofProgress u cr
    | .other => ⌜u = GoInterface.nil⌝ ∨ oneofCreate u null ∨ oneofCancel u null ∨
        oneofProgress u null)

/-- **The watch requests on the wire** (a trusted wire model, as the unary ones): the client's
message `watchReqSend`, the server's decoded copy `watchReqRecv` (owned), a message the receiver
owns at any content (`own`: a fresh `new(WatchRequest)` is one). -/
abbrev pbWatchRequest : StreamMsg GF where
  ty := etcdserverpb.WatchRequest.ty
  M := WatchReqM
  cnt := inferInstance
  send := watchReqSend
  recv := watchReqRecv
  own l := iprop(∃ v : etcdserverpb.WatchRequest, l ↦ v)

/-- **The watch responses on the wire** (a trusted wire model): the server's message
`watchRespMsg` (read-only), the client's decoded copy `watchRespRecv` (owned: a fresh message;
the watch slice's unit W-C), a message the receiver owns at any content (`own`: a fresh
`new(WatchResponse)` is one). -/
abbrev pbWatchResponse : StreamMsg GF where
  ty := etcdserverpb.WatchResponse.ty
  M := WatchRespM
  cnt := inferInstance
  send := watchRespMsg
  recv := watchRespRecv
  own l := iprop(∃ v : etcdserverpb.WatchResponse, l ↦ v)

/-! ## The stream specification -/

/-- **The client's restrictions** (persistent): every request it sends is restricted
(`watchReqOk`: no `prev_kv`, no fragments, no filters). -/
def upRestricted (Up : Nat → WatchReqM → IProp GF) : IProp GF :=
  iprop(□ ∀ (i : Nat) (m : WatchReqM), Up i m -∗ ⌜watchReqOk m⌝)

instance upRestricted_persistent (Up : Nat → WatchReqM → IProp GF) :
    Persistent (upRestricted Up) := by
  unfold upRestricted; infer_instance

/-- The `i`th watch request the client sent is `m` (persistent; `upAt` at `pbWatchRequest`). -/
def upAtW (γ : StreamNames) (i : Nat) (m : WatchReqM) : IProp GF := monoListIdxOwn γ.up i m

instance upAtW_persistent (γ : StreamNames) (i : Nat) (m : WatchReqM) :
    Persistent (upAtW (GF := GF) γ i m) := by
  unfold upAtW; infer_instance

/-- The watch responses `L` were sent down first (persistent; `downLb` at `pbWatchResponse`). -/
def downLbW (γ : StreamNames) (L : List WatchRespM) : IProp GF := monoListLbOwn γ.down L

instance downLbW_persistent (γ : StreamNames) (L : List WatchRespM) :
    Persistent (downLbW (GF := GF) γ L) := by
  unfold downLbW; infer_instance

/-- **The watcher a created response names** (the watch slice's units W-M and W-C): for a
create request `c` answered by a registered (not canceled) response `m`, the mvcc watcher `w`
the store registered for it (`mvcc.watcherIs`: its names, its fixed range `r`, the request's
key, range and start revision with the response's id, `createRangeOk c m.watchId r`, its
filters, its first revision `lo`: `c.startRev`, or for `0` the length of a committed log at the
registration; no filter: `fcs` holds none, as `watchReqOk` asks), the stream `γo` having assigned the id to it (`mvcc.idAssigned`, persistent) and
the id's token (`mvcc.idTok`, exclusive: a stream announces an id once), and (unit W-K) a
snapshot of the stream's channel's sent list taken after the registration (`streamSentLb`: the
point of the channel's order the response is sent after, so `sendLoop` sends every response of
id `-1` queued before it first), at least as long as the watcher's registration index
(`streamRegAt`, K1b); nothing for any other answer. -/
def ctrlWatcher (γ : mvcc.WsNames) (γo : mvcc.WsStreamNames) (req : WatchReqM) (m : WatchRespM) :
    IProp GF :=
  match req with
  | .create c => if m.canceled then iprop(True) else
      iprop(∃ (w : Loc) (r : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat),
        ⌜createRangeOk c m.watchId r⌝ ∗ mvcc.watcherIs γ w r fcs lo ∗
        fcs ↦*□ ([] : List GoFunc) ∗
        mvcc.idAssigned γo m.watchId w ∗ mvcc.idTok γo m.watchId ∗
        ∃ (l : List mvcc.RespM) (n : Nat), mvcc.streamSentLb γo l ∗ mvcc.streamRegAt γo w n ∗
          ⌜n ≤ l.length⌝)
  | _ => iprop(True)

/-- **A control response** `m`: it answers the request `req` the client sent at some position `i`
(`upAtW`), as `ctrlAnswers` says, with the request's answer token (`ansTok`: no request is
answered twice); a created response names the mvcc watcher registered for the request
(`ctrlWatcher`, over the store's names `γ` and the run's mvcc stream's `γo`); the run's names are
the stream's auxiliary name (`streamAuxIs`, the watch slice's unit W-C). -/
def ctrlOk (γs : StreamNames) (γ : mvcc.WsNames) (m : WatchRespM) : IProp GF :=
  iprop(∃ (i : Nat) (req : WatchReqM) (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (auxOf γo γa) ∗ upAtW γs i req ∗ ⌜ctrlAnswers req m⌝ ∗
    ctrlWatcher γ γo req m ∗ ansTok γa i)

/-- **The stream's progress fact** (unit W-M2): the client sent a progress request (at some
position of the up queue). The handler saves it as the mvcc stream's progress fact
(`NewWatchStream`'s `Q`), so a response of id `-1` (`progressAll`'s) carries it. -/
def progQ (γs : StreamNames) : IProp GF := iprop(∃ i : Nat, upAtW γs i .progress)

instance progQ_persistent (γs : StreamNames) : Persistent (progQ (GF := GF) γs) := by
  unfold progQ; infer_instance

/-- **The stream's cancellation reason** (unit W-K, K1b): the client sent a cancel request for
`id`. The handler saves it as the mvcc stream's (`NewWatchStream`'s `Ψ`); `recvLoop` has it when it
calls `Cancel id`, so a progress response of id `-1` covers every watcher of the stream registered
before it whose id the client did not ask to cancel. -/
def cancelQ (γs : StreamNames) (id : w64) : IProp GF := iprop(∃ i : Nat, upAtW γs i (.cancel id))

instance cancelQ_persistent (γs : StreamNames) (id : w64) :
    Persistent (cancelQ (GF := GF) γs id) := by
  unfold cancelQ; infer_instance

instance progQ_timeless (γs : StreamNames) : Timeless (progQ (GF := GF) γs) := by
  unfold progQ upAtW; infer_instance

/-- **What an mvcc response says of the stream** (persistent; unit W-M2, what the client's watch
needs, formerly its premises S2 and S3): if it has events, its id is one the stream (named in its
auxiliary name) assigned to its watcher; if its id is `-1`, it answers a progress request. -/
def mvccExtra (γs : StreamNames) (r : mvcc.RespM) : IProp GF :=
  iprop(□ (⌜r.evs ≠ []⌝ -∗ ∃ (γo : mvcc.WsStreamNames) (γa : GName),
      streamAuxIs γs (auxOf γo γa) ∗ mvcc.idAssigned γo r.id r.w) ∗
    □ (⌜r.id = W64 (-1)⌝ -∗ progQ γs))

instance mvccExtra_persistent (γs : StreamNames) (r : mvcc.RespM) :
    Persistent (mvccExtra (GF := GF) γs r) := by
  unfold mvccExtra; infer_instance

/-- **Where an mvcc response is on the stream's channel** (persistent; unit W-K, K1b): the
channel `γc` (its registration indices, cancellation reason and sent list named by the stream's
`γo`, the run's auxiliary name), the responses `pre` sent before it (`r.idx` its position, the
snapshot `pre ++ [r]`), what it covers (`respCov`) and, for id `-1`, the watchers registered
before it (`regsAt`); and the stream's cancellation reason, the client's cancel requests
(`cancelQ`, saved at `γo.rsn`); (K2e-7d) what was forwarded of `pre` before `r`, sent after
the responses `L` (`fwdCov`). -/
def mvccCov (γs : StreamNames) (γ : mvcc.WsNames) (L : List WatchRespM) (r : mvcc.RespM) :
    IProp GF :=
  iprop(∃ (γc : mvcc.WatchChanNames) (pre : List mvcc.RespM) (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (auxOf γo γa) ∗
    ⌜γo.regi = γc.regi ∧ γo.rsn = γc.rsn ∧ γo.sentl = γc.sentl ∧ r.idx = pre.length ∧
      fwdCov L pre r⌝ ∗
    mvcc.chanSentLb γc (pre ++ [r]) ∗ mvcc.respCov γ γc pre r ∗ mvcc.regsAt γc pre.length r ∗
    savedPredOwn γo.rsn DFrac.discard (cancelQ γs))

instance mvccCov_persistent (γs : StreamNames) (γ : mvcc.WsNames) (L : List WatchRespM)
    (r : mvcc.RespM) : Persistent (mvccCov (GF := GF) γs γ L r) := by
  unfold mvccCov; infer_instance

/-- **A response of the mvcc watch stream** sent at position `j` (persistent): the response of
the mvcc response `r` (`mvccResp`), whose header's revision is `r`'s, `r` the last of the
responses `rs` received for its watcher (`mvcc.watchRecvOk`: their events are the watcher's
deliveries), its id, unless `-1`, live after the responses before it (`idLive`; the watch
slice's unit W-C); if `r` has events, the watcher's responses with events sent before `j` (the down
queue's first `j` responses, `downLbW`), then `r`, are its responses with events received; and
what it says of the stream (`mvccExtra`, unit W-M2); where it is on the channel (`mvccCov`, K1b),
and no response before it came from it (each is sent once); (K2e-7d) the responses sent before it
while its id was live were queued before it (`fwdIdx`). -/
def mvccOk (γs : StreamNames) (γ : mvcc.WsNames) (j : Nat) (m : WatchRespM) : IProp GF :=
  iprop(∃ (r : mvcc.RespM) (rs : List mvcc.RespM) (L : List WatchRespM),
    ⌜m = mvccResp r m.hdr ∧ m.hdr.revision = r.rev ∧ L.length = j ∧ rs.getLast? = some r ∧
      (r.id ≠ W64 (-1) → idLive L r.id)⌝ ∗
    downLbW γs L ∗ mvcc.watchRecvOk γ r.w rs ∗
    ⌜r.evs ≠ [] → sentEvsOf L r.w ++ [r] = rs.filter (fun x => decide (x.evs ≠ []))⌝ ∗
    mvccExtra γs r ∗ mvccCov γs γ L r ∗ ⌜(∀ m' ∈ L, m'.src ≠ some r) ∧ fwdIdx L r⌝)

instance mvccOk_persistent (γs : StreamNames) (γ : mvcc.WsNames) (j : Nat) (m : WatchRespM) :
    Persistent (mvccOk (GF := GF) γs γ j m) := by
  unfold mvccOk; infer_instance

/-- **A created response sent at down position `j` follows the responses of id `-1` queued before
it** (persistent; the watch slice's unit W-K, `issues/etcd-watch-progress-before-created.md`): for
a registered (created, not canceled) control response `m`, its watcher `w` (`idAssigned`, as its
`ctrlWatcher` names it), the snapshot `l0` of the stream's channel's sent list its `ctrlWatcher`
carries (taken after the registration), a later snapshot `l` (`l0 <+: l`: the send loop drained
the channel before sending `m`), and the down list `L` of the `j` responses sent before it: every
response of id `-1` in `l` is among `L`'s mvcc responses. Nothing for any other control response.
(K1b) `w` was registered on the channel at an index `n` at most `l0`'s length (`streamRegAt`), so a
progress response sent after `m` was queued after `w`'s registration. -/
def createdAfter (γs : StreamNames) (j : Nat) (m : WatchRespM) : IProp GF :=
  if m.created && !m.canceled then
    iprop(∃ (γo : mvcc.WsStreamNames) (γa : GName) (w : Loc) (l0 l : List mvcc.RespM)
        (L : List WatchRespM) (n : Nat),
      streamAuxIs γs (auxOf γo γa) ∗ mvcc.idAssigned γo m.watchId w ∗
      mvcc.streamSentLb γo l0 ∗ mvcc.streamSentLb γo l ∗ downLbW γs L ∗
      mvcc.streamRegAt γo w n ∗ ⌜n ≤ l0.length⌝ ∗
      ⌜l0 <+: l ∧ L.length = j ∧ ∀ x ∈ l, x.id = W64 (-1) → ∃ m' ∈ L, m'.src = some x⌝)
  else iprop(True)

instance createdAfter_persistent (γs : StreamNames) (j : Nat) (m : WatchRespM) :
    Persistent (createdAfter (GF := GF) γs j m) := by
  unfold createdAfter; split <;> infer_instance

/-- **What the watch server says of its `j`th response** `m`: its header is the
server's (cluster `cid`, member `mid`), and it is a control response (`ctrlOk`; a created one
follows the progress responses queued before it, `createdAfter`, unit W-K) or one of the mvcc
watch stream's (`mvccOk`, over the store's names `γ`). -/
def watchDn (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64) (j : Nat) (m : WatchRespM) :
    IProp GF :=
  iprop(⌜m.hdr.clusterId = cid ∧ m.hdr.memberId = mid⌝ ∗
    ((⌜m.src = none⌝ ∗ ctrlOk γs γ m ∗ createdAfter γs j m) ∨ mvccOk γs γ j m))

open Iris.ProofMode in
/-- The created response's snapshot (`ctrlWatcher`'s), kept. -/
theorem ctrlWatcher_snap (γ : mvcc.WsNames) (γo : mvcc.WsStreamNames) (c : CreateReqM)
    (m : WatchRespM) (h : m.canceled = false) :
    ctrlWatcher (GF := GF) γ γo (.create c) m ⊢
      ctrlWatcher γ γo (.create c) m ∗
        ∃ (w : Loc) (l : List mvcc.RespM) (n : Nat), mvcc.idAssigned γo m.watchId w ∗
          mvcc.streamSentLb γo l ∗ mvcc.streamRegAt γo w n ∗ ⌜n ≤ l.length⌝ := by
  unfold ctrlWatcher
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  iintro ⟨%w, %rg, %fcs, %lo, %Hrg, #Hwi, #Hfcs, #Hia, Hit, %l, %n, #Hl, #Hn, %Hnl⟩
  isplitl [Hit]
  · iexists w, rg, fcs, lo
    iframe Hit
    iframe #
    ipureintro; exact ⟨Hrg, Hnl⟩
  iexists w, l, n; iframe #; ipureintro; exact Hnl


/-- **The watch stream's specification** (the note's §4; persistent): the handler's content of
every response sent down is exactly `watchDn`. The handler produces `Dn j m` from `watchDn`; the
client reads `watchDn` from the `Dn j m` it receives. -/
def watchStreamSpec (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64)
    (Dn : Nat → WatchRespM → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (m : WatchRespM), Dn j m ∗-∗ watchDn γs γ cid mid j m)

instance watchStreamSpec_persistent (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64)
    (Dn : Nat → WatchRespM → IProp GF) : Persistent (watchStreamSpec γs γ cid mid Dn) := by
  unfold watchStreamSpec; infer_instance

/-! ## The client's end of the watch stream (unit W-W) -/

/-- **The generated stub `wc`** (`*etcdserverpb.watchClient`) on the connection `conn`
(`NewWatchClient(conn)`'s `cc`: the `*grpc.ClientConn` as a `ClientConnInterface`). -/
def watchStubAt (wc conn : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.watchClient go!"cc" wc ↦□
    (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
      GoInterface))

instance watchStubAt_persistent (wc conn : Loc) : Persistent (watchStubAt (GF := GF) wc conn) := by
  unfold watchStubAt; infer_instance

/-- **The `Watch` service's descriptor** (persistent; a fact of `etcdserverpb`'s initialization,
as `watchVars`: `Watch_ServiceDesc` is the generated literal and nothing writes it): its
`Streams` slice holds at least one `StreamDesc` (the `Watch` stream's), read-only. What the stub
reads (`&Watch_ServiceDesc.Streams[0]`). -/
def watchDescOk : IProp GF :=
  iprop(∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams"
      (globalAddr etcdserverpb.Watch_ServiceDesc) ↦□ sl ∗ sl ↦*□ sds ∗ ⌜0 < sds.length⌝)

instance watchDescOk_persistent : Persistent (watchDescOk (GF := GF)) := by
  unfold watchDescOk; infer_instance

/-- **The client end of a watch stream** (persistent; what `watchClient.Watch` returns, the
`Watch_WatchClient` the client's `watch.go` uses): `cliBidiStreamIs` at the watch messages.
`Send(req)` of a request `watchReqSend req m` with the client's content `Up i m`;
`Recv()` returns a fresh response `watchRespMsg resp m` with the server's content `Dn j m`. -/
abbrev cliWatchStreamIs (cs : GoInterface) (γ : StreamNames) (Up : Nat → WatchReqM → IProp GF)
    (Dn : Nat → WatchRespM → IProp GF) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  cliBidiStreamIs cs γ pbWatchRequest pbWatchResponse Up Dn cd

end defs

end v3rpc
end EtcdGrove
end Perennial
