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
not on the wire, the mvcc response it carries (`src`: its index in the send loop's received list
and the API's `WResp`; the mvcc API migration, 2026-11-05, `notes/mvcc-api-clients/WatchSpecs.lean`
§2). The server's message (`Rep.send`) is read-only, as the unary responses'.

**The stream specification** (`watchDn`, `watchStreamSpec`, over mvcc's API): in `InvWatch.lean`,
next to the run it is stated over (the migration onto mvcc's API, 2026-11-05).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchMsgModel
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.google_golang_org.grpc.InvGrpcStream
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass
public import Proof.go_etcd_io.etcd.server.v3.auth.ModeTag
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
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

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **A `*pb.WatchRequest` the client sends** at `l` holding `m` (read-only; unit W-W): its oneof
(`RequestUnion`) and the inner request's fields the server reads (as `watchReqRecv`, all
read-only). The codec's copy of it is one `watchReqRecv` holds at `m` (the wire model; the
decoded key's length bound, `createReqOwn`'s, is the codec's: a message is at most grpc's
receive limit, below `2 ^ 31` bytes). The message is not `nil` (stage A of the per-type models,
2026-11-07: a registered model's `send null m ⊢ False`; every sender builds it fresh). An `other`
request has no oneof: Go encodes a wrapper whose inner message is `nil` as an empty inner message,
which decodes to a non-`nil` one, so a sent wrapper of `nil` is not an `other` on the wire (the
stage A Freeze review, W1). -/
def watchReqSend (l : Loc) (m : WatchReqM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗
    ∃ u : GoInterface, structFieldRef etcdserverpb.WatchRequest go!"RequestUnion" l ↦□ u ∗
    match m with
    | .create c => ∃ cr : Loc, oneofCreate u cr ∗ createReqSend cr c
    | .cancel id => ∃ cr : Loc, ⌜cr ≠ null⌝ ∗
        oneofCancel u cr ∗
        structFieldRef etcdserverpb.WatchCancelRequest go!"WatchId" cr ↦□ id
    | .progress => ∃ cr : Loc, ⌜cr ≠ null⌝ ∗
        oneofProgress u cr
    | .other => ⌜u = GoInterface.nil⌝)

/-- **A bound on a `*pb.WatchRequest`'s encoding** (`pbWatchRequest.wireLen`; 2026-10-30): a
create's key and range end, its filters (a packed enum, at most 10 bytes each), and the fixed part
(`wireSlack`); a cancel's or a progress request's fixed part. -/
def watchReqWireLen : WatchReqM → Nat
  | .create c => c.key.length + c.rangeEnd.length + 10 * c.filters.length + wireSlack
  | _ => wireSlack

/-- **The watch requests on the wire** (a trusted wire model, as the unary ones): the client's
message `watchReqSend`, the server's decoded copy `watchReqRecv` (owned), a message the receiver
owns at any content (`own`: a fresh `new(WatchRequest)` is one). -/
abbrev pbWatchRequest : StreamMsg GF where
  ty := etcdserverpb.WatchRequest.ty
  M := WatchReqM
  cnt := inferInstance
  send := watchReqSend
  wireLen := watchReqWireLen
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

/-- **A registered watcher's authorization** (the auth plan's A4, 2026-10-24; persistent;
strengthened in G2, 2026-10-30): in the mode some tag of the store's owner tag names
(`auth.modeTag tag M`: the server's, `watchSrvOk`), the class of the create request's read
(`apply.watchClassFrom`: the request's key, normalized, and its range end as the check saw it) for
the auth info `info` at auth states recorded at indices at least the create's bound `n` (the
client's `CreateReqM.bound`); with auth on, `info` bound to the stream's token `tok`
(`infoBoundT`: the empty user, a token issued to `info`'s user, or the server's TLS identity; gated
on the mode, the margin of `NewAuthStore`'s axiom, as in `isWatchPermitted.spec`); and the
request's shape (`auth.reqShape`: a non-empty key, a range that is a point, open-ended or proper --
mvcc's `Watch` refused the rest), so that in `on γa` every key the watcher covers was readable by
that principal at a recorded state no older than `n` (`WatchClass.lean`, `ctrlWatcher_authorized`). -/
def watchAuthed (tag : GName) (s : Loc) (tok : Option GoString) (n : Nat)
    (key rangeEnd : GoString) : IProp GF :=
  iprop(∃ (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
    auth.modeTag tag M ∗ apply.watchClassFrom M n info key rangeEnd ∗
    □ (⌜M.isOn = true⌝ → infoBoundT s M tok info) ∗
    ⌜auth.reqShape (apply.watchKey key) rangeEnd⌝)

instance watchAuthed_persistent (tag : GName) (s : Loc) (tok : Option GoString) (n : Nat)
    (key rangeEnd : GoString) :
    Persistent (watchAuthed (GF := GF) tag s tok n key rangeEnd) := by
  unfold watchAuthed; infer_instance

/-- **What a passed check gives** (G2's freeze, 2026-10-30): the mode `M` and the auth info `info`
the check classed, the mode's tag, the class at the bound `n`, with auth on `info` bound to the
token, and the request's shape (for a client of `watchAuthed`, e.g. `client.watchCheckOk_tok`, in
place of unfolding it). -/
theorem watchAuthed_elim (tag : GName) (s : Loc) (tok : Option GoString) (n : Nat)
    (key rangeEnd : GoString) :
    watchAuthed (GF := GF) tag s tok n key rangeEnd ⊢
      ∃ (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
        auth.modeTag tag M ∗ apply.watchClassFrom M n info key rangeEnd ∗
        □ (⌜M.isOn = true⌝ → infoBoundT s M tok info) ∗
        ⌜auth.reqShape (apply.watchKey key) rangeEnd⌝ := by
  unfold watchAuthed; iintro H; iexact H

/-- **The stream's cancellation reason** (unit W-K, K1b): the client sent a cancel request for
`id`. `recvLoop` has it when it calls `Cancel id`, and keeps it in the run's invariant (`wsInv`)
for the watcher it makes not live, so a progress response of id `-1` covers every watcher of the
stream registered before it whose id the client did not ask to cancel. -/
def cancelQ (γs : StreamNames) (id : w64) : IProp GF := iprop(∃ i : Nat, upAtW γs i (.cancel id))

instance cancelQ_persistent (γs : StreamNames) (id : w64) :
    Persistent (cancelQ (GF := GF) γs id) := by
  unfold cancelQ; infer_instance

instance cancelQ_timeless (γs : StreamNames) (id : w64) : Timeless (cancelQ (GF := GF) γs id) := by
  unfold cancelQ upAtW; infer_instance

/-! ## The client's end of the watch stream (unit W-W) -/

/-- **The generated stub `wc`** (`*etcdserverpb.watchClient`) on the connection `conn`
(`NewWatchClient(conn)`'s `cc`: the `*grpc.ClientConn` as a `ClientConnInterface`). -/
def watchStubAt (wc conn : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.watchClient go!"cc" wc ↦□
    (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
      GoInterface))

instance watchStubAt_persistent (wc conn : Loc) : Persistent (watchStubAt (GF := GF) wc conn) := by
  unfold watchStubAt; infer_instance

/-- **A watch stub's connection is determined** (G2's proofs, 2026-10-30): two `watchStubAt` facts of
one stub name the same connection (its `cc` field is read-only). -/
theorem watchStubAt_agree (wc conn conn' : Loc) :
    watchStubAt (GF := GF) wc conn ∗ watchStubAt wc conn' ⊢ ⌜conn = conn'⌝ := by
  iintro ⟨#Hs, #Hs'⟩
  unfold watchStubAt
  icombine Hs Hs' gives %Heq
  simp at Heq
  ipureintro
  exact go.intoVal_inj Heq

/-- **The `Watch` service's descriptor** (persistent; a fact of `etcdserverpb`'s initialization,
as `watchVars`: `Watch_ServiceDesc` is the generated literal and nothing writes it): its
`Streams` slice holds at least one `StreamDesc` (the `Watch` stream's), read-only, a client
stream (`ClientStreams`: what `NewStream`'s spec asks). What the stub reads
(`&Watch_ServiceDesc.Streams[0]`). -/
def watchDescOk : IProp GF :=
  iprop(∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams"
      (globalAddr etcdserverpb.Watch_ServiceDesc) ↦□ sl ∗ sl ↦*□ sds ∗
    ⌜0 < sds.length ∧ ∀ sd, sds[0]? = some sd → sd.ClientStreams' = true⌝)

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