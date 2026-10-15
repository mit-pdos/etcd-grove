/-
**The watch stream's server end** (the watch slice's unit W-S, 2026-10-14): the interface of a
gRPC bidirectional stream as the server's handler sees it, in the shape of `notes/grpc-stream-spec.md`
(§2), stated locally (the generic gRPC specification's author will instantiate it), the `Watch`
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
      c.filters, c.prevKv, c.watchId, c.fragment))
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
unbound there, a translator bug, `notes/STATUS.md`; etcd's client never sends one). -/
def watchReqOk : WatchReqM → Prop
  | .create c => c.prevKv = false ∧ c.fragment = false ∧ c.filters = []
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

/-- **The response the send loop makes of the mvcc response `r`** with the header `h` (its
revision `r.rev`): `r`'s watch id and events, not created, not canceled (mvcc's responses never
carry a compaction: `respIs`), no reason, not fragmented, `r` as its ghost source. -/
def mvccResp (r : mvcc.RespM) (h : HdrM) : WatchRespM :=
  { hdr := h, watchId := r.id, created := false, canceled := false, compactRev := W64 0,
    cancelReason := [], fragment := false, evs := r.evs, src := some r }

/-- The mvcc responses with events of the watcher `w` among the responses `L` sent down. -/
def sentEvsOf (L : List WatchRespM) (w : Loc) : List mvcc.RespM :=
  (L.filterMap WatchRespM.src).filter fun x => decide (x.w = w ∧ x.evs ≠ [])

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Stream messages -/

/-- **A message type of a stream** (as grpc's `ProtoMsg`, with the decoded copy owned): its Go
type, the model of its content (countable: the queues are ghost lists of models), the sender's
message `send l m`, and `recv l m`, a decoded copy the receiver owns. -/
structure StreamMsg (GF : BundledGFunctors) where
  ty : go.GoType
  M : Type
  cnt : Pos.Countable M
  send : Loc → M → IProp GF
  recv : Loc → M → IProp GF

attribute [instance] StreamMsg.cnt

/-! ## The stream's ghost state -/

/-- The ghost names of one stream: the up queue (the requests the client sent, a mono list), the
server's received prefix of it, the down queue (the responses the server sent, a mono list) and
the up queue's end. -/
structure StreamNames where
  up : GName
  upRcv : GName
  down : GName
  upEnd : GName

/-- **The receiver's token** at `L`: the requests received so far, a prefix of the up queue. -/
def srvRecvTok {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) : IProp GF :=
  iprop(dghostVar γ.upRcv (DFrac.own (1 : Qp).half) L ∗ monoListLbOwn γ.up L)

/-- The `i`th request the client sent on the stream is `m` (persistent). -/
def upAt {Req : StreamMsg GF} (γ : StreamNames) (i : Nat) (m : Req.M) : IProp GF :=
  monoListIdxOwn γ.up i m

instance upAt_persistent {Req : StreamMsg GF} (γ : StreamNames) (i : Nat) (m : Req.M) :
    Persistent (upAt (GF := GF) γ i m) := by
  unfold upAt; infer_instance

/-- The client closed the up queue after the requests `L` (persistent). -/
def upClosed {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) : IProp GF :=
  dghostVar γ.upEnd DFrac.discard L

instance upClosed_persistent {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) :
    Persistent (upClosed (GF := GF) γ L) := by
  unfold upClosed; infer_instance

/-- **The sender's token** at `L`: the responses sent so far (half the down queue's authority;
the transport holds the other). -/
def srvSendTok {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) : IProp GF :=
  monoListAuthOwn γ.down (1 : Qp).half L

/-- The responses `L` were sent down, in order, first (persistent). -/
def downLb {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) : IProp GF :=
  monoListLbOwn γ.down L

instance downLb_persistent {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) :
    Persistent (downLb (GF := GF) γ L) := by
  unfold downLb; infer_instance

/-- The sender knows what it sent: its token's lower bound. -/
theorem srvSendTok_lb {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) :
    srvSendTok (GF := GF) (Rep := Rep) γ L ⊢ srvSendTok γ L ∗ downLb γ L := by
  unfold srvSendTok downLb
  iintro H
  ihave #Hlb := monoListLbOwn_get γ.down (1 : Qp).half L $$ H
  isplitl [H]
  · iexact H
  · iexact Hlb

/-! ## The stream's errors -/

/-- **An error of the stream** (`Recv`'s, `Send`'s; persistent): a typed error (the gRPC status
error or a context error grpc returns), in an error tree for every pointer target as `errors.Is`
needs it (`errors.errorIsTree`; `errors.TreeTyped` of pointer targets). -/
def streamErr (err : GoInterface) : IProp GF :=
  iprop(⌜context.isTypedErr err⌝ ∗
    □ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
      _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
      ⌜S err ∧ (ptrTarget target → _root_.Perennial.errors.TreeTyped S target)⌝)

instance streamErr_persistent (err : GoInterface) : Persistent (streamErr (GF := GF) err) := by
  unfold streamErr; infer_instance

/-- `err` is `io.EOF`'s value. -/
def eofIs (err : GoInterface) : IProp GF :=
  iprop(globalAddr _root_.Perennial.io.EOF ↦□ err)

instance eofIs_persistent (err : GoInterface) : Persistent (eofIs (GF := GF) err) := by
  unfold eofIs; infer_instance

/-! ## The server end -/

/-- **The server end of a stream** (persistent; the note's §2): the interface value `st`, whose
`Recv()` returns the next request (`Req.recv`, owned) with the client's content `Up i m` and
the receiver's token grown, or `io.EOF` once the client closed the up queue after the requests
received (`upClosed`), or another error; whose `Send(l)` of a message `Rep.send l m` with the
handler's content `Dn j m` for its position `j` grows the sender's token (or fails, the message
maybe delivered); and whose `Context()` returns the run's context `ci` (`isContext ci cd`,
grpc's run context `grpcRunCtx`). -/
def srvStreamIs (st : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ L : List Req.M,
      {{ srvRecvTok (Req := Req) γ L }}
        (App (Val #(methods si.ty go!"Recv" si.v)) (Val #()))
      {{ (req : Loc) (err : GoInterface), RET (PairV #req #err);
          (⌜err = GoInterface.nil⌝ ∗ ∃ m : Req.M, Req.recv req m ∗ Up L.length m ∗
            srvRecvTok (Req := Req) γ (L ++ [m])) ∨
          (eofIs err ∗ ⌜err ≠ GoInterface.nil⌝ ∗ srvRecvTok (Req := Req) γ L ∗
            upClosed (Req := Req) γ L) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ streamErr err ∗ srvRecvTok (Req := Req) γ L) }}) ∗
    □ (∀ (L : List Rep.M) (l : Loc) (m : Rep.M),
      {{ srvSendTok (Rep := Rep) γ L ∗ Rep.send l m ∗ Dn L.length m }}
        (App (Val #(methods si.ty go!"Send" si.v)) (Val #l))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ srvSendTok (Rep := Rep) γ (L ++ [m])) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ streamErr err ∗ srvSendTok (Rep := Rep) γ L) }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
      {{ RET #(GoInterface.ok ci); True }}) ∗
    context.isContext ci cd ∗ grpcRunCtx ci)

instance srvStreamIs_persistent (st : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
    Persistent (srvStreamIs st γ Req Rep Up Dn ci cd) := by
  unfold srvStreamIs; infer_instance

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

/-- **The watch requests on the wire** (a trusted wire model, as the unary ones). -/
abbrev pbWatchRequest : StreamMsg GF where
  ty := etcdserverpb.WatchRequest.ty
  M := WatchReqM
  cnt := inferInstance
  send _ _ := iprop(True)
  recv := watchReqRecv

/-- **The watch responses on the wire** (a trusted wire model). -/
abbrev pbWatchResponse : StreamMsg GF where
  ty := etcdserverpb.WatchResponse.ty
  M := WatchRespM
  cnt := inferInstance
  send := watchRespMsg
  recv := watchRespMsg

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

/-- **A control response** `m` (persistent): it answers the request `req` the client sent at
some position `i` (`upAtW`), as `ctrlAnswers` says. -/
def ctrlOk (γ : StreamNames) (m : WatchRespM) : IProp GF :=
  iprop(∃ (i : Nat) (req : WatchReqM), upAtW γ i req ∗ ⌜ctrlAnswers req m⌝)

instance ctrlOk_persistent (γ : StreamNames) (m : WatchRespM) :
    Persistent (ctrlOk (GF := GF) γ m) := by
  unfold ctrlOk; infer_instance

/-- **A response of the mvcc watch stream** sent at position `j` (persistent): the response of
the mvcc response `r` (`mvccResp`), whose header's revision is `r`'s, `r` the last of the
responses `rs` received for its watcher (`mvcc.watchRecvOk`: their events are the watcher's
deliveries); if `r` has events, the watcher's responses with events sent before `j` (the down
queue's first `j` responses, `downLbW`), then `r`, are its responses with events received. -/
def mvccOk (γs : StreamNames) (γ : mvcc.WsNames) (j : Nat) (m : WatchRespM) : IProp GF :=
  iprop(∃ (r : mvcc.RespM) (rs : List mvcc.RespM) (L : List WatchRespM),
    ⌜m = mvccResp r m.hdr ∧ m.hdr.revision = r.rev ∧ L.length = j ∧ rs.getLast? = some r⌝ ∗
    downLbW γs L ∗ mvcc.watchRecvOk γ r.w rs ∗
    ⌜r.evs ≠ [] → sentEvsOf L r.w ++ [r] = rs.filter (fun x => decide (x.evs ≠ []))⌝)

instance mvccOk_persistent (γs : StreamNames) (γ : mvcc.WsNames) (j : Nat) (m : WatchRespM) :
    Persistent (mvccOk (GF := GF) γs γ j m) := by
  unfold mvccOk; infer_instance

/-- **What the watch server says of its `j`th response** `m` (persistent): its header is the
server's (cluster `cid`, member `mid`), and it is a control response (`ctrlOk`) or one of the
mvcc watch stream's (`mvccOk`, over the store's names `γ`). -/
def watchDn (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64) (j : Nat) (m : WatchRespM) :
    IProp GF :=
  iprop(⌜m.hdr.clusterId = cid ∧ m.hdr.memberId = mid⌝ ∗
    ((⌜m.src = none⌝ ∗ ctrlOk γs m) ∨ mvccOk γs γ j m))

instance watchDn_persistent (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64) (j : Nat)
    (m : WatchRespM) : Persistent (watchDn (GF := GF) γs γ cid mid j m) := by
  unfold watchDn; infer_instance

/-- **The watch stream's specification** (the note's §4; persistent): the handler's content of
every response sent down is exactly `watchDn`. The handler produces `Dn j m` from `watchDn`; the
client reads `watchDn` from the `Dn j m` it receives. -/
def watchStreamSpec (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64)
    (Dn : Nat → WatchRespM → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (m : WatchRespM), Dn j m ∗-∗ watchDn γs γ cid mid j m)

instance watchStreamSpec_persistent (γs : StreamNames) (γ : mvcc.WsNames) (cid mid : w64)
    (Dn : Nat → WatchRespM → IProp GF) : Persistent (watchStreamSpec γs γ cid mid Dn) := by
  unfold watchStreamSpec; infer_instance

end defs

end v3rpc
end EtcdGrove
end Perennial
