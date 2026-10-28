/-
**gRPC streams: the generic specification of the stream wire** (the watch slice's unit W-W,
2026-10-15): both ends of a gRPC stream, the registration of a streaming method, and the
transport's claims, for any method and message types, in the style of the unary specification
(`InvGrpc.lean`, left untouched: its author deferred streams). Lean-first (no Rocq counterpart);
the design is `notes/grpc-stream-spec.md` (§2, §2a; §6 as built) and `notes/decisions.md`, "The
stream wire: both ends on grpc's raw streams, the generated wrappers proved, the registration as
the handler's premise".

**The model: two indexed FIFO queues per stream** (ghost mono lists, `StreamNames`): up (the
client's requests, `γ.up`; the client holds half its authority, `cliSendTok`, the transport the
other; the server's received prefix `srvRecvTok`, with its lower bound) and down (the server's
responses, `γ.down`; `srvSendTok` with the server, the client's received prefix `cliRecvTok`).
The `i`th request carries the client's content `Up i m` (what the server learns with it), the
`j`th response the server's content `Dn j m` (what the client learns with it). The ends of the
queues are persistent facts (`upClosed γ L`: the client closed the up queue after `L`;
`downClosed γ L`: the server's handler returned after sending `L`).

**The transport's claims** (the trust boundary; what the axioms below and the client's
`NewStream` assert, read them against grpc's `stream.go`/`server.go` and HTTP/2): while the
stream lives, each direction delivers the messages intact (the codec's copy of a message `send`
holds at `m` is one `recv` holds at `m`, the `StreamMsg` instance's wire model), in order, without
loss or duplication; a receive returns `io.EOF` exactly when the other side closed its direction
and everything it sent before was received; a send that fails may or may not have delivered its
message (the sender's token is at the old or the new list, which one being the transport's
knowledge, so the two ends never disagree); after an error nothing more is promised. The server's
run starts when the client's `NewStream` returns (the handler may be entered later; no message is
lost in between).

**The server end, raw** (`srvRawStreamIs st γ Req Rep Up Dn ci cd`, persistent): grpc's
`ServerStream` the runtime passes to a `StreamDesc.Handler`: `RecvMsg(m any)` into an owned
message (`Req.own`), `SendMsg(m any)`, `Context()` (the run's context `ci`, `isContext ci cd ∗
grpcRunCtx ci`). **The server end, wrapped** (`srvStreamIs`, unit W-S's interface, moved here):
the generated handler's `grpc.GenericServerStream[Req, Res]` (`Recv()` allocating the request,
`Send(*Res)`, `Context()`), derived from the raw end (`srvStreamIs_of_raw`).

**The client end, raw** (`cliStreamIs cs γ Req Rep Up Dn cd`): grpc's `ClientStream` that
`ClientConn.NewStream` returns: `SendMsg`, `RecvMsg`, `CloseSend`, `Context`. **Wrapped**
(`cliBidiStreamIs`): the generated stub's `grpc.GenericClientStream[Req, Res]` (`Send(*Req)`,
`Recv()` allocating the response, `CloseSend()`, `Context()`), derived (`cliBidiStreamIs_of_raw`).

**The registration** (`grpcStreamMethodOk mh srv ics S Up Spec`): the method handler `mh` with
the service `srv`, under the server's stream interceptor chain `ics` (`srvStreamChainWP`, as
grpc's `chainStreamServerInterceptors` composes it), run by grpc with the run slot `S`, a fresh
raw server end, both tokens at `[]`, and the stream specification `Spec γ Dn` (the handler's
premise: the serving layer fixes `Dn` at the stream's creation); the run returns nothing (the
slot stays with the run: `Watch` returns while its receive loop may be blocked). Since
2026-10-18 (the axiom audit: the model ran at most `n` streams in all, Go runs every one) the
runtime's `n` slots are a pool (`grpcSlotPool S`, an invariant) that a run is given
(`grpcStreamMethodOkR`) and may return its slot to from whichever thread frees it last
(`grpcSlotPool_return`): the model bounds the runs holding a slot at once, not all runs.
`grpcStreamMethodOk` (a run that keeps its slot) gives it (`grpcStreamMethodOk_R`). `Spec` is
satisfiable per stream (`streamSpecOk`): the transport picks `Dn` with `□ Spec γ Dn` and gives a
copy to each end. Served by `grpc.serveStream` from `grpcStreamServerAt addr ics sregs` (an
axiomatized token of the server's construction, beside the unary `grpcServerAt`), obtaining
`grpcServesStream`; `isGrpcStream addr name Up Spec` is what a client needs.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc
public import Spec.google_golang_org.grpc.GenericServerStream__Recv
public import Spec.google_golang_org.grpc.GenericServerStream__Send
public import Spec.google_golang_org.grpc.GenericServerStream__Context
public import Spec.google_golang_org.grpc.GenericClientStream__Send
public import Spec.google_golang_org.grpc.GenericClientStream__Recv
public import Spec.google_golang_org.grpc.GenericClientStream__CloseSend
public import Spec.google_golang_org.grpc.GenericClientStream__Context
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Perennial.Proof.io

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Stream messages -/

/-- **A message type of a stream** (as grpc's `ProtoMsg`, with the decoded copy owned): its Go
type, the model of its content (countable: the queues are ghost lists of models), the sender's
message `send l m` (given back by a send: the codec only reads it), `recv l m`, a decoded copy the
receiver owns, and `own l`, a message the receiver owns at any content, into which a receive
decodes (a fresh `new(T)`: `own` holds of it, a premise of the wrappers' lemmas). Each instance is
a trusted wire model of its Go type, as a `ProtoMsg`. -/
structure StreamMsg (GF : BundledGFunctors) where
  ty : go.GoType
  M : Type
  cnt : Pos.Countable M
  send : Loc → M → IProp GF
  recv : Loc → M → IProp GF
  own : Loc → IProp GF

attribute [instance] StreamMsg.cnt

/-! ## The stream's ghost state -/

/-- The ghost names of one stream: the up queue (the requests the client sent), the server's
received prefix of it, the down queue (the responses the server sent), the up queue's end, the
client's received prefix of the down queue, the down queue's end, and (the watch slice's unit
W-C) an auxiliary name the handler sets once (`streamAuxTok`, `streamAuxIs`): the names of the
handler's own per-stream ghost state, allocated after the stream specification is fixed, which
the stream specification can then mention. -/
structure StreamNames where
  up : GName
  upRcv : GName
  down : GName
  upEnd : GName
  downRcv : GName
  downEnd : GName
  aux : GName

/-- **The stream's auxiliary name, not yet set** (exclusive): the handler's run gets it with the
fresh stream (`grpcStreamMethodOk`) and sets it once (`streamAux_set`). -/
def streamAuxTok (γ : StreamNames) : IProp GF :=
  dghostVar γ.aux (DFrac.own 1) (none : Option (List GName))

/-- **The stream's auxiliary name is set to `v`** (persistent; agreement: `streamAuxIs_agree`):
the handler's own ghost names for this stream. -/
def streamAuxIs (γ : StreamNames) (v : List GName) : IProp GF :=
  dghostVar γ.aux DFrac.discard (some v)

instance streamAuxIs_persistent (γ : StreamNames) (v : List GName) :
    Persistent (streamAuxIs (GF := GF) γ v) := by
  unfold streamAuxIs; infer_instance

/-- The handler sets the auxiliary name, once. -/
theorem streamAux_set (γ : StreamNames) (v : List GName) :
    streamAuxTok (GF := GF) γ ⊢ |==> streamAuxIs γ v := by
  unfold streamAuxTok streamAuxIs
  iintro H
  imod dghostVar_update (some v) γ.aux none $$ H with H
  imod dghostVar_persist γ.aux 1 (some v) $$ H with H
  imodintro
  iexact H

/-- Two settings of the auxiliary name agree. -/
theorem streamAuxIs_agree (γ : StreamNames) (v v' : List GName) :
    streamAuxIs (GF := GF) γ v ∗ streamAuxIs γ v' ⊢ ⌜v = v'⌝ := by
  unfold streamAuxIs
  iintro ⟨H1, H2⟩
  ihave %H := dghostVar_agree γ.aux (some v) DFrac.discard (some v') DFrac.discard $$ H1 H2
  ipureintro
  cases H; rfl

/-- **The server's receiver token** at `L`: the requests received so far, a prefix of the up
queue. -/
def srvRecvTok {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) : IProp GF :=
  iprop(dghostVar γ.upRcv (DFrac.own (1 : Qp).half) L ∗ monoListLbOwn γ.up L)

/-- The `i`th request the client sent on the stream is `m` (persistent). -/
def upAt {Req : StreamMsg GF} (γ : StreamNames) (i : Nat) (m : Req.M) : IProp GF :=
  monoListIdxOwn γ.up i m

instance upAt_persistent {Req : StreamMsg GF} (γ : StreamNames) (i : Nat) (m : Req.M) :
    Persistent (upAt (GF := GF) γ i m) := by
  unfold upAt; infer_instance

/-- The requests `L` were sent up, in order, first (persistent). -/
def upLb {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) : IProp GF :=
  monoListLbOwn γ.up L

instance upLb_persistent {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) :
    Persistent (upLb (GF := GF) γ L) := by
  unfold upLb; infer_instance

/-- The client closed the up queue after the requests `L` (persistent). -/
def upClosed {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) : IProp GF :=
  dghostVar γ.upEnd DFrac.discard L

instance upClosed_persistent {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) :
    Persistent (upClosed (GF := GF) γ L) := by
  unfold upClosed; infer_instance

/-- **The server's sender token** at `L`: the responses sent so far (half the down queue's
authority; the transport holds the other). -/
def srvSendTok {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) : IProp GF :=
  monoListAuthOwn γ.down (1 : Qp).half L

/-- The responses `L` were sent down, in order, first (persistent). -/
def downLb {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) : IProp GF :=
  monoListLbOwn γ.down L

instance downLb_persistent {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) :
    Persistent (downLb (GF := GF) γ L) := by
  unfold downLb; infer_instance

/-- The server's handler returned after sending the responses `L`: the down queue is closed
(persistent). -/
def downClosed {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) : IProp GF :=
  dghostVar γ.downEnd DFrac.discard L

instance downClosed_persistent {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) :
    Persistent (downClosed (GF := GF) γ L) := by
  unfold downClosed; infer_instance

/-- **The client's sender token** at `L`: the requests sent so far (half the up queue's
authority; the transport holds the other). -/
def cliSendTok {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) : IProp GF :=
  monoListAuthOwn γ.up (1 : Qp).half L

/-- **The client's receiver token** at `L`: the responses received so far, a prefix of the down
queue. -/
def cliRecvTok {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) : IProp GF :=
  iprop(dghostVar γ.downRcv (DFrac.own (1 : Qp).half) L ∗ monoListLbOwn γ.down L)

/-- The server knows what it sent: its token's lower bound. -/
theorem srvSendTok_lb {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) :
    srvSendTok (GF := GF) (Rep := Rep) γ L ⊢ srvSendTok γ L ∗ downLb γ L := by
  unfold srvSendTok downLb
  iintro H
  ihave #Hlb := monoListLbOwn_get γ.down (1 : Qp).half L $$ H
  isplitl [H]
  · iexact H
  · iexact Hlb

/-- The client knows what it sent: its token's lower bound. -/
theorem cliSendTok_lb {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) :
    cliSendTok (GF := GF) (Req := Req) γ L ⊢ cliSendTok γ L ∗ upLb γ L := by
  unfold cliSendTok upLb
  iintro H
  ihave #Hlb := monoListLbOwn_get γ.up (1 : Qp).half L $$ H
  isplitl [H]
  · iexact H
  · iexact Hlb

/-- What a lower bound of the up queue says of a position. -/
theorem upLb_at {Req : StreamMsg GF} (γ : StreamNames) (L : List Req.M) (i : Nat) (m : Req.M)
    (h : L[i]? = some m) : upLb (GF := GF) γ L ⊢ upAt γ i m := by
  unfold upLb upAt
  iintro H
  iapply (monoListIdxOwn_get (GF := GF) i m h) $$ H

/-- The client knows what it received: its token's lower bound of the down queue. -/
theorem cliRecvTok_lb {Rep : StreamMsg GF} (γ : StreamNames) (L : List Rep.M) :
    cliRecvTok (GF := GF) (Rep := Rep) γ L ⊢ cliRecvTok γ L ∗ downLb γ L := by
  unfold cliRecvTok downLb
  iintro ⟨H1, #H2⟩
  iframe
  iframe #

/-! ## The stream's errors -/

/-- **An error of the stream** (`Recv`'s, `Send`'s; persistent): a typed error (the gRPC status
error or a context error grpc returns), in an error tree for every pointer target as `errors.Is`
needs it (`errors.errorIsTree`; `errors.TreeTyped` of a target that is `nil` or a pointer error,
the server's `ptrTarget`). -/
def streamErr (err : GoInterface) : IProp GF :=
  iprop(⌜context.isTypedErr err⌝ ∗
    □ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
      _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
      ⌜S err ∧ ((∀ tii, target = GoInterface.ok tii → _root_.Perennial.errors.IsPointerError tii) →
        _root_.Perennial.errors.TreeTyped S target)⌝)

instance streamErr_persistent (err : GoInterface) : Persistent (streamErr (GF := GF) err) := by
  unfold streamErr; infer_instance

/-- **An error of the client's end** (persistent): a non-nil stream error that is a client error
(`clientErr`: a leaf, not an `EtcdError`) grpc's `status` accepts (`statusErrOk`): a gRPC status
error, a context error, or `io.EOF` (a `SendMsg` on a stream the server ended), as the unary
attempt's errors (`grpcInvokerOk`). -/
def cliStreamErr (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
    streamErr err)

instance cliStreamErr_persistent (err : GoInterface) : Persistent (cliStreamErr (GF := GF) err) := by
  unfold cliStreamErr; infer_instance

/-- `err` is `io.EOF`'s value. -/
def eofIs (err : GoInterface) : IProp GF :=
  iprop(globalAddr _root_.Perennial.io.EOF ↦□ err)

instance eofIs_persistent (err : GoInterface) : Persistent (eofIs (GF := GF) err) := by
  unfold eofIs; infer_instance

namespace client

/-- **`io.EOF` is a client error grpc's `status` accepts** (a package fact of `io`, persistent): a
leaf error (`errors.New("EOF")`) whose `Error()` returns. (Moved here from the client's
`InvWatch.lean` on 2026-10-18, for the lessor's keep-alive loop.) -/
def eofOk : IProp GF :=
  iprop(□ ∀ err : GoInterface, eofIs err -∗ ⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗
    go_etcd_io.etcd.cache.v3.statusErrOk err)

instance eofOk_persistent : Persistent (eofOk (GF := GF)) := by
  unfold eofOk; infer_instance

end client

/-- A message `l` of the Go type `T` passed as `any` (grpc's `SendMsg(m any)`, `RecvMsg(m any)`). -/
abbrev msgAny (T : go.GoType) (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType T) #l

/-! ## The server end -/

/-- **The server end of a stream, raw** (persistent): grpc's `ServerStream` `st` the runtime
passes to a stream handler. `RecvMsg(&out)` into an owned message (`Req.own out`) decodes the next
request into it (`Req.recv out m`, owned) with the client's content `Up i m` for its position `i`
(the receiver's token grown), or returns `io.EOF` once the client closed the up queue after the
requests received (`upClosed`), or another error (`out` back owned); `SendMsg(&l)` of a message
`Rep.send l m` (given back) with the handler's content `Dn j m` for its position `j` grows the
sender's token, or fails, the message delivered or not (the token at the old or the new list);
`Context()` returns the run's context `ci` (`isContext ci cd`, `grpcRunCtx ci`). -/
def srvRawStreamIs (st : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜st = GoInterface.ok si⌝ ∗
    □ (∀ (L : List Req.M) (out : Loc),
      {{ srvRecvTok (Req := Req) γ L ∗ Req.own out }}
        (App (Val #(methods si.ty go!"RecvMsg" si.v)) (Val #(msgAny Req.ty out)))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ ∃ m : Req.M, Req.recv out m ∗ Up L.length m ∗
            srvRecvTok (Req := Req) γ (L ++ [m])) ∨
          (eofIs err ∗ ⌜err ≠ GoInterface.nil⌝ ∗ srvRecvTok (Req := Req) γ L ∗
            upClosed (Req := Req) γ L ∗ Req.own out) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ streamErr err ∗ srvRecvTok (Req := Req) γ L ∗
            Req.own out) }}) ∗
    □ (∀ (L : List Rep.M) (l : Loc) (m : Rep.M),
      {{ srvSendTok (Rep := Rep) γ L ∗ Rep.send l m ∗ Dn L.length m }}
        (App (Val #(methods si.ty go!"SendMsg" si.v)) (Val #(msgAny Rep.ty l)))
      {{ (err : GoInterface), RET #err; Rep.send l m ∗
          ((⌜err = GoInterface.nil⌝ ∗ srvSendTok (Rep := Rep) γ (L ++ [m])) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ streamErr err ∗ ∃ L' : List Rep.M,
            ⌜L' = L ∨ L' = L ++ [m]⌝ ∗ srvSendTok (Rep := Rep) γ L')) }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
      {{ RET #(GoInterface.ok ci); True }}) ∗
    context.isContext ci cd ∗ grpcRunCtx ci)

instance srvRawStreamIs_persistent (st : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
    Persistent (srvRawStreamIs st γ Req Rep Up Dn ci cd) := by
  unfold srvRawStreamIs; infer_instance

/-- **The server end of a stream, as the generated handler wraps it** (persistent; unit W-S's
interface, `notes/grpc-stream-spec.md` §2a): the interface value `st` (the generated
`Watch_WatchServer`, grpc's `BidiStreamingServer[Req, Res]` holding a
`*GenericServerStream[Req, Res]`), whose `Recv()` returns the next request (`Req.recv`, owned)
with the client's content `Up i m` and the receiver's token grown, or `io.EOF` once the client
closed the up queue after the requests received (`upClosed`), or another error; whose `Send(l)` of
a message `Rep.send l m` with the handler's content `Dn j m` for its position `j` grows the
sender's token (or fails, the message delivered or not: the token at the old or the new list);
and whose `Context()` returns the run's context `ci` (`isContext ci cd`, grpc's run context
`grpcRunCtx`). Derived from the raw end (`srvStreamIs_of_raw`). -/
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
          (⌜err ≠ GoInterface.nil⌝ ∗ streamErr err ∗ ∃ L' : List Rep.M,
            ⌜L' = L ∨ L' = L ++ [m]⌝ ∗ srvSendTok (Rep := Rep) γ L') }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
      {{ RET #(GoInterface.ok ci); True }}) ∗
    context.isContext ci cd ∗ grpcRunCtx ci)

instance srvStreamIs_persistent (st : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) :
    Persistent (srvStreamIs st γ Req Rep Up Dn ci cd) := by
  unfold srvStreamIs; infer_instance

/-! ## The client end -/

/-- **The client end of a stream, raw** (persistent): grpc's `ClientStream` `cs` that
`ClientConn.NewStream` returns. `SendMsg(&l)` of a request `Req.send l m` (given back) with the
client's content `Up i m` for its position `i` grows the sender's token, or fails, the request
delivered or not (the token at the old or the new list); `RecvMsg(&out)` into an owned message
(`Rep.own out`) decodes the next response into it (`Rep.recv out m`) with the server's content
`Dn j m` for its position `j`, or returns `io.EOF` once the server's handler returned after the
responses received (`downClosed`), or another error (`out` back owned); `CloseSend()` closes the
up queue after the requests sent (`upClosed`); `Context()` returns the stream's context, of the
descriptor `cd` (derived from the caller's: done when it is, or when the stream ends). -/
def cliStreamIs (cs : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cs = GoInterface.ok ci⌝ ∗
    □ (∀ (L : List Req.M) (l : Loc) (m : Req.M),
      {{ cliSendTok (Req := Req) γ L ∗ Req.send l m ∗ Up L.length m }}
        (App (Val #(methods ci.ty go!"SendMsg" ci.v)) (Val #(msgAny Req.ty l)))
      {{ (err : GoInterface), RET #err; Req.send l m ∗
          ((⌜err = GoInterface.nil⌝ ∗ cliSendTok (Req := Req) γ (L ++ [m])) ∨
          (cliStreamErr err ∗ ∃ L' : List Req.M,
            ⌜L' = L ∨ L' = L ++ [m]⌝ ∗ cliSendTok (Req := Req) γ L')) }}) ∗
    □ (∀ (L : List Rep.M) (out : Loc),
      {{ cliRecvTok (Rep := Rep) γ L ∗ Rep.own out }}
        (App (Val #(methods ci.ty go!"RecvMsg" ci.v)) (Val #(msgAny Rep.ty out)))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ ∃ m : Rep.M, Rep.recv out m ∗ Dn L.length m ∗
            cliRecvTok (Rep := Rep) γ (L ++ [m])) ∨
          (eofIs err ∗ ⌜err ≠ GoInterface.nil⌝ ∗ cliRecvTok (Rep := Rep) γ L ∗
            downClosed (Rep := Rep) γ L ∗ Rep.own out) ∨
          (cliStreamErr err ∗ cliRecvTok (Rep := Rep) γ L ∗ Rep.own out) }}) ∗
    □ (∀ L : List Req.M,
      {{ cliSendTok (Req := Req) γ L }}
        (App (Val #(methods ci.ty go!"CloseSend" ci.v)) (Val #()))
      {{ (err : GoInterface), RET #err; upClosed (Req := Req) γ L ∗
          (⌜err = GoInterface.nil⌝ ∨ cliStreamErr err) }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Context" ci.v)) (Val #()))
      {{ (cx : GoInterfaceOk), RET #(GoInterface.ok cx); context.isContext cx cd }}))

instance cliStreamIs_persistent (cs : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) :
    Persistent (cliStreamIs cs γ Req Rep Up Dn cd) := by
  unfold cliStreamIs; infer_instance

/-- **The client end of a bidirectional stream, as the generated stub wraps it** (persistent):
the interface value `cs` (grpc's `BidiStreamingClient[Req, Res]`, the generated
`Watch_WatchClient`, holding a `*GenericClientStream[Req, Res]`): `Send(l)` is `SendMsg`'s,
`Recv()` allocates the response and returns it (`Rep.recv resp m` for a fresh `resp`, with the
server's content) or `nil` and the error, `CloseSend()` and `Context()` the raw end's. Derived
from the raw end (`cliBidiStreamIs_of_raw`). -/
def cliBidiStreamIs (cs : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cs = GoInterface.ok ci⌝ ∗
    □ (∀ (L : List Req.M) (l : Loc) (m : Req.M),
      {{ cliSendTok (Req := Req) γ L ∗ Req.send l m ∗ Up L.length m }}
        (App (Val #(methods ci.ty go!"Send" ci.v)) (Val #l))
      {{ (err : GoInterface), RET #err; Req.send l m ∗
          ((⌜err = GoInterface.nil⌝ ∗ cliSendTok (Req := Req) γ (L ++ [m])) ∨
          (cliStreamErr err ∗ ∃ L' : List Req.M,
            ⌜L' = L ∨ L' = L ++ [m]⌝ ∗ cliSendTok (Req := Req) γ L')) }}) ∗
    □ (∀ L : List Rep.M,
      {{ cliRecvTok (Rep := Rep) γ L }}
        (App (Val #(methods ci.ty go!"Recv" ci.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          (⌜err = GoInterface.nil⌝ ∗ ∃ m : Rep.M, Rep.recv resp m ∗ Dn L.length m ∗
            cliRecvTok (Rep := Rep) γ (L ++ [m])) ∨
          (⌜resp = null⌝ ∗ eofIs err ∗ ⌜err ≠ GoInterface.nil⌝ ∗ cliRecvTok (Rep := Rep) γ L ∗
            downClosed (Rep := Rep) γ L) ∨
          (⌜resp = null⌝ ∗ cliStreamErr err ∗ cliRecvTok (Rep := Rep) γ L) }}) ∗
    □ (∀ L : List Req.M,
      {{ cliSendTok (Req := Req) γ L }}
        (App (Val #(methods ci.ty go!"CloseSend" ci.v)) (Val #()))
      {{ (err : GoInterface), RET #err; upClosed (Req := Req) γ L ∗
          (⌜err = GoInterface.nil⌝ ∨ cliStreamErr err) }}) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Context" ci.v)) (Val #()))
      {{ (cx : GoInterfaceOk), RET #(GoInterface.ok cx); context.isContext cx cd }}))

instance cliBidiStreamIs_persistent (cs : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) :
    Persistent (cliBidiStreamIs cs γ Req Rep Up Dn cd) := by
  unfold cliBidiStreamIs; infer_instance

/-! ## The generated wrappers over the raw ends -/

/-- **The server end the generated handler passes** (`&grpc.GenericServerStream[Req, Res]{ServerStream:
stream}`, as `BidiStreamingServer[Req, Res]`) meets the wrapped interface (`srvStreamIs`) when its
embedded stream (read-only) is a raw server end: `Recv` allocates the request (a fresh message the
receiver owns, `Req.own`) and receives into it, `Send` and `Context` are the raw end's
(`GenericServerStream`'s methods, axioms at the boundary). -/
theorem srvStreamIs_of_raw {Req Rep : StreamMsg GF} (V W : Type) [ZeroVal V]
    [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V Req.ty]
    (wp_Recv : grpc.GenericServerStream.Recv.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericServerStream.Send.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericServerStream.Context.spec (GF := GF) (hG := hG))
    (p : Loc) (st : GoInterface) (γ : StreamNames) (Up : Nat → Req.M → IProp GF)
    (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    structFieldRef (google_golang_org.grpc.GenericServerStream V W) go!"ServerStream" p ↦□ st ∗
      srvRawStreamIs st γ Req Rep Up Dn ci cd ∗ (□ ∀ l : Loc, l ↦ (zero_val V) -∗ Req.own l) ⊢
    srvStreamIs (interface.mkOk (go.GoType.PointerType
      (google_golang_org.grpc.GenericServerStream.ty Req.ty Rep.ty)) #p) γ Req Rep Up Dn ci cd := by
  iintro ⟨#Hf, #Hraw, #Hown⟩
  iunfold srvRawStreamIs at Hraw
  icases Hraw with ⟨%si, %Hst, #HRecv, #HSend, #HCtx, #Hctx, #Hrc⟩
  subst Hst
  unfold srvStreamIs
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %L %Φ !> Htok HΦ
    iapply (wp_Recv Req.ty Rep.ty V W p si Φ)
    isplitr
    · iexact Hf
    iintro %m Hm
    ihave Hm' := Hown $$ %m Hm
    iapply HRecv $$ %L %m [Htok Hm']
    · iframe
    iintro !> %err Hres
    iexists err
    isplitr
    · ipureintro; rfl
    icases Hres with (⟨%Herr, %mm, Hr, HUp, Htok⟩ | ⟨#Heof, %Hne, Htok, #Hcl, -⟩ |
      ⟨%Hne, #Hse, Htok, -⟩)
    · subst Herr
      simp only [↓reduceIte]
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists mm
      iframe
    · simp only [Hne, ↓reduceIte]
      iapply HΦ
      iright; ileft
      iframe
      iframe #
      ipureintro; exact Hne
    · simp only [Hne, ↓reduceIte]
      iapply HΦ
      iright; iright
      iframe
      iframe #
      ipureintro; exact Hne
  isplitr
  · iintro !> %L %l %m %Φ !> ⟨Htok, Hs, HDn⟩ HΦ
    iapply (wp_Send Req.ty Rep.ty V W p si l Φ)
    isplitr
    · iexact Hf
    iapply HSend $$ %L %l %m [Htok Hs HDn]
    · iframe
    iintro !> %err ⟨-, Hres⟩
    iapply HΦ
    iexact Hres
  isplitr
  · iintro !> %Φ !> - HΦ
    iapply (wp_Context Req.ty Rep.ty V W p si Φ)
    isplitr
    · iexact Hf
    iapply HCtx $$ []
    · itrivial
    iexact HΦ
  iframe #

/-- **The client end the generated stub returns** (`&grpc.GenericClientStream[Req, Res]{ClientStream:
stream}`, as `BidiStreamingClient[Req, Res]`) meets the wrapped interface (`cliBidiStreamIs`) when
its embedded stream (read-only) is a raw client end: `Send`, `CloseSend` and `Context` are the
raw end's, `Recv` allocates the response (a fresh message the receiver owns, `Rep.own`) and
receives into it (`GenericClientStream`'s methods, axioms at the boundary). -/
theorem cliBidiStreamIs_of_raw {Req Rep : StreamMsg GF} (V W : Type) [ZeroVal W]
    [TypedPointsto (GF := GF) W] [IntoValTyped (GF := GF) W Rep.ty]
    (wp_Send : grpc.GenericClientStream.Send.spec (GF := GF) (hG := hG))
    (wp_Recv : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG))
    (wp_CloseSend : grpc.GenericClientStream.CloseSend.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG))
    (p : Loc) (cs : GoInterface) (γ : StreamNames) (Up : Nat → Req.M → IProp GF)
    (Dn : Nat → Rep.M → IProp GF) (cd : context.ContextDesc (IProp GF)) :
    structFieldRef (google_golang_org.grpc.GenericClientStream V W) go!"ClientStream" p ↦□ cs ∗
      cliStreamIs cs γ Req Rep Up Dn cd ∗ (□ ∀ l : Loc, l ↦ (zero_val W) -∗ Rep.own l) ⊢
    cliBidiStreamIs (interface.mkOk (go.GoType.PointerType
      (google_golang_org.grpc.GenericClientStream.ty Req.ty Rep.ty)) #p) γ Req Rep Up Dn cd := by
  iintro ⟨#Hf, #Hraw, #Hown⟩
  iunfold cliStreamIs at Hraw
  icases Hraw with ⟨%ci, %Hcs, #HSend, #HRecv, #HClose, #HCtx⟩
  subst Hcs
  unfold cliBidiStreamIs
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %L %l %m %Φ !> ⟨Htok, Hs, HUp⟩ HΦ
    iapply (wp_Send Req.ty Rep.ty V W p ci l Φ)
    isplitr
    · iexact Hf
    iapply HSend $$ %L %l %m [Htok Hs HUp]
    · iframe
    iexact HΦ
  isplitr
  · iintro !> %L %Φ !> Htok HΦ
    iapply (wp_Recv Req.ty Rep.ty V W p ci Φ)
    isplitr
    · iexact Hf
    iintro %m Hm
    ihave Hm' := Hown $$ %m Hm
    iapply HRecv $$ %L %m [Htok Hm']
    · iframe
    iintro !> %err Hres
    iexists err
    isplitr
    · ipureintro; rfl
    icases Hres with (⟨%Herr, %mm, Hr, HDn, Htok⟩ | ⟨#Heof, %Hne, Htok, #Hcl, -⟩ |
      ⟨#Hse, Htok, -⟩)
    · subst Herr
      simp only [↓reduceIte]
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists mm
      iframe
    · simp only [Hne, ↓reduceIte]
      iapply HΦ
      iright; ileft
      iframe
      iframe #
      ipureintro; exact ⟨rfl, Hne⟩
    · ihave #Hse' := Hse
      iunfold cliStreamErr at Hse'
      icases Hse' with ⟨%Hne, -, -⟩
      simp only [Hne.1, ↓reduceIte]
      iapply HΦ
      iright; iright
      iframe
      iframe #
      ipureintro; rfl
  isplitr
  · iintro !> %L %Φ !> Htok HΦ
    iapply (wp_CloseSend Req.ty Rep.ty V W p ci Φ)
    isplitr
    · iexact Hf
    iapply HClose $$ %L [Htok]
    · iframe
    iexact HΦ
  · iintro !> %Φ !> - HΦ
    iapply (wp_Context Req.ty Rep.ty V W p ci Φ)
    isplitr
    · iexact Hf
    iapply HCtx $$ []
    · itrivial
    iexact HΦ

/-! ## The registration: stream handlers, the interceptor chain, grpc's runs -/

/-- **A stream specification of a method** (what the handler takes and the client learns, per
stream): `Spec γ Dn`, `Dn` the server's content of each response. -/
abbrev StreamSpec (Rep : StreamMsg GF) : Type := StreamNames → (Nat → Rep.M → IProp GF) → IProp GF

/-- **The stream specification is satisfiable, per stream** (persistent): for any stream's names
some content `Dn` meets it, persistently. What lets the transport fix `Dn` at a stream's creation
and give `Spec γ Dn` to both ends. -/
def streamSpecOk {Rep : StreamMsg GF} (Spec : StreamSpec Rep) : IProp GF :=
  iprop(□ ∀ γ : StreamNames, ∃ Dn : Nat → Rep.M → IProp GF, □ Spec γ Dn)

instance streamSpecOk_persistent {Rep : StreamMsg GF} (Spec : StreamSpec Rep) :
    Persistent (streamSpecOk (GF := GF) Spec) := by
  unfold streamSpecOk; infer_instance

/-- **A service's stream method `h` meets `Spec`, with the client's content `Up` and the per-run
resource `S`** (persistent; the stream analogue of `grpcHandlerOk`): a call `h(st)` on a wrapped
server end (`srvStreamIs`, both tokens at `[]`), given `S` and `Spec γ Dn`, returns (nothing
promised: the run's resources need not come back, see the file header). -/
def grpcStreamHandlerOk {Req Rep : StreamMsg GF} (h : val) (S : IProp GF)
    (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) : IProp GF :=
  iprop(□ ∀ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (Φ : val → IProp GF),
    Spec γ Dn -∗ S -∗ srvStreamIs st γ Req Rep Up Dn ci cd -∗ srvRecvTok (Req := Req) γ [] -∗
    srvSendTok (Rep := Rep) γ [] -∗ streamAuxTok γ -∗ ▷ (∀ err : GoInterface, Φ #err) -∗
    WP (App (Val h) (Val #st)) {{ Φ }})

instance grpcStreamHandlerOk_persistent {Req Rep : StreamMsg GF} (h : val) (S : IProp GF)
    (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    Persistent (grpcStreamHandlerOk h S Up Spec) := by
  unfold grpcStreamHandlerOk; infer_instance

/-- **An interceptor's `info`** (the `*grpc.StreamServerInfo` grpc allocates for a streaming
call): its fields, read-only. -/
def srvStreamInfoIs (info : Loc) : IProp GF :=
  iprop(∃ fm : GoString, ∃ cs ss : Bool,
    structFieldRef google_golang_org.grpc.StreamServerInfo go!"FullMethod" info ↦□ fm ∗
    structFieldRef google_golang_org.grpc.StreamServerInfo go!"IsClientStream" info ↦□ cs ∗
    structFieldRef google_golang_org.grpc.StreamServerInfo go!"IsServerStream" info ↦□ ss)

instance srvStreamInfoIs_persistent (info : Loc) : Persistent (srvStreamInfoIs (GF := GF) info) := by
  unfold srvStreamInfoIs; infer_instance

/-- A stream handler's call `h(srv, stream)` (`grpc.StreamHandler`, a `StreamDesc.Handler`). -/
abbrev streamHandlerCall (h : val) (srv st : val) : Expr :=
  App (App (Val h) (Val srv)) (Val st)

/-- A stream interceptor's call `ic(srv, ss, info, handler)` (`grpc.StreamServerInterceptor`). -/
abbrev streamInterceptorCall (ic : GoFunc) (srv st info : val) (h : GoFunc) : Expr :=
  App (App (App (App (Val #ic) (Val srv)) (Val st)) (Val info)) (Val #h)

/-- **The server's stream interceptor chain `ics` over the stream handler `h`** (grpc's
`chainStreamServerInterceptors`, `getChainStreamHandler`; as `srvChainWP` for unary calls): with
no interceptor, grpc calls `h(srv, ss)` itself; otherwise the first interceptor is called with a
handler `h'` of grpc's making, whose calls are the rest of the chain's (with the same `info`). `Ψ`
is the call's postcondition. -/
def srvStreamChainWP (info : val) : List GoFunc → val → val → val → (val → IProp GF) → IProp GF
  | [], h, srv, st, Ψ => WP (streamHandlerCall h srv st) {{ Ψ }}
  | ic :: ics, h, srv, st, Ψ =>
    iprop(∀ h' : GoFunc,
      (□ ∀ (srv' st' : val) (Ψ' : val → IProp GF),
        srvStreamChainWP info ics h srv' st' Ψ' -∗ WP (streamHandlerCall #h' srv' st') {{ Ψ' }}) -∗
      WP (streamInterceptorCall ic srv st info h') {{ Ψ }})

/-- **The stream interceptor `ic` is transparent, with its per-run resource `R`** (persistent;
the stream analogue of `srvInterceptorOk`): called with `R`, a raw server end `st`, an `info` and
a handler `h`, it either calls `h` once on the same service value and a server end `st'` of the
same stream (the same queues, tokens and contents; possibly another context of the run's: etcd's
`newStreamInterceptor` wraps `ss` in a `serverStreamWithCtx` with a cancellable child context when
the client requires a leader, grpc-prometheus's in a counting `monitoredServerStream`) and returns
its result, or returns a non-nil error without calling `h`; `R` comes back either way. The caller
gives both continuations (`∧`: one is taken). The handler returns an `error` value: a
deferred-call wrapper needs this, as `srvInterceptorOk` does. -/
def srvStreamInterceptorOk (ic : GoFunc) (R : IProp GF) : IProp GF :=
  iprop(□ ∀ (Req Rep : StreamMsg GF) (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF)
      (γ : StreamNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (srv st : GoInterface) (info : Loc) (h : GoFunc) (Ψ : val → IProp GF),
    R -∗ srvRawStreamIs st γ Req Rep Up Dn ci cd -∗ srvStreamInfoIs info -∗
    ((∀ (st' : GoInterface) (ci' : GoInterfaceOk) (cd' : context.ContextDesc (IProp GF)),
        srvRawStreamIs st' γ Req Rep Up Dn ci' cd' -∗
        WP (streamHandlerCall #h #srv #st')
          {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗ (R -∗ Ψ v) }}) ∧
      (R -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ Ψ #err)) -∗
    WP (streamInterceptorCall ic #srv #st #info h) {{ Ψ }})

instance srvStreamInterceptorOk_persistent (ic : GoFunc) (R : IProp GF) :
    Persistent (srvStreamInterceptorOk (GF := GF) ic R) := by
  unfold srvStreamInterceptorOk; infer_instance

/-- **Each stream interceptor of `ics` is transparent, with its resource in `Rs`**
(persistent). -/
def srvStreamInterceptorsOk : List GoFunc → List (IProp GF) → IProp GF
  | [], [] => iprop(True)
  | ic :: ics, R :: Rs => iprop(srvStreamInterceptorOk ic R ∗ srvStreamInterceptorsOk ics Rs)
  | _, _ => iprop(⌜False⌝)

instance srvStreamInterceptorsOk_persistent (ics : List GoFunc) (Rs : List (IProp GF)) :
    Persistent (srvStreamInterceptorsOk ics Rs) := by
  induction ics generalizing Rs with
  | nil => cases Rs <;> (unfold srvStreamInterceptorsOk; infer_instance)
  | cons ic ics ih =>
    cases Rs with
    | nil => unfold srvStreamInterceptorsOk; infer_instance
    | cons R Rs => unfold srvStreamInterceptorsOk; have := ih Rs; infer_instance

/-- **A chain of transparent stream interceptors runs the handler or fails**
(`srvStreamChainWP` from the interceptors' contracts): with the interceptors' resources, a raw
server end, an `info`, and both continuations of the handler's call (on any server end of the
same stream, its result with the resources back; or an early error with them back), the chain's
call meets `Ψ`. -/
theorem srvStreamChainWP_of_ok (ics : List GoFunc) (Rs : List (IProp GF)) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Dn : Nat → Rep.M → IProp GF) (γ : StreamNames)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (srv st : GoInterface)
    (info : Loc) (h : val) (Ψ : val → IProp GF) :
    srvStreamInterceptorsOk ics Rs ∗ ([∗list] R ∈ Rs, R) ∗ srvRawStreamIs st γ Req Rep Up Dn ci cd ∗
      srvStreamInfoIs info ∗
      ((∀ (st' : GoInterface) (ci' : GoInterfaceOk) (cd' : context.ContextDesc (IProp GF)),
          srvRawStreamIs st' γ Req Rep Up Dn ci' cd' -∗
          WP (streamHandlerCall h #srv #st')
            {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗ (([∗list] R ∈ Rs, R) -∗ Ψ v) }}) ∧
        (([∗list] R ∈ Rs, R) -∗ ∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ Ψ #err)) ⊢
    srvStreamChainWP #info ics h #srv #st Ψ := by
  induction ics generalizing Rs Ψ st ci cd with
  | nil =>
    cases Rs with
    | cons R Rs =>
      rw [show srvStreamInterceptorsOk (GF := GF) [] (R :: Rs) = iprop(⌜False⌝) from rfl]
      iintro ⟨%H, -⟩; exact H.elim
    | nil =>
      iintro ⟨-, -, #Hst, -, H⟩
      unfold srvStreamChainWP
      icases H with ⟨H, -⟩
      ihave H := H $$ %st %ci %cd Hst
      iapply (wp_mono (Φ := fun v => iprop(∃ err : GoInterface, ⌜v = #err⌝ ∗
        (([∗list] R ∈ ([] : List (IProp GF)), R) -∗ Ψ v)))) $$ H
      iintro %v ⟨%err, %Hv, HΨ⟩
      iapply HΨ
      iapply BigSepL.bigSepL_nil.2
      itrivial
  | cons ic ics ih =>
    cases Rs with
    | nil =>
      rw [show srvStreamInterceptorsOk (GF := GF) (ic :: ics) [] = iprop(⌜False⌝) from rfl]
      iintro ⟨%H, -⟩; exact H.elim
    | cons R Rs =>
      rw [show srvStreamInterceptorsOk (GF := GF) (ic :: ics) (R :: Rs) =
        iprop(srvStreamInterceptorOk ic R ∗ srvStreamInterceptorsOk ics Rs) from rfl]
      iintro ⟨⟨#Hic, #Hoks⟩, HRs, #Hst, #Hinfo, H⟩
      ihave ⟨HR, HRs⟩ := (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R)
        (xs := Rs)).1 $$ HRs
      unfold srvStreamChainWP
      iintro %h' #Hh'
      iunfold srvStreamInterceptorOk at Hic
      iapply Hic $$ %Req %Rep %Up %Dn %γ %ci %cd %srv %st %info %h' %Ψ HR Hst Hinfo
      isplit
      · iintro %st' %ci' %cd' #Hst'
        iapply Hh'
        iapply (ih (Rs := Rs) (Ψ := fun v => iprop(∃ err : GoInterface, ⌜v = #err⌝ ∗ (R -∗ Ψ v)))
          (st := st') (ci := ci') (cd := cd'))
        iframe #
        iframe
        isplit
        · icases H with ⟨H, -⟩
          iintro %st'' %ci'' %cd'' #Hst''
          ihave H := H $$ %st'' %ci'' %cd'' Hst''
          iapply (wp_mono (Φ := fun v => iprop(∃ err : GoInterface, ⌜v = #err⌝ ∗
            (([∗list] R ∈ R :: Rs, R) -∗ Ψ v)))) $$ H
          iintro %v ⟨%err, %Hv, HΨ⟩
          iexists err
          isplitr
          · ipureintro; exact Hv
          iintro HRs'
          iexists err
          isplitr
          · ipureintro; exact Hv
          iintro HR'
          iapply HΨ
          iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R)
            (xs := Rs)).2
          iframe
        · icases H with ⟨-, H⟩
          iintro HRs' %err %Herr
          iexists err
          isplitr
          · ipureintro; rfl
          iintro HR'
          iapply H $$ [HR' HRs'] %err %Herr
          iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
          iframe
      · icases H with ⟨-, H⟩
        iintro HR' %err %Herr
        iapply H $$ [HR' HRs] %err %Herr
        iapply (BigSepL.bigSepL_cons (PROP := IProp GF) (Φ := fun _ R => R) (x := R) (xs := Rs)).2
        iframe

/-- The namespace of grpc's stream-slot pools. -/
def grpcSlotN : Namespace := nroot .@ "grpc.streamSlots"

/-- **A pool of the per-run resource `S`** (persistent; 2026-10-18): the copies of `S` grpc's
runtime holds for the stream runs it will start (`grpc.serveStream` makes it of its `n` copies
and takes one for each run); a run, or a goroutine of it, returns its copy when done
(`grpcSlotPool_return`). -/
def grpcSlotPool (S : IProp GF) : IProp GF :=
  inv grpcSlotN iprop(∃ k : Nat, [∗list] _x ∈ List.replicate k (), S)

/-- **The stream method handler `mh` with the service `srv`, under the stream interceptor chain
`ics`, meets `Spec` with the client's content `Up` and the per-run resource `S`** (persistent;
what grpc's runtime runs for a streaming call, `processStreamingRPC`): the stream specification
is satisfiable per stream (`streamSpecOk`), and a run, given `Spec γ Dn`, `S`, the run's context,
a fresh raw server end of the stream (`srvRawStreamIs`, both tokens at `[]`) and grpc's `info`,
through the chain, terminates or not, promising nothing (`S` is not returned: the run keeps it,
see the file header). -/
def grpcStreamMethodOk {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) : IProp GF :=
  iprop(streamSpecOk Spec ∗
    □ ∀ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (info : Loc),
      Spec γ Dn -∗ S -∗ srvRawStreamIs st γ Req Rep Up Dn ci cd -∗
      srvRecvTok (Req := Req) γ [] -∗ srvSendTok (Rep := Rep) γ [] -∗ streamAuxTok γ -∗
      srvStreamInfoIs info -∗
      srvStreamChainWP #info ics mh #srv #st (fun _ => iprop(True)))

/-- **`grpcStreamMethodOk` with the slot pool** (persistent; 2026-10-18): as `grpcStreamMethodOk`,
and a run is also given the runtime's pool of `S` (`grpcSlotPool S`), to return its copy to
when it is done (from any thread: `Watch` returns while its receive loop may hold its slot). What
`grpc.serveStream` takes. -/
def grpcStreamMethodOkR {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    IProp GF :=
  iprop(streamSpecOk Spec ∗
    □ ∀ (γ : StreamNames) (Dn : Nat → Rep.M → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (info : Loc),
      Spec γ Dn -∗ S -∗ grpcSlotPool S -∗ srvRawStreamIs st γ Req Rep Up Dn ci cd -∗
      srvRecvTok (Req := Req) γ [] -∗ srvSendTok (Rep := Rep) γ [] -∗ streamAuxTok γ -∗
      srvStreamInfoIs info -∗
      srvStreamChainWP #info ics mh #srv #st (fun _ => iprop(True)))

instance grpcStreamMethodOkR_persistent {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    Persistent (grpcStreamMethodOkR mh srv ics S Up Spec) := by
  unfold grpcStreamMethodOkR; infer_instance

/-- A run that keeps its slot meets the pooled contract (it ignores the pool). -/
theorem grpcStreamMethodOk_R {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    grpcStreamMethodOk mh srv ics S Up Spec ⊢ grpcStreamMethodOkR mh srv ics S Up Spec := by
  unfold grpcStreamMethodOk grpcStreamMethodOkR
  iintro ⟨#Hs, #Hr⟩
  iframe Hs
  iintro !> %γ %Dn %ci %cd %st %info HSp HS - Hraw HR HT Ha Hi
  iapply Hr $$ HSp HS Hraw HR HT Ha Hi

instance grpcStreamMethodOk_persistent {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (S : IProp GF) (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    Persistent (grpcStreamMethodOk mh srv ics S Up Spec) := by
  unfold grpcStreamMethodOk; infer_instance

/-- **A streaming method a server registers**: its full name (`"/etcdserverpb.Watch/Watch"`),
its message types, the client's content of its requests, its stream specification, the
generated handler its `ServiceDesc`'s `StreamDesc` holds (`etcdserverpb._Watch_Watch_Handler`),
and the service value registered with the `ServiceDesc`. -/
structure GrpcStreamMethod (GF : BundledGFunctors) where
  name : GoString
  Req : StreamMsg GF
  Rep : StreamMsg GF
  Up : Nat → Req.M → IProp GF
  spec : StreamSpec Rep
  handler : val
  srv : GoInterface

end defs

/-! ## The opaque facts about grpc's runtime (streams) -/

/-- **The gRPC server listening at `addr`, built with the stream interceptor chain `ics`, its
services' streaming methods `sregs` registered** (exclusive; an axiomatized predicate, the stream
analogue of `grpcServerAt`, which keeps its arity): `ics` the stream interceptors `grpc.NewServer`'s
options chain (`StreamInterceptor`'s, then `ChainStreamInterceptor`'s, in order: etcd's
`v3rpc.Server` installs grpc-prometheus's and `newStreamInterceptor`), `sregs` the `(full method
name, StreamDesc.Handler, service value)` of every stream of the `ServiceDesc`s registered with
`RegisterService`. Established by the server's unverified construction: a premise of the
server's results. -/
axiom grpcStreamServerAt {GF : BundledGFunctors} [GooseExts] (addr : GoString) (ics : List GoFunc)
  (sregs : List (GoString × val × GoInterface)) : IProp GF

/-- **The server at `addr` runs the stream handler `mh` with the service `srv` and the stream
chain `ics` for the method `name`, with the per-run resource `S`** (persistent; an axiomatized
predicate, introduced only by `grpc.serveStream`). -/
axiom grpcServesStream {GF : BundledGFunctors} [GooseExts] (addr name : GoString) (mh : val)
  (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) : IProp GF

axiom grpcServesStream_persistent {GF : BundledGFunctors} [GooseExts] (addr name : GoString)
  (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) :
  Persistent (grpcServesStream addr name mh srv ics S)

attribute [instance] grpcServesStream_persistent

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The streaming method `name` of the server at `addr` meets `Spec`, with the client's
content `Up`** (persistent): grpc's runtime at `addr` runs, for `name`, a stream handler with a
service and the server's stream chain that meet it (`grpcStreamMethodOk`), with the resource it
was served with. What a client's `NewStream` needs. -/
def isGrpcStream {Req Rep : StreamMsg GF} (addr name : GoString) (Up : Nat → Req.M → IProp GF)
    (Spec : StreamSpec Rep) : IProp GF :=
  iprop(∃ (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
    grpcServesStream addr name mh srv ics S ∗ grpcStreamMethodOkR mh srv ics S Up Spec)

instance isGrpcStream_persistent {Req Rep : StreamMsg GF} (addr name : GoString)
    (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    Persistent (isGrpcStream addr name Up Spec) := by
  unfold isGrpcStream; infer_instance

/-- **The streaming method `name` of every server at `addrs`, each with its own content and
specification** (persistent; D32): what a stream on a connection to `addrs` needs, wherever grpc's
balancer sends it. Reducible, by recursion, so that at one address it is that address's
`isGrpcStream` (as `isGrpcRpcs`, D27). -/
@[reducible] def isGrpcStreams {Req Rep : StreamMsg GF} : List GoString → GoString →
    (GoString → Nat → Req.M → IProp GF) → (GoString → StreamSpec Rep) → IProp GF
  | [], _, _, _ => iprop(True)
  | [a], name, Up, Spec => isGrpcStream a name (Up a) (Spec a)
  | a :: b :: rest, name, Up, Spec =>
    iprop(isGrpcStream a name (Up a) (Spec a) ∗ isGrpcStreams (b :: rest) name Up Spec)

instance isGrpcStreams_persistent {Req Rep : StreamMsg GF} (addrs : List GoString)
    (name : GoString) (Up : GoString → Nat → Req.M → IProp GF) (Spec : GoString → StreamSpec Rep) :
    Persistent (isGrpcStreams addrs name Up Spec) := by
  induction addrs with
  | nil => unfold isGrpcStreams; infer_instance
  | cons a rest ih =>
    cases rest with
    | nil => unfold isGrpcStreams; infer_instance
    | cons b bs => unfold isGrpcStreams; infer_instance

/-- A served stream handler that meets `Spec` registers it. -/
theorem isGrpcStream_intro {Req Rep : StreamMsg GF} (addr name : GoString) (mh : val)
    (srv : GoInterface) (ics : List GoFunc) (S : IProp GF) (Up : Nat → Req.M → IProp GF)
    (Spec : StreamSpec Rep) :
    grpcServesStream addr name mh srv ics S ∗ grpcStreamMethodOkR mh srv ics S Up Spec ⊢
      isGrpcStream addr name Up Spec := by
  iintro ⟨#H1, #H2⟩
  unfold isGrpcStream
  iexists mh, srv, ics, S
  iframe #

/-- **Serving streams** (an axiom, the server side of the stream boundary; the stream analogue of
`grpc.serve`): a gRPC server at `addr`, built with the stream chain `ics`, with the streaming
methods `sregs` registered (`grpcStreamServerAt`), of which the methods `ms` (distinct names),
each meeting its stream specification with the per-run resource `S` as grpc runs it
(`grpcStreamMethodOkR`: its `StreamDesc.Handler` on the registered service value, a raw server
end of a fresh stream with the run's context, through the chain), and that hands the runtime `n`
copies of `S`, is served at `addr`. The copies form a pool (`grpcSlotPool S`, separate from the
unary runs'): a run takes one and is given the pool, to return its copy to when the run's
resources are free (2026-10-18, the axiom audit; until then a run kept its copy, so the model
started at most `n` streams in all while Go starts every one). The runtime starts a stream when
the pool holds a copy, so the model bounds the runs holding a slot at once (`n`: etcd's watch
runs hold reader slots of its locks, which Go's `RWMutex` bounds at about `2 ^ 30` concurrent
readers). -/
axiom grpc.serveStream (addr : GoString) (ics : List GoFunc)
    (sregs : List (GoString × val × GoInterface)) (ms : List (GrpcStreamMethod GF)) (S : IProp GF)
    (n : Nat) :
  (ms.map GrpcStreamMethod.name).Nodup → (∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ sregs) →
  (grpcStreamServerAt addr ics sregs ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
    [∗list] m ∈ ms, grpcStreamMethodOkR m.handler m.srv ics S m.Up m.spec) ⊢
  |={⊤}=> [∗list] m ∈ ms, grpcServesStream addr m.name m.handler m.srv ics S

/-- **The streaming methods of a served server are registered** (`grpc.serveStream`,
`isGrpcStream_intro`), for runs that keep their slots (`grpcStreamMethodOk`, as
`grpcStreamMethodOk_R`). -/
theorem grpc_serveStream_rpcs (addr : GoString) (ics : List GoFunc)
    (sregs : List (GoString × val × GoInterface)) (ms : List (GrpcStreamMethod GF)) (S : IProp GF)
    (n : Nat) (hnd : (ms.map GrpcStreamMethod.name).Nodup)
    (hreg : ∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ sregs) :
    (grpcStreamServerAt addr ics sregs ∗ ([∗list] _x ∈ List.replicate n (), S) ∗
      □ [∗list] m ∈ ms, grpcStreamMethodOk m.handler m.srv ics S m.Up m.spec) ⊢
    |={⊤}=> [∗list] m ∈ ms, isGrpcStream addr m.name m.Up m.spec := by
  iintro ⟨Hl, Hs, #Hh0⟩
  ihave #Hh : iprop([∗list] m ∈ ms, grpcStreamMethodOkR m.handler m.srv ics S m.Up m.spec) $$ []
  · iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ms)
      (Φ := fun _ m => grpcStreamMethodOk m.handler m.srv ics S m.Up m.spec)
      (Ψ := fun _ m => grpcStreamMethodOkR m.handler m.srv ics S m.Up m.spec)
      (fun {_ m} => grpcStreamMethodOk_R (GF := GF) m.handler m.srv ics S m.Up m.spec)) $$ Hh0
  imod (grpc.serveStream addr ics sregs ms S n hnd hreg) $$ [Hl Hs] with Hsv
  · iframe
    iexact Hh
  imodintro
  have Hm := BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := ms)
    (Φ := fun _ m => iprop(grpcServesStream addr m.name m.handler m.srv ics S ∗
      grpcStreamMethodOkR m.handler m.srv ics S m.Up m.spec))
    (Ψ := fun _ m => isGrpcStream addr m.name m.Up m.spec)
    (fun {_ m} => isGrpcStream_intro (GF := GF) addr m.name m.handler m.srv ics S m.Up m.spec)
  iapply Hm
  iapply BigSepL.bigSepL_sep_eqv.2
  isplitl [Hsv]
  · iexact Hsv
  · iexact Hh

end reg

end EtcdGrove
end Perennial
