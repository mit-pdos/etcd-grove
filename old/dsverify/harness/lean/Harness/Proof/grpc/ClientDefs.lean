/-
The client side of the lab's grpc model (`clientconn.go`): the representation predicates of a
`*ClientConn` and of its transports, their lock invariants and ghost state, and the specs of
`Dial`/`DialContext`/`NewClient`, `(*ClientConn).Invoke`, `Close` and the transport's internals
(proved in `Client.lean`, over the ghost lemmas of `ClientGhost.lean`).

**A transport** (one connection; `TNames`): the connection's names (`GConnNames`, `Proto.lean`),
a copy `cl` of the connection's client frames (mono-list; halves in `sendInv` and `tInv`, so that
the holder of `sending` knows the frames exactly and the invariant `tInv` bounds their number
below `2 ^ 64`), the shutdown flag `sdl` (mono-list of `Unit`, `[()]` once shut down; full
authority in `muInv`, so `shutLb` is a persistent witness) and a token `dead` the reader holds
while it runs. A call's sequence number is its frame's index in the list (`t.seq`, owned by
`sendInv`, is the list's length while the transport is up): no two calls share one, so a pending
entry under `s` is the call of frame `s` (`callRes`, with a lower bound of the list naming frame
`s`'s continuation and collection token), and the reader routes an answer by its sequence
number. A call appends its frame to the ghost list when it registers (holding both locks), before
writing it: the protocol speaks of prefixes of the frames, and the deposit goes to the
connection then (the server takes it only once it read the frame).

**Invariants.**
* `sendInv` (`t.sending`): `t.seq`, the dialer's `sendTok`, the `cl` half, and while up, the
  bytes written are exactly the frames.
* `muInv` (`t.mu`): `pending`, `shutdown`, the `sdl` authority; while the reader runs, each
  pending call's resources (`callRes`): the promise of its `done` channel (`callDone`) and the
  collection token of its frame.
* `tInv` (an invariant): the `cl` half and the connection's `reqs` half (the other is in
  `connInv`), with the number of frames below `2 ^ 64`.
-/
module

public import Harness.Proof.grpc.Wire
public import Harness.Proof.grpc.Pb
public import Harness.Proof.grpc.StatusSpec
public import Harness.Proof.net.Dial
public import Harness.Proof.net.TCPConn__Close
public import Perennial.Golang.Theory.Chan.Idioms.Future
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn
open google_golang_org.protobuf.proto (PbCodec PbKit codecSet kitCodecOk)
open net.rpc (connIface errAny)

namespace google_golang_org.grpc

/-- The ghost names of a transport (see the file header). -/
structure TNames where
  conn : GConnNames
  cl : GName
  sdl : GName
  dead : GName

def tN : Namespace := ndot grpcN "transport"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The transport is shut down (persistent). -/
def shutLb (γn : TNames) : IProp GF := monoListLbOwn γn.sdl [()]

/-- What a call's `done` channel carries: `nil` (the transport failed), or a `*response` with
the answer's code, message and reply bytes, and `Φ` of the reply for status `OK`. -/
def callDone (Φ : List w8 → IProp GF) (r : Loc) : IProp GF :=
  iprop(⌜r = null⌝ ∨
    ∃ (code : w64) (msg : GoString) (body : GoSlice) (b : List w8),
      structFieldRef response go!"code" r ↦ code ∗ structFieldRef response go!"msg" r ↦ msg ∗
      structFieldRef response go!"body" r ↦ body ∗ body ↦* b ∗
      ⌜code = W64 0 ∨ uint.Z code < 2 ^ 32⌝ ∗
      (if code = W64 0 then Φ b else iprop(True)))

/-- The resources of the pending call `pc` under sequence number `s` (with the map entry, in
`muInv`): frame `s` is its call (a lower bound of the list), the promise of its channel, its
saved continuation and its collection token. -/
def callRes (γn : TNames) (s : w64) (pc : Loc) : IProp GF :=
  iprop(∃ (L : List CFrame) (fm : GoString) (b : List w8) (post col : GName) (ch : Loc)
      (γf : FutureNames) (Φ : List w8 → IProp GF),
    monoListLbOwn γn.conn.reqs L ∗ ⌜L[uint.nat s]? = some (.call fm b post col)⌝ ∗
    structFieldRef pendingCall go!"done" pc ↦□ ch ∗ isFuture Loc γf ch ∗
    Fulfill γf (callDone Φ) ∗ savedPredOwn post .discard Φ ∗ token col)

/-- The transport's invariant (see the file header). -/
def tInv (γn : TNames) : IProp GF :=
  iprop(∃ L : List CFrame, monoListAuthOwn γn.conn.reqs (1 : Qp).half L ∗
    monoListAuthOwn γn.cl (1 : Qp).half L ∗ ⌜L.length < 2 ^ 64⌝)

/-- The invariant of `t.sending` (see the file header). -/
def sendInv (γn : TNames) (t : Loc) (cid : w64) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ (L : List CFrame) (sq : w64) (Wb : List w8),
    structFieldRef transport go!"seq" t ↦ sq ∗ sendTok cid false (reqProto W a) Wb ∗
    monoListAuthOwn γn.cl (1 : Qp).half L ∗ ⌜∀ q ∈ cmsgs L, q.length < 2 ^ 63⌝ ∗
    (⌜sq = W64 L.length ∧ Wb = net.rpc.framesOf (cmsgs L)⌝ ∨ shutLb γn))

/-- The pending calls' resources while the reader runs. -/
def pendAlive (γn : TNames) (m : GMap w64 Loc) : IProp GF :=
  iprop([∗map] s ↦ pc ∈ m, callRes γn s pc)

/-- The invariant of `t.mu` (see the file header). -/
def muInv (γn : TNames) (t : Loc) : IProp GF :=
  iprop(∃ (mp : Loc) (m : GMap w64 Loc) (sd : Bool),
    structFieldRef transport go!"pending" t ↦ mp ∗ mp ↦$ m ∗
    structFieldRef transport go!"shutdown" t ↦ sd ∗
    monoListAuthOwn γn.sdl 1 (if sd then [()] else []) ∗
    (pendAlive γn m ∨ (token γn.dead ∗ ⌜m = ∅ ∧ sd = true⌝)))

/-- `t` is a transport of address `a` in world `W` (persistent). -/
def isTransportN (t : Loc) (W : GrpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64)
    (γn : TNames) : IProp GF :=
  iprop(structFieldRef transport go!"conn" t ↦□ cv ∗ connIface cv cid false ∗
    isGConn W a cid γn.conn ∗
    sync.isMutex (structFieldRef transport go!"sending" t) (sendInv γn t cid W a) ∗
    sync.isMutex (structFieldRef transport go!"mu" t) (muInv γn t) ∗
    inv tN (tInv γn))

/-- `t` is a transport of address `a` in world `W` (persistent). -/
def isTransport (t : Loc) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ (cv : GoInterface) (cid : w64) (γn : TNames), isTransportN t W a cv cid γn)

/-- The reader's resources (`input`): its token, having read the frames `Q` of answers. -/
def readerOwn (γn : TNames) (cid : w64) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ Q : List (List w8),
    recvTok cid false (respProto W a) (net.rpc.framesOf Q) ∗ token γn.dead ∗
    ⌜∀ q ∈ Q, q.length < 2 ^ 63⌝)

/-- The invariant of a `*ClientConn`'s `mu`: its current transport (nil or one of its
address) and `closed`. -/
def ccInv (cc : Loc) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ (t : Loc) (cl : Bool), structFieldRef ClientConn go!"t" cc ↦ t ∗
    structFieldRef ClientConn go!"closed" cc ↦ cl ∗ (⌜t = null⌝ ∨ isTransport t W a))

/-- `cc` is a client connection to address `a` of world `W` (persistent). -/
def isClientConn (cc : Loc) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(structFieldRef ClientConn go!"target" cc ↦□ a ∗
    sync.isMutex (structFieldRef ClientConn go!"mu" cc) (ccInv cc W a) ∗
    grpcAddr W a)

instance regElem_persistent' (W : GrpcWorld GF) (cid : w64) (γ : GConnNames) :
    Persistent (regElem W cid γ) := by unfold regElem; infer_instance
instance isGConn_persistent' (W : GrpcWorld GF) (a : GoString) (cid : w64) (γ : GConnNames) :
    Persistent (isGConn W a cid γ) := by unfold isGConn; infer_instance
instance respProto_persistent' (W : GrpcWorld GF) (a : GoString) (cid : w64) (bs : List w8) :
    Persistent (respProto W a cid bs) := by unfold respProto; infer_instance
instance reqProto_persistent' (W : GrpcWorld GF) (a : GoString) (cid : w64) (bs : List w8) :
    Persistent (reqProto W a cid bs) := by unfold reqProto; infer_instance

instance grpcAddr_persistent' (W : GrpcWorld GF) (a : GoString) :
    Persistent (grpcAddr W a) := by unfold grpcAddr; infer_instance

instance shutLb_persistent (γn : TNames) : Persistent (shutLb (GF := GF) γn) := by
  unfold shutLb; infer_instance
instance isTransportN_persistent (t : Loc) (W : GrpcWorld GF) (a : GoString) (cv : GoInterface)
    (cid : w64) (γn : TNames) : Persistent (isTransportN t W a cv cid γn) := by
  unfold isTransportN isGConn regElem; infer_instance
instance isTransport_persistent (t : Loc) (W : GrpcWorld GF) (a : GoString) :
    Persistent (isTransport t W a) := by unfold isTransport; infer_instance
instance isClientConn_persistent (cc : Loc) (W : GrpcWorld GF) (a : GoString) :
    Persistent (isClientConn cc W a) := by
  unfold isClientConn grpcAddr; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]
variable [google_golang_org.protobuf.reflect.protoreflect.Assumptions]
variable [google_golang_org.protobuf.proto.Assumptions]
variable [google_golang_org.grpc.codes.Assumptions] [google_golang_org.grpc.status.Assumptions]
variable [context.Assumptions] [fmt.Assumptions]
variable [PbKit] [PbCodec GF]

/-- What a caller of `Invoke` with spec `S` gives for its request `args`: a nil request (the
empty message) with the deposit `S [] Φ`, or one the codec encodes, the deposit for its
encoding; `R` comes back in every case (e.g. the caller's view of `args`). -/
def encPre (args : GoInterface) (S : UnarySpec GF) (Φ : List w8 → IProp GF) (R : IProp GF) :
    IProp GF :=
  iprop((⌜args = interface.nil⌝ ∗ S [] Φ ∗ R) ∨
    (⌜args ≠ interface.nil⌝ ∗ PbCodec.marshal args (fun o => match o with
      | some bs => iprop(S bs Φ ∗ R)
      | none => R)))

/-- What a registered call's caller holds: its channel's future, awaiting `callDone Φ`. -/
def sentCall (pc : Loc) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop(∃ (ch : Loc) (γf : FutureNames), structFieldRef pendingCall go!"done" pc ↦□ ch ∗
    isFuture Loc γf ch ∗ Await γf [callDone Φ])

/-- `t.isShutdown()`. -/
abbrev transport.isShutdown.spec : Prop :=
  ∀ (t : Loc) (W : GrpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isTransport t W a }}
    (App (Val (t @!! go.GoType.PointerType transport.ty @!! go!"isShutdown")) (Val #()))
  {{ (b : Bool), RET #b; True }}

/-- `t.send(fm, req)` with the deposit for full method `fm` at `a`: a registered call and its
sequence number, or `false` (the deposit may be lost: the call ran at most once). -/
abbrev transport.send.spec : Prop :=
  ∀ (t : Loc) (W : GrpcWorld GF) (a : GoString) (fm : GoString) (req : GoSlice) (bs : List w8)
    (S : UnarySpec GF) (Φ : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isTransport t W a ∗
      req ↦* bs ∗ ⌜W.MS a fm = some S⌝ ∗ S bs Φ }}
    (App (App (Val (t @!! go.GoType.PointerType transport.ty @!! go!"send")) (Val #fm))
      (Val #req))
  {{ (pc : Loc) (seq : w64) (ok : Bool), RET (PairV (PairV #pc #seq) #ok);
      if ok then sentCall pc Φ else iprop(True) }}

/-- `t.cancel(seq)`: writes a cancellation frame (or nothing). -/
abbrev transport.cancel.spec : Prop :=
  ∀ (t : Loc) (W : GrpcWorld GF) (a : GoString) (seq : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isTransport t W a }}
    (App (Val (t @!! go.GoType.PointerType transport.ty @!! go!"cancel")) (Val #seq))
  {{ RET #(); True }}

/-- `t.input()`, the reader goroutine. -/
abbrev transport.input.spec : Prop :=
  ∀ (t : Loc) (W : GrpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64) (γn : TNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isTransportN t W a cv cid γn ∗
      readerOwn γn cid W a }}
    (App (Val (t @!! go.GoType.PointerType transport.ty @!! go!"input")) (Val #()))
  {{ RET #(); True }}

/-- `newTransport(conn)` on the dialer's end of a registered connection. -/
abbrev newTransport.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64) (γ : GConnNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ connIface cv cid false ∗
      isGConn W a cid γ ∗
      monoListAuthOwn γ.reqs (1 : Qp).half ([] : List CFrame) ∗
      sendTok cid false (reqProto W a) [] ∗ recvTok cid false (respProto W a) [] }}
    (App (Val (@! google_golang_org.grpc.newTransport)) (Val #cv))
  {{ (t : Loc), RET #t; isTransport t W a }}

/-- `cc.getTransport()`: a transport of `cc`'s address, or a status error. -/
abbrev ClientConn.getTransport.spec : Prop :=
  ∀ (cc : Loc) (W : GrpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isClientConn cc W a }}
    (App (Val (cc @!! go.GoType.PointerType ClientConn.ty @!! go!"getTransport")) (Val #()))
  {{ (t : Loc) (err : GoInterface), RET (PairV #t #err);
      (⌜err = interface.nil⌝ ∗ isTransport t W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ c msg, status.statusErrOf err c msg) }}

/-- `ctxErr(ctx)`: a status error. -/
abbrev ctxErr.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ context.isContext ctx cd }}
    (App (Val (@! google_golang_org.grpc.ctxErr)) (Val #(interface.ok ctx)))
  {{ (err : GoInterface), RET #err; ∃ c msg, status.statusErrOf err c msg }}

/-- `cc.Invoke(ctx, fm, args, reply, opts)` (`notes/grpc-model.md`): `nil` after one run of the
method's handler at the server on the encoded request, with its continuation `Φ rep` and the
reply decoded into `reply` (`Θ rep true`); or a status error, after at most one run (the deposit
may be lost), with the decoding resource `D` back or a failed decoding, and `R` (or the
encoding premise, if nothing was encoded). -/
abbrev ClientConn.Invoke.spec : Prop :=
  ∀ (cc : Loc) (W : GrpcWorld GF) (a : GoString) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (fm : GoString) (S : UnarySpec GF)
    (args reply : GoInterface) (opts : GoSlice) (Φ : List w8 → IProp GF) (R D : IProp GF)
    (Θ : List w8 → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ isClientConn cc W a ∗ context.isContext ctx cd ∗
      ⌜W.MS a fm = some S⌝ ∗ encPre args S Φ R ∗ D ∗
      □ (D -∗ ∀ rep, PbCodec.unmarshal rep reply (Θ rep)) }}
    (App (App (App (App (App (Val (cc @!! go.GoType.PointerType ClientConn.ty @!! go!"Invoke"))
      (Val #(interface.ok ctx))) (Val #fm)) (Val #args)) (Val #reply)) (Val #opts))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ R ∗ ∃ rep, Φ rep ∗ Θ rep true) ∨
      (⌜err ≠ interface.nil⌝ ∗ (∃ c msg, status.statusErrOf err c msg) ∗
        (R ∨ encPre args S Φ R) ∗ (D ∨ ∃ rep, Θ rep false)) }}

/-- `cc.Close()`: `nil`, or a status error (a second `Close`). -/
abbrev ClientConn.Close.spec : Prop :=
  ∀ (cc : Loc) (W : GrpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isClientConn cc W a }}
    (App (Val (cc @!! go.GoType.PointerType ClientConn.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∨ ∃ c msg, status.statusErrOf err c msg }}

/-- What `Dial` returns for options `os`: a client connection if some option sets credentials,
else `errNoTransportSecurity`. -/
def dialPost (W : GrpcWorld GF) (a : GoString) (os : List DialOption) (cc : Loc)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil ∧ ∃ o ∈ os, o.creds' = true⌝ ∗ isClientConn cc W a) ∨
    (⌜err ≠ interface.nil ∧ cc = null ∧ ∀ o ∈ os, o.creds' = false⌝ ∗ errAny err))

/-- `newClientConn(a, opts)`. -/
abbrev newClientConn.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opts : GoSlice) (dq : DFrac) (os : List DialOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcAddr W a ∗
      opts ↦*{dq} os }}
    (App (App (Val (@! google_golang_org.grpc.newClientConn)) (Val #a)) (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      opts ↦*{dq} os ∗ dialPost W a os cc err }}

/-- `Dial(a, opts...)`. -/
abbrev Dial.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opts : GoSlice) (dq : DFrac) (os : List DialOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcAddr W a ∗
      opts ↦*{dq} os }}
    (App (App (Val (@! google_golang_org.grpc.Dial)) (Val #a)) (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      opts ↦*{dq} os ∗ dialPost W a os cc err }}

/-- `NewClient(a, opts...)`. -/
abbrev NewClient.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opts : GoSlice) (dq : DFrac) (os : List DialOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcAddr W a ∗
      opts ↦*{dq} os }}
    (App (App (Val (@! google_golang_org.grpc.NewClient)) (Val #a)) (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      opts ↦*{dq} os ∗ dialPost W a os cc err }}

/-- `DialContext(ctx, a, opts...)`. -/
abbrev DialContext.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (ctx : GoInterface) (opts : GoSlice) (dq : DFrac)
    (os : List DialOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcAddr W a ∗
      opts ↦*{dq} os }}
    (App (App (App (Val (@! google_golang_org.grpc.DialContext)) (Val #ctx)) (Val #a))
      (Val #opts))
  {{ (cc : Loc) (err : GoInterface), RET (PairV #cc #err);
      opts ↦*{dq} os ∗ dialPost W a os cc err }}

end spec

end google_golang_org.grpc

end Perennial
