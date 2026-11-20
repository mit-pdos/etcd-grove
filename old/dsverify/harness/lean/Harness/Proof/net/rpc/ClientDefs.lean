/-
The client side of the lab's model of `net/rpc` (`client.go`; `notes/craq-net.md`, "rpc specs"):
the client's representation predicate `isClient`, its lock invariants and ghost state, and the
specs of `newClient`, `input`, `Call`, `Close`, `DialHTTPPath` and `DialHTTP` (proved in
`Client.lean`, over the ghost lemmas of `ClientGhost.lean`).

**Ghost state of a client** (`ClientNames`), over its connection's names (`RpcConnNames`,
`Proto.lean`):
* `cl`: a copy of the connection's request list `reqs` (mono-list; halves in `sendInv` and
  `cliInv`), so that the holder of `sending` knows the requests exactly;
* `pend`: the pending calls, a ghost map from a sequence number to `PEntry` (the
  `*pendingCall`, the call's saved continuation `post`, its collection token `col` and the saved
  name `ret` of its decoding resource); authority halves in `muInv` and `cliInv`. An element half
  is with the map entry (`muInv`), the other half with the request the call wrote (`cliInv`'s
  store, for each request whose answer the reader has not consumed; held by the caller between
  inserting its entry and writing its request). So a response for a request the reader has not
  consumed finds, under the request's sequence number, either nothing or that request's call.
* `cons`: the answers the reader consumed (mono-list of `(index, msg, reply)`; halves with the
  reader and `cliInv`);
* `sdl`: whether the client is shut down (mono-list of `Unit`, `[()]` once shut down; full
  authority in `muInv`, so `shutLb` is a persistent witness);
* `last`: the last insertion into the pending map (halves in `muInv` and in `sendInv` while the
  client is up; a writer whose write failed keeps its half: no insertion follows, so the entry
  it finds under its sequence number is its own);
* `dead`: a token the reader holds while it runs and gives to `muInv` when it stops.

**Invariants.**
* `sendInv` (`c.sending`): the dialer's `sendTok`, which holds `rpcHead` and the frames of the
  requests (unless shut down: after a failed write the stream holds a partial frame).
* `muInv` (`c.mu`): the fields `seq`, `pending`, `closing`, `shutdown`; while the reader runs,
  each map entry's element half and its call's resources (`callRes`: the `done` channel's
  promise, the decoding resource `D`, the collection token); a ghost entry with no map entry
  (a "zombie", left by a failed writer or by the reader for a response nobody waits for) only
  once shut down.
* `cliInv` (an invariant): the request lists, the pending authority, the consumed answers and
  the store of element halves of the requests not consumed.
-/
module

public import Harness.Proof.net.rpc.WireSpec
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

namespace net.rpc

/-- A pending call: its `*pendingCall`, the saved continuation's name `post`, the collection
token `col`, the saved name `ret` of its decoding resource. -/
abbrev PEntry := Loc × GName × GName × GName

/-- A consumed answer: the request's index, the error message, the reply. -/
abbrev Ans := Nat × GoString × List w8

/-- The ghost names of a client (see the file header). -/
structure ClientNames where
  conn : RpcConnNames
  cl : GName
  pend : GName
  cons : GName
  sdl : GName
  last : GName
  dead : GName

def cliN : Namespace := ndot rpcN "client"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [RpcKit] [RpcCodec GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The client is shut down (persistent). -/
def shutLb (γn : ClientNames) : IProp GF := monoListLbOwn γn.sdl [()]

/-- What a call's `done` channel carries: `nil` with the method's answer `Φ rep ""` and the
reply decoded (`Θ rep true`); `ServerError(msg)` (`msg ≠ ""`) with the method's answer
`Φ rep msg` and the decoding resource back (`D`); or another error, not a `ServerError`, with
the decoding resource back or a failed decoding (`Θ rep false`). Every error comes with its
`Error()` (`errMsg` for a `ServerError`, `errAny` for the others). -/
def callPost (Φ : List w8 → GoString → IProp GF) (Θ : List w8 → Bool → IProp GF)
    (D : IProp GF) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ rep, Φ rep [] ∗ Θ rep true) ∨
    (∃ msg : GoString, ⌜msg ≠ [] ∧ err = serverErr msg⌝ ∗ errMsg err msg ∗
      (∃ rep, Φ rep msg) ∗ D) ∨
    (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ errAny err ∗
      (D ∨ ∃ rep, Θ rep false)))

/-- The resources of pending call `e` (with the map entry, in `muInv`). -/
def callRes (e : PEntry) : IProp GF :=
  iprop(∃ (ch : Loc) (reply : GoInterface) (γf : FutureNames)
      (Φ : List w8 → GoString → IProp GF) (Θ : List w8 → Bool → IProp GF) (D : IProp GF),
    structFieldRef pendingCall go!"reply" e.1 ↦□ reply ∗
    structFieldRef pendingCall go!"done" e.1 ↦□ ch ∗
    isFuture GoInterface γf ch ∗ Fulfill γf (callPost Φ Θ D) ∗
    savedPredOwn e.2.1 .discard (fun p : List w8 × GoString => Φ p.1 p.2) ∗ token e.2.2.1 ∗
    savedPropOwn e.2.2.2 .discard D ∗ D ∗
    □ (D -∗ ∀ rep, RpcCodec.dec rep reply (Θ rep)) ∗
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet ∗ kitCodecOk)

/-- The store's element half for a request not consumed. -/
def storeRes (γn : ClientNames) (r : RpcReq) : IProp GF :=
  iprop(∃ (pc : Loc) (ret : GName),
    ghostMapElem γn.pend r.seq (DFrac.own (1 : Qp).half) ((pc, r.post, r.col, ret) : PEntry))

/-- The store: for each request not consumed (`C`, the consumed indices), its element half. -/
def store (γn : ClientNames) (C : List Nat) (L : List RpcReq) : IProp GF :=
  iprop([∗list] i ↦ r ∈ L, if i ∈ C then iprop(True) else storeRes γn r)

/-- The client's invariant (see the file header). -/
def cliInv (γn : ClientNames) : IProp GF :=
  iprop(∃ (L : List RpcReq) (P : GMap w64 PEntry) (C : List Ans),
    monoListAuthOwn γn.conn.reqs (1 : Qp).half L ∗ monoListAuthOwn γn.cl (1 : Qp).half L ∗
    ghostMapAuth γn.pend (1 : Qp).half P ∗ monoListAuthOwn γn.cons (1 : Qp).half C ∗
    ⌜(∀ y ∈ C, y.1 < L.length) ∧ (C.map Prod.fst).Nodup⌝ ∗
    store γn (C.map Prod.fst) L)

/-- The invariant of `c.sending`: the dialer's writer token, holding `rpcHead` and the frames
of the requests `L` (unless shut down), and the `last` half (while up). -/
def sendInv (γn : ClientNames) (cid : w64) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ (L : List RpcReq) (Wb : List w8),
    sendTok cid false (reqProto W a) Wb ∗ monoListAuthOwn γn.cl (1 : Qp).half L ∗
    ⌜∀ q ∈ L.map reqMsg, q.length < 2 ^ 63⌝ ∗
    ((⌜Wb = rpcHead ++ framesOf (L.map reqMsg)⌝ ∗
        ∃ lst : List (w64 × PEntry), ghostVar γn.last (1 : Qp).half lst) ∨
      shutLb γn))

/-- The last insertion `lst`, if its entry is not in `P` any more, was deleted (no later entry
under its key). -/
def lastOk (lst : List (w64 × PEntry)) (P : GMap w64 PEntry) : Prop :=
  ∀ s e, (s, e) ∈ lst → P !! s = some e ∨ P !! s = none

/-- The ghost state of the pending map while the reader runs. -/
def pendAlive (γn : ClientNames) (m : GMap w64 Loc) (sd : Bool) : IProp GF :=
  iprop(∃ (P : GMap w64 PEntry) (lst : List (w64 × PEntry)),
    ghostMapAuth γn.pend (1 : Qp).half P ∗ ghostVar γn.last (1 : Qp).half lst ∗
    ⌜lastOk lst P ∧ (sd = false → ∀ s, P !! s ≠ none → m !! s ≠ none)⌝ ∗
    [∗map] s ↦ pc ∈ m, ∃ e : PEntry, ⌜P !! s = some e ∧ e.1 = pc⌝ ∗
      ghostMapElem γn.pend s (DFrac.own (1 : Qp).half) e ∗ callRes e)

/-- The invariant of `c.mu` (see the file header). -/
def muInv (γn : ClientNames) (c : Loc) : IProp GF :=
  iprop(∃ (sq : w64) (mp : Loc) (m : GMap w64 Loc) (sd cls : Bool),
    structFieldRef Client go!"seq" c ↦ sq ∗ structFieldRef Client go!"pending" c ↦ mp ∗
    mp ↦$ m ∗ structFieldRef Client go!"shutdown" c ↦ sd ∗
    structFieldRef Client go!"closing" c ↦ cls ∗
    monoListAuthOwn γn.sdl 1 (if sd then [()] else []) ∗
    (pendAlive γn m sd ∨ (token γn.dead ∗ ⌜m = ∅ ∧ sd = true⌝)))

/-- `c` is an rpc client of address `a` in world `W` (persistent). -/
def isClientN (c : Loc) (W : RpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64)
    (γn : ClientNames) : IProp GF :=
  iprop(structFieldRef Client go!"conn" c ↦□ cv ∗ connIface cv cid false ∗
    isRpcConn W a cid γn.conn ∗
    sync.isMutex (structFieldRef Client go!"sending" c) (sendInv γn cid W a) ∗
    sync.isMutex (structFieldRef Client go!"mu" c) (muInv γn c) ∗
    inv cliN (cliInv γn))

/-- `c` is an rpc client of address `a` in world `W` (persistent). -/
def isClient (c : Loc) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ (cv : GoInterface) (cid : w64) (γn : ClientNames), isClientN c W a cv cid γn)

/-- The reader's resources (`input`): its token, having read `connectedBytes` and the frames
of its consumed answers `C` (each with its persistent answer). -/
def readerOwn (γn : ClientNames) (cid : w64) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ (C : List Ans) (Lr : List RpcReq),
    recvTok cid false (respProto W a) (connectedBytes ++ framesOf (C.map (respMsg Lr))) ∗
    monoListAuthOwn γn.cons (1 : Qp).half C ∗ token γn.dead ∗ monoListLbOwn γn.conn.reqs Lr ∗
    ([∗list] y ∈ C, ghostMapElem γn.conn.ans y.1 .discard (some y.2)) ∗
    ⌜(∀ y ∈ C, y.1 < Lr.length) ∧ (C.map Prod.fst).Nodup ∧
      ∀ q ∈ C.map (respMsg Lr), q.length < 2 ^ 63⌝)

instance regElem_persistent_c (W : RpcWorld GF) (cid : w64) (γ : RpcConnNames) :
    Persistent (regElem (GF := GF) W cid γ) := by
  unfold regElem; infer_instance

instance isRpcConn_persistent_c (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) :
    Persistent (isRpcConn (GF := GF) W a cid γ) := by
  unfold isRpcConn regElem; infer_instance

instance isClientN_persistent (c : Loc) (W : RpcWorld GF) (a : GoString) (cv : GoInterface)
    (cid : w64) (γn : ClientNames) : Persistent (isClientN (GF := GF) c W a cv cid γn) := by
  unfold isClientN; infer_instance

instance isClient_persistent (c : Loc) (W : RpcWorld GF) (a : GoString) :
    Persistent (isClient (GF := GF) c W a) := by
  unfold isClient; infer_instance

instance shutLb_persistent (γn : ClientNames) : Persistent (shutLb (GF := GF) γn) := by
  unfold shutLb; infer_instance

/-! ## Specs -/

/-- `getCodec()`: a hypothesis here, stated as `Codec.lean`'s `getCodec.spec` (named apart so
that both files can be imported together; `getCodec.wp_proof` proves it). -/
abbrev getCodec.clientSpec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) }}
    (App (Val (@! net.rpc.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecFns (GF := GF) c }}

/-- `c.Close()`: closes the connection (a second `Close` returns `ErrShutdown`); an error comes
with its `Error()`. -/
abbrev Client.Close.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isClient c W a }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∨ errAny err }}

/-- `c.Call(sm, args, reply)` (`notes/craq-net.md`, "rpc specs"): `nil` after one run of the
method at the server on the encoded arguments, with its answer `Φ rep ""` and the reply decoded
into `reply` (`Θ rep true`); `ServerError(msg)` for a non-empty `msg` after one run, with its
answer `Φ rep msg` and the decoding resource `D` back; or another error, which is not a
`ServerError`, after at most one run (the deposit is lost), with `D` back or a failed
decoding, or, when the client is already shut down (nothing was encoded), the encoding premise
and `D` back. Every error comes with its `Error()` and the fact that its type implements
`error` (`errMsg` for a `ServerError`; `errAny` for the others, whose message may be
arbitrary: the `net` model's `*OpError`). -/
abbrev Client.Call.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a sm svc M : GoString) (S : MethodSpec GF)
    (args reply : GoInterface) (Φ : List w8 → GoString → IProp GF) (Rargs D : IProp GF)
    (Θ : List w8 → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗ kitCodecOk ∗
      isClient c W a ∗ ⌜splitSM sm = some (svc, M) ∧ W.SS a svc = some S⌝ ∗
      RpcCodec.enc args (fun bs => iprop(S M bs Φ ∗ Rargs)) ∗ D ∗
      □ (D -∗ ∀ rep, RpcCodec.dec rep reply (Θ rep)) }}
    (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #sm)) (Val #args)) (Val #reply))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ Rargs ∗ ∃ rep, Φ rep [] ∗ Θ rep true) ∨
      (∃ msg : GoString, ⌜msg ≠ [] ∧ err = serverErr msg⌝ ∗ errMsg err msg ∗ Rargs ∗
        (∃ rep, Φ rep msg) ∗ D) ∨
      (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ errAny err ∗
        ((Rargs ∗ (D ∨ ∃ rep, Θ rep false)) ∨
          (RpcCodec.enc args (fun bs => iprop(S M bs Φ ∗ Rargs)) ∗ D))) }}

/-- `c.input()`, the reader goroutine. -/
abbrev Client.input.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64)
    (γn : ClientNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isClientN c W a cv cid γn ∗
      readerOwn γn cid W a }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"input")) (Val #()))
  {{ RET #(); True }}

/-- `newClient(conn)` on the dialer's end of a registered connection whose head is written and
read. -/
abbrev newClient.spec : Prop :=
  ∀ (W : RpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64) (γ : RpcConnNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ connIface cv cid false ∗
      isRpcConn W a cid γ ∗ monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗
      sendTok cid false (reqProto W a) rpcHead ∗ recvTok cid false (respProto W a) connectedBytes }}
    (App (Val (@! net.rpc.newClient)) (Val #cv))
  {{ (c : Loc), RET #c; isClient c W a }}

/-- `DialHTTPPath("tcp", a, rpcPath)` on an rpc address: a client, or an error (with its
`Error()`). -/
abbrev DialHTTPPath.spec : Prop :=
  ∀ (W : RpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcAddr W a }}
    (App (App (App (Val (@! net.rpc.DialHTTPPath)) (Val #(go!"tcp"))) (Val #a)) (Val #rpcPath))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ errAny err) }}

/-- `DialHTTP("tcp", a)` on an rpc address: a client, or an error (with its `Error()`). -/
abbrev DialHTTP.spec : Prop :=
  ∀ (W : RpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ rpcAddr W a }}
    (App (App (Val (@! net.rpc.DialHTTP)) (Val #(go!"tcp"))) (Val #a))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ errAny err) }}

end defs

end net.rpc

end Perennial
