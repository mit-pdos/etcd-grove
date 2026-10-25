/-
**The stream writer** (rafthttp stage 5b; `notes/rafthttp-plan.md`, D38d). Lean-first.

A `streamWriter` of type `ty` (msgappv2 or message) from the local member `lid` to the peer `pid`
has a long-running goroutine (`run`) that takes the connections the stream handler attaches
(`connc`, `outConnOk`: the handler's response writer, after a `200`, for a stream request of the
connection registered as `(γw, ty, pid)`) and encodes the messages queued on `msgc` (`swMsg`: a
message for `pid` with its bundle) into the attached one. Each message's one-shot part is
deposited as the frame's (`stream_deposit`) before it is encoded, so the bytes written stay a
stream's (`streamSent`, the response protocol). On a failure or a new connection the old one is
closed, which gives its response writer back to the handler (`closeRight`: the handler must not
use it after it returns, nor the writer after the close), and `msgc` is replaced: the queued
messages are dropped (a loss).

`working`, `closer` and `msgc` are guarded by `mu` (`swLockInv`), written only by `run`, which
holds the other half of each (`swRunOwn`) and reads `msgc` without the lock.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A stream type's value (`streamTypeMsgAppV2`, `streamTypeMessage`). -/
def StreamTy.str : StreamTy → GoString
  | .msgAppV2 => go!"msgappv2"
  | .message => go!"message"

/-- A message's encoding is below `2^50` bytes (see `swMsg`). -/
def swMsgBound (ml : Loc) : Prop := (pbEnc raftpb.Message.ty ml).length < 2 ^ 50

/-- **A message for the stream writer of type `ty` from `lid` to `pid`** (`msgc`'s): `pipeMsg`'s
(read-only, marshalable, for `pid`, not a snapshot, without responses, with its bundle), and for the
msgappv2 stream an `MsgApp` of raft's shape from `lid` to `pid` (`V2EncOk`: `peer.pick` sends only
those there); (stage 5b) its encoding below `2^50` bytes (`swMsgBound`: the writer sums the sizes
of up to 2049 messages into an `int` it adds to a counter, which must not be negative; for stage 6
to establish, or to replace by a physical bound). -/
def swMsg (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn ml DFrac.discard st ∗ □ Rh.γn.N.P st ∗ Rh.γn.N.O st ∗
    ⌜MsgMarshals st ∧ st.msg.To' = pid ∧ st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧
      (ty = .msgAppV2 → V2EncOk lid pid st) ∧ swMsgBound ml⌝)

/-- **The right to close `cl` once** (exclusive), giving it `Q`: its `Close()` returns some error. -/
def closeRight (cl : GoInterface) (Q : IProp GF) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜cl = GoInterface.ok ci⌝ ∗
    ∀ Φ : val → IProp GF, Q -∗ ▷ (∀ e : GoInterface, Φ #e) -∗
      WP (App (Val #(methods ci.ty go!"Close" ci.v)) (Val #())) {{ Φ }})

/-- What closing a connection gives back to its handler: its response writer, committed (2026-10-23,
stage 5e-2: the handler returns it so, `http.handlerDone`), at some status and bytes. -/
def connBack (Rh : RaftHttp GF) (wi : GoInterfaceOk) (a : GoString) (R : http.HReq) (γk : GName) :
    IProp GF :=
  iprop(∃ (st : w64) (w : List w8),
    http.respWriter (raftHttpNet Rh) (GoInterface.ok wi) a R γk (some st) w)

/-- **A connection attached to the stream writer of type `ty` from `lid` to `pid`** (`connc`'s,
`attachOutgoingConn`'s): its type, writer and flusher (the handler's response writer `wi`), closer
and ids, read-only; the response writer after a `200`, nothing written, of the stream request of a
connection registered as `(γw, ty, pid)` to the address `a` that `lid` owns; and the right to close
it, giving the writer back. -/
def outConnOk (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (conn : Loc) : IProp GF :=
  iprop(∃ (wi : GoInterfaceOk) (cl : GoInterface) (a : GoString) (R : http.HReq) (γk γw : GName),
    conn.[rafthttp.outgoingConn, go!"t"] ↦□ ty.str ∗
    conn.[rafthttp.outgoingConn, go!"Writer"] ↦□ GoInterface.ok wi ∗
    conn.[rafthttp.outgoingConn, go!"Flusher"] ↦□ GoInterface.ok wi ∗
    conn.[rafthttp.outgoingConn, go!"Closer"] ↦□ cl ∗
    conn.[rafthttp.outgoingConn, go!"localID"] ↦□ lid ∗
    conn.[rafthttp.outgoingConn, go!"peerID"] ↦□ pid ∗
    http.respWriter (raftHttpNet Rh) (GoInterface.ok wi) a R γk (some (W64 200)) [] ∗
    streamReg Rh γk (γw, ty, pid) ∗
    ⌜Rh.owner R.host = lid ∧ R.host = a ∧ R.path = streamPath ty pid⌝ ∗
    closeRight cl (connBack Rh wi a R γk))

/-- **The encoder `enc` of a stream of type `ty`** writing to `wi`, at the codec's state `s`
(exclusive): a `*msgAppV2Encoder` (`v2EncOwn`) or a `*messageEncoder` (its writer, read-only). -/
def encOwn (lid pid : w64) (fs : Loc) :
    (ty : StreamTy) → GoInterface → GoInterfaceOk → (ty.codec lid pid).S → IProp GF
  | .msgAppV2, enc, wi, s => iprop(∃ e : Loc,
      ⌜enc = interface.mkOk (go.GoType.PointerType rafthttp.msgAppV2Encoder.ty) #e⌝ ∗
      v2EncOwn e wi fs s)
  | .message, enc, wi, _ => iprop(∃ e : Loc,
      ⌜enc = interface.mkOk (go.GoType.PointerType rafthttp.messageEncoder.ty) #e⌝ ∗
      e.[rafthttp.messageEncoder, go!"w"] ↦□ GoInterface.ok wi)

/-- **The writer goroutine's live connection** (exclusive): its encoder `enc` and flusher `fl` on
the response writer `wi`, which has written the chain `fr` (each frame with its facts) of the
connection registered as `(γw, ty, pid)`; and the right to close `cl`. -/
def swLive (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (fs : Loc) (enc fl cl : GoInterface) :
    IProp GF :=
  iprop(∃ (wi : GoInterfaceOk) (a : GoString) (R : http.HReq) (γk γw : GName)
      (fr : List (MsgWire × List w8)) (s : (ty.codec lid pid).S),
    ⌜fl = GoInterface.ok wi⌝ ∗ encOwn lid pid fs ty enc wi s ∗
    http.respWriter (raftHttpNet Rh) (GoInterface.ok wi) a R γk (some (W64 200)) (chainBytes fr) ∗
    ⌜Chain (ty.codec lid pid) (ty.codec lid pid).init fr s⌝ ∗
    ([∗list] i ↦ f ∈ fr, frameDep Rh.γn.N γw pid i f.1) ∗
    streamReg Rh γk (γw, ty, pid) ∗
    ⌜Rh.owner R.host = lid ∧ R.host = a ∧ R.path = streamPath ty pid⌝ ∗
    closeRight cl (connBack Rh wi a R γk))

/-- **What `mu` guards** of the writer `cw`: half of `msgc` (with its bag), `working` and
`closer` each (`run` holds the other halves). -/
def swLockInv (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (cw : Loc) : IProp GF :=
  iprop(∃ (mc : GoChan) (γm : ChanNames) (wk : Bool) (cl : GoInterface),
    typedPointsto (cw.[rafthttp.streamWriter, go!"msgc"]) mc (DFrac.own (1 : Qp).half) ∗
    typedPointsto (cw.[rafthttp.streamWriter, go!"working"]) wk (DFrac.own (1 : Qp).half) ∗
    typedPointsto (cw.[rafthttp.streamWriter, go!"closer"]) cl (DFrac.own (1 : Qp).half) ∗
    isChanBag γm mc (swMsg Rh ty lid pid))

/-- **`run`'s halves** of the guarded fields, at `mc` (with its bag), `wk` and `cl`. -/
def swRunOwn (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (cw : Loc) (mc : GoChan)
    (wk : Bool) (cl : GoInterface) : IProp GF :=
  iprop(∃ γm : ChanNames,
    typedPointsto (cw.[rafthttp.streamWriter, go!"msgc"]) mc (DFrac.own (1 : Qp).half) ∗
    typedPointsto (cw.[rafthttp.streamWriter, go!"working"]) wk (DFrac.own (1 : Qp).half) ∗
    typedPointsto (cw.[rafthttp.streamWriter, go!"closer"]) cl (DFrac.own (1 : Qp).half) ∗
    isChanBag γm mc (swMsg Rh ty lid pid))

/-- **A stream writer's fixed fields** (persistent): its logger (not `nil`), ids, peer status,
follower stats (not `nil`: the msgappv2 encoder counts into it), `Raft` (whose calls take one of
the resources `Rr`), mutex, and channels: `connc` a bag of attached connections, `stopc` and
`done` broadcast channels (`stop` closes the one, `run` the other). -/
def swFixed (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (cw : Loc) :
    IProp GF :=
  iprop(∃ (lg ps fs : Loc) (r : GoInterface) (γd : GName) (cc sc dc : GoChan)
      (γc γs γdn : ChanNames),
    cw.[rafthttp.streamWriter, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    cw.[rafthttp.streamWriter, go!"localID"] ↦□ lid ∗
    cw.[rafthttp.streamWriter, go!"peerID"] ↦□ pid ∗
    cw.[rafthttp.streamWriter, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    cw.[rafthttp.streamWriter, go!"fs"] ↦□ fs ∗ ⌜fs ≠ null⌝ ∗
    cw.[rafthttp.streamWriter, go!"r"] ↦□ r ∗ netRaftOk Rh.γn lid γd Rr r ∗
    sync.isMutex (cw.[rafthttp.streamWriter, go!"mu"]) (swLockInv Rh ty lid pid cw) ∗
    cw.[rafthttp.streamWriter, go!"connc"] ↦□ cc ∗ isChanBag γc cc (outConnOk Rh ty lid pid) ∗
    cw.[rafthttp.streamWriter, go!"stopc"] ↦□ sc ∗ ownBroadcastChan sc γs iprop(True) .Unknown ∗
    cw.[rafthttp.streamWriter, go!"done"] ↦□ dc ∗ ownBroadcastChan dc γdn iprop(True) .Unknown)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance swFixed_persistent (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF)
    (cw : Loc) : Persistent (swFixed Rh ty lid pid Rr cw) := by
  unfold swFixed; infer_instance

/-- **The right to stop the writer `cw`** (exclusive, once): closing its stop channel. -/
def swStopRight (cw : Loc) : IProp GF :=
  iprop(∃ (sc : GoChan) (γs : ChanNames), cw.[rafthttp.streamWriter, go!"stopc"] ↦□ sc ∗
    ownBroadcastChan sc γs iprop(True) .Pending)

/-- **The right to close the writer `cw`'s `done`** (exclusive, `run`'s): once, when it returns. -/
def swDoneRight (cw : Loc) : IProp GF :=
  iprop(∃ (dc : GoChan) (γd : ChanNames), cw.[rafthttp.streamWriter, go!"done"] ↦□ dc ∗
    ownBroadcastChan dc γd iprop(True) .Pending)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A typed points-to is two halves (a Perennial gap: its example `etcd_session` proves it
locally; `notes/perennial-changes.md`). -/
theorem typedPointsto_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  have h := (typedPointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rwa [DFrac.op_own, Qp.half_add_half] at h

/-- Two halves of a typed points-to agree and make the whole. -/
theorem typedPointsto_combine_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v1 v2 : V) :
    typedPointsto (GF := GF) l v1 (DFrac.own (1 : Qp).half) ∗
      typedPointsto l v2 (DFrac.own (1 : Qp).half) ⊢ ⌜v1 = v2⌝ ∗ typedPointsto l v1 (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Heq
  subst Heq
  isplitr
  · ipureintro; rfl
  · iapply (typedPointsto_halves l v1).2
    isplitl [H1]
    · iexact H1
    · iexact H2

/-- **`run` takes `mu`**: its halves and the lock's make the guarded fields whole. -/
theorem swRunOwn_combine (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (cw : Loc)
    (mc : GoChan) (wk : Bool) (cl : GoInterface) :
    swRunOwn Rh ty lid pid cw mc wk cl ⊢ swLockInv Rh ty lid pid cw -∗
      ∃ γm : ChanNames, cw.[rafthttp.streamWriter, go!"msgc"] ↦ mc ∗
        cw.[rafthttp.streamWriter, go!"working"] ↦ wk ∗ cw.[rafthttp.streamWriter, go!"closer"] ↦ cl ∗
        isChanBag γm mc (swMsg Rh ty lid pid) := by
  iintro Hrun Hinv
  iunfold swRunOwn at Hrun
  icases Hrun with ⟨%γm, Hmc, Hwk, Hcl, #Hbag⟩
  iunfold swLockInv at Hinv
  icases Hinv with ⟨%mc0, %γm0, %wk0, %cl0, Hmc0, Hwk0, Hcl0, -⟩
  ihave ⟨%Hemc, Hmc⟩ := typedPointsto_combine_halves _ _ _ $$ [$Hmc $Hmc0]
  ihave ⟨%Hewk, Hwk⟩ := typedPointsto_combine_halves _ _ _ $$ [$Hwk $Hwk0]
  ihave ⟨%Hecl, Hcl⟩ := typedPointsto_combine_halves _ _ _ $$ [$Hcl $Hcl0]
  iexists γm
  iframe; iframe #

/-- **`run` releases `mu`**: the guarded fields whole make its halves and the lock's. -/
theorem swRunOwn_split (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (cw : Loc)
    (mc : GoChan) (γm : ChanNames) (wk : Bool) (cl : GoInterface) :
    cw.[rafthttp.streamWriter, go!"msgc"] ↦ mc ∗ cw.[rafthttp.streamWriter, go!"working"] ↦ wk ∗
      cw.[rafthttp.streamWriter, go!"closer"] ↦ cl ∗ isChanBag γm mc (swMsg Rh ty lid pid) ⊢
      swRunOwn Rh ty lid pid cw mc wk cl ∗ swLockInv Rh ty lid pid cw := by
  iintro ⟨Hmc, Hwk, Hcl, #Hbag⟩
  ihave ⟨Hmc, Hmc0⟩ := (typedPointsto_halves _ _).1 $$ Hmc
  ihave ⟨Hwk, Hwk0⟩ := (typedPointsto_halves _ _).1 $$ Hwk
  ihave ⟨Hcl, Hcl0⟩ := (typedPointsto_halves _ _).1 $$ Hcl
  isplitl [Hmc Hwk Hcl]
  · iunfold swRunOwn
    iexists γm
    iframe; iframe #
  · iunfold swLockInv
    iexists mc, γm, wk, cl
    iframe; iframe #

end lemmas

end EtcdGrove
end Perennial
