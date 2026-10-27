/-
**The snapshot sender** (rafthttp stage 6b, opaque; defined 2026-10-24, stage 7d, D42).
`newSnapshotSender` gives a sender (`snapSenderOk`, persistent: what `send` and `post` read of the
sender and its transport, as `pipeSenderOk` is the pipeline's) and the right to stop it once
(`snapSenderStop`: `stop` closes its `stopc`). `send` is reached only through `peer.sendSnap`,
from `Transport.SendSnapshot`. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Sender
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Codec
public import Proof.errors.NewVarCell

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A snapshot sender `s` to the peer `pid`** (persistent; what `newSnapshotSender` returns): its
fields, read-only (the ids of its member `lid` and of `pid`, the cluster id, its transport, the
peer's picker and status, the member's `Raft`, the transport's error channel, its stop channel,
only closed), and of its transport the logger, URLs and pipeline round tripper (of the raft
network); the peer's hosts' registration (`pipeReg`), `pid` another member. -/
def snapSenderOk (Rh : RaftHttp GF) (pid : w64) (s : Loc) : IProp GF :=
  iprop(∃ (tr pk ps : Loc) (r : GoInterface) (ec sc : GoChan) (γs : ChanNames) (lg : Loc)
      (urls : GoSlice) (uvs : List net.url.URL) (lid cid : go_etcd_io.etcd.client.pkg.v3.types.ID)
      (rt : GoInterface) (γd : GName) (R : IProp GF),
    s.[rafthttp.snapshotSender, go!"from"] ↦□ lid ∗ s.[rafthttp.snapshotSender, go!"to"] ↦□ pid ∗
    s.[rafthttp.snapshotSender, go!"cid"] ↦□ cid ∗ s.[rafthttp.snapshotSender, go!"tr"] ↦□ tr ∗
    s.[rafthttp.snapshotSender, go!"picker"] ↦□ pk ∗
    s.[rafthttp.snapshotSender, go!"status"] ↦□ ps ∗ s.[rafthttp.snapshotSender, go!"r"] ↦□ r ∗
    s.[rafthttp.snapshotSender, go!"errorc"] ↦□ ec ∗
    s.[rafthttp.snapshotSender, go!"stopc"] ↦□ sc ∗
    tr.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    tr.[rafthttp.Transport, go!"URLs"] ↦□ urls ∗ urls ↦*□ uvs ∗
    tr.[rafthttp.Transport, go!"pipelineRt"] ↦□ rt ∗ http.roundTripperOk (raftHttpNet Rh) rt ∗
    pickerOk pk (peerURL Rh pid) ∗ peerStatusOk ps ∗ netRaftOk Rh.γn lid γd R r ∗
    ownBroadcastChan sc γs iprop(True) .Unknown ∗ pipeReg Rh pid ∗ ⌜Rh.member lid ∧ lid ≠ pid⌝ ∗
    ⌜trURLsOk Rh lid uvs⌝)

set_option synthInstance.maxHeartbeats 8000000 in
set_option synthInstance.maxSize 65536 in
instance snapSenderOk_persistent (Rh : RaftHttp GF) (pid : w64) (s : Loc) :
    Persistent (snapSenderOk Rh pid s) := by
  unfold snapSenderOk; infer_instance

/-- **A snapshot message for the peer `pid`** (D22 S-i's `netSnapBundle`, the message to `pid`): the
raft message `ml`, a `MsgSnap` of a snapshot `sn` to `pid`, read-only for good, with its bundle,
and the right to read the merged message's reader `rc`, whose complete streams are bbolt images
of some `D` with the payload's certificate at the snapshot's index. What `send` takes. -/
def snapBundleTo (N : NetPayload GF) (pid : w64) (ml : Loc) (rc : GoInterface) : IProp GF :=
  iprop(∃ (st : MsgSt) (sn : SnapshotM) (D : backend.Data), msgOwn ml DFrac.discard st ∗
    (□ N.P st) ∗ N.O st ∗
    ⌜st.msg.Type' = MsgSnap ∧ st.snap = some sn ∧ st.resps = [] ∧ st.msg.To' = pid⌝ ∗
    backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗
    □ N.img sn.Metadata'.Index' D)

/-- **The snapshot body's prefixes** (D42): comparable with the envelope's frame `msgFrame bs`. -/
def snapPre (bs : List w8) (x : List w8) : Prop := x <+: msgFrame bs ∨ msgFrame bs <+: x

/-- **The snapshot body's complete streams** (D42): the envelope's frame, then a complete stream of
the merged message's reader (in `Φ`). -/
def snapPhi (bs : List w8) (Φ : List w8 → Prop) (x : List w8) : Prop :=
  ∃ t, x = msgFrame bs ++ t ∧ Φ t

/-- **A reader whose `Close` returns** (persistent): from any goroutine, any number of times. -/
def rdCloseOk (ri : GoInterfaceOk) : IProp GF :=
  iprop(□ {{ (True : IProp GF) }}
      (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
    {{ (err : GoInterface), RET #err; True }})

instance rdCloseOk_persistent (ri : GoInterfaceOk) : Persistent (rdCloseOk (GF := GF) ri) := by
  unfold rdCloseOk; infer_instance

/-- **net/http's errors are not rafthttp's `errMemberRemoved`** (stage 7d, the user's choice): the
statement of `netErrNotRemoved_ok`'s trust boundary. `errMemberRemoved` is rafthttp's own
`errors.New` error, returned only by `checkPostResponse` and the stream's `dial`, never handed to
net/http (nor to the snapshot's pipe, whose writer closes with the backend's errors), so no error
net/http makes or wraps is it, or wraps it: `errors.Is` of one against it is `false`. -/
def netErrNotRemoved_spec : Prop :=
  ∀ (e eR : GoInterface),
    ⊢ {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ http.netErr e ∗
          globalAddr rafthttp.errMemberRemoved ↦□ eR }}
        (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #e)) (Val #eR))
      {{ RET #false; True }}

/-- **What the snapshot sender's `post` returns** (persistent; stage 7d): `nil`, an error of
net/http's (`netErr`), or a leaf pointer error other than `errMemberRemoved` (`errStopped`,
`checkPostResponse`'s); an error whose `Error()` returns. -/
def snapPostErr (err : GoInterface) : IProp GF :=
  iprop(http.errStrOk err ∗ (⌜err = GoInterface.nil⌝ ∨ http.netErr err ∨
    ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e ∧ errLeaf e⌝ ∗
      □ (∀ eR : GoInterface, globalAddr rafthttp.errMemberRemoved ↦□ eR -∗ ⌜err ≠ eR⌝)))

instance snapPostErr_persistent (err : GoInterface) : Persistent (snapPostErr (GF := GF) err) := by
  unfold snapPostErr; infer_instance

/-- A post's error (`postErr`) of a status other than `403` is a snapshot post's. -/
theorem snapPostErr_of_postErr (st : w64) (err : GoInterface) (h : st ≠ W64 403) :
    postErr (GF := GF) st err ⊢ snapPostErr err := by
  unfold postErr snapPostErr
  iintro ⟨#HS, (%Hn | ⟨%H403, -⟩ | #Hl)⟩
  · iframe #; ileft; ipureintro; exact Hn
  · exact absurd H403 h
  · iframe #

/-- **The right to stop the snapshot sender `s`** (exclusive, once: `stop` closes its `stopc`). -/
def snapSenderStop (s : Loc) : IProp GF :=
  iprop(∃ (sc : GoChan) (γs : ChanNames), s.[rafthttp.snapshotSender, go!"stopc"] ↦□ sc ∗
    ownBroadcastChan sc γs iprop(True) .Pending)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [ErrorStringLeaf]

/-- An `errors.New` error whose cell holds a message other than `errMemberRemoved`'s is a snapshot
post's leaf error (`snapPostErr`; as `checkPostResponse`'s `postErr_errorString`). -/
theorem snapPostErr_errorString (x xR : Loc) (m mR : GoString) (hm : m ≠ mR) :
    ⊢ (□ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }}) -∗
      errStrCell x m -∗
      globalAddr rafthttp.errMemberRemoved ↦□
        interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xR -∗
      errStrCell xR mR -∗
      snapPostErr (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #HM #Hc #Hg #HcR
  iunfold snapPostErr
  isplitr
  · iapply errorString_errStrOk $$ HM
  iright; iright
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; exact ⟨rfl, errorString_leaf x⟩
  imodintro
  iintro %eR #HeR
  icombine Hg HeR gives %Heq
  subst Heq
  ihave %Hne := errStrCell_ne x xR m mR hm $$ Hc HcR
  ipureintro
  intro he
  apply Hne
  injection he with h1
  injection h1 with _ hv
  exact go.intoVal_inj (V := Loc) hv

end lemmas

end EtcdGrove
end Perennial
