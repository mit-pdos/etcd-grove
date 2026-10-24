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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    ownBroadcastChan sc γs iprop(True) .Unknown ∗ pipeReg Rh pid ∗ ⌜Rh.member lid ∧ lid ≠ pid⌝)

set_option synthInstance.maxHeartbeats 8000000 in
set_option synthInstance.maxSize 65536 in
instance snapSenderOk_persistent (Rh : RaftHttp GF) (pid : w64) (s : Loc) :
    Persistent (snapSenderOk Rh pid s) := by
  unfold snapSenderOk; infer_instance

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

/-- **The right to stop the snapshot sender `s`** (exclusive, once: `stop` closes its `stopc`). -/
def snapSenderStop (s : Loc) : IProp GF :=
  iprop(∃ (sc : GoChan) (γs : ChanNames), s.[rafthttp.snapshotSender, go!"stopc"] ↦□ sc ∗
    ownBroadcastChan sc γs iprop(True) .Pending)

end defs

end EtcdGrove
end Perennial
