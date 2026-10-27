/-
**The pipeline's sending side** (rafthttp stage 4d): what `pipeline.post` reads of its pipeline and
transport (`pipeSenderOk`), the peer's URLs (`peerURL`), and the errors `checkPostResponse`
returns (`postErr`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Picker

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

/-- A URL of only a scheme `http`, a host and a path (what `url.URL.String` is specified for:
`http.URLString_spec`), its host one `url.Parse` accepts (`http.urlHostOk`, what `NewRequest`
needs; stage 4e). -/
def urlPlain (u : net.url.URL) : Prop :=
  u.Scheme' = go!"http" ∧ u.Opaque' = "" ∧ u.User' = null ∧ u.Fragment' = "" ∧
    u.RawQuery' = "" ∧ u.RawPath' = "" ∧ u.RawFragment' = "" ∧ u.ForceQuery' = false ∧
    u.OmitHost' = false ∧ http.urlHostOk u.Host'

/-- **A URL of the peer `to`**: plain, its host owned by `to`. -/
def peerURL (Rh : RaftHttp GF) (to : w64) (u : net.url.URL) : Prop :=
  urlPlain u ∧ Rh.owner u.Host' = to

/-- **The peer `to`'s hosts are served with the raft protocol** (persistent; stage 4e): each
host the network's owner map gives to `to` has `raftProto Rh` registered (`http.httpProtoAt`), what
`RoundTrip` needs of a request's host. -/
def pipeReg (Rh : RaftHttp GF) (to : w64) : IProp GF :=
  iprop(□ ∀ host : GoString, ⌜Rh.owner host = to⌝ -∗ http.httpProtoAt host (raftProto Rh))

instance pipeReg_persistent (Rh : RaftHttp GF) (to : w64) : Persistent (pipeReg Rh to) := by
  unfold pipeReg; infer_instance

instance ownBroadcastChan_unknown_persistent (ch : GoChan) (γ : ChanNames) (Q : IProp GF) :
    Persistent (ownBroadcastChan ch γ Q .Unknown) := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef; infer_instance

/-- **What `post` reads** (persistent) of the pipeline `p` to the peer `to`: its transport's
logger, URLs, id, cluster id and pipeline round tripper (of the raft network), its picker (of the
peer's URLs), its stop channel (only closed), the peer's hosts' registration (`pipeReg`). -/
def pipeSenderOk (Rh : RaftHttp GF) (p : Loc) (to : w64) : IProp GF :=
  iprop(∃ (tr pk : Loc) (sc ec : GoChan) (γs : ChanNames) (lg : Loc) (urls : GoSlice)
      (uvs : List net.url.URL) (lid cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (rt : GoInterface),
    p.[rafthttp.pipeline, go!"tr"] ↦□ tr ∗ p.[rafthttp.pipeline, go!"picker"] ↦□ pk ∗
    p.[rafthttp.pipeline, go!"stopc"] ↦□ sc ∗ p.[rafthttp.pipeline, go!"errorc"] ↦□ ec ∗
    p.[rafthttp.pipeline, go!"peerID"] ↦□ to ∗
    tr.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    tr.[rafthttp.Transport, go!"URLs"] ↦□ urls ∗ urls ↦*□ uvs ∗
    tr.[rafthttp.Transport, go!"ID"] ↦□ lid ∗ tr.[rafthttp.Transport, go!"ClusterID"] ↦□ cid ∗
    tr.[rafthttp.Transport, go!"pipelineRt"] ↦□ rt ∗ http.roundTripperOk (raftHttpNet Rh) rt ∗
    pickerOk pk (peerURL Rh to) ∗ ownBroadcastChan sc γs iprop(True) .Unknown ∗ pipeReg Rh to ∗
    ⌜Rh.member lid ∧ lid ≠ to⌝ ∗ ⌜trURLsOk Rh lid uvs⌝)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance pipeSenderOk_persistent (Rh : RaftHttp GF) (p : Loc) (to : w64) :
    Persistent (pipeSenderOk Rh p to) := by
  unfold pipeSenderOk; infer_instance

/-- **What `checkPostResponse` returns** for the status `st` (persistent): `nil`;
`errMemberRemoved` for a `403`; or another leaf pointer error, not `errMemberRemoved`'s; in each
case an error whose `Error()` returns (`http.errStrOk`). -/
def postErr (st : w64) (err : GoInterface) : IProp GF :=
  iprop(http.errStrOk err ∗ (⌜err = GoInterface.nil⌝ ∨
    (⌜st = W64 403⌝ ∗ globalAddr rafthttp.errMemberRemoved ↦□ err) ∨
    ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e ∧ errLeaf e⌝ ∗
      □ (∀ eR : GoInterface, globalAddr rafthttp.errMemberRemoved ↦□ eR -∗ ⌜err ≠ eR⌝)))

instance postErr_persistent (st : w64) (err : GoInterface) : Persistent (postErr (GF := GF) st err) := by
  unfold postErr; infer_instance

end defs

end EtcdGrove
end Perennial
