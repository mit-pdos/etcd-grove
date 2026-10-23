/-
**The pipeline's goroutines** (`pipeline.handle`, `start`, `stop`; rafthttp stage 4d): what a
message on the pipeline's `msgc` carries (`pipeMsg`), what `handle` reads of its pipeline
(`pipeHandleOk`), what `start` needs (`pipeFixed`) and what it gives (`pipeStarted`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Sender
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A message for the pipeline to the peer `to`**: read-only, marshalable, for `to`, not a
snapshot (which goes by `snapshotSender`) and without responses, with its persistent part and
its one-shot part (`N.P`, `N.O`: what the network delivers with it). -/
def pipeMsg (Rh : RaftHttp GF) (to : w64) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn ml DFrac.discard st ∗ □ Rh.γn.N.P st ∗ Rh.γn.N.O st ∗
    ⌜MsgMarshals st ∧ st.msg.To' = to ∧ st.msg.Type' ≠ MsgSnap ∧ st.resps = []⌝)

/-- **What `handle` reads** (persistent) of the pipeline `p` to the peer `to`: what `post` reads,
its peer status, its follower stats (`nil` or not), its `Raft` (whose calls take one of the
resources `R`), and its message channel (a bag of `pipeMsg`s). -/
def pipeHandleOk (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF) : IProp GF :=
  iprop(pipeSenderOk Rh p to ∗
    ∃ (ps fs : Loc) (r : GoInterface) (id : w64) (γd : GName) (mc : Loc) (γm : ChanNames),
    p.[rafthttp.pipeline, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    p.[rafthttp.pipeline, go!"followerStats"] ↦□ fs ∗
    p.[rafthttp.pipeline, go!"raft"] ↦□ r ∗ netRaftOk Rh.γn id γd R r ∗
    p.[rafthttp.pipeline, go!"msgc"] ↦□ mc ∗ isChanBag γm mc (pipeMsg Rh to))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance pipeHandleOk_persistent (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF) :
    Persistent (pipeHandleOk Rh p to R) := by
  unfold pipeHandleOk; infer_instance

/-- **A pipeline's fixed fields** (persistent; what `start` needs besides its channels and wait
group): `pipeSenderOk`'s and `pipeHandleOk`'s but the stop and message channels. -/
def pipeFixed (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF) : IProp GF :=
  iprop(∃ (tr pk : Loc) (ec : GoChan) (lg : Loc) (urls : GoSlice) (uvs : List net.url.URL)
      (lid cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (rt : GoInterface) (ps fs : Loc)
      (r : GoInterface) (id : w64) (γd : GName),
    p.[rafthttp.pipeline, go!"tr"] ↦□ tr ∗ p.[rafthttp.pipeline, go!"picker"] ↦□ pk ∗
    p.[rafthttp.pipeline, go!"errorc"] ↦□ ec ∗ p.[rafthttp.pipeline, go!"peerID"] ↦□ to ∗
    tr.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    tr.[rafthttp.Transport, go!"URLs"] ↦□ urls ∗ urls ↦*□ uvs ∗
    tr.[rafthttp.Transport, go!"ID"] ↦□ lid ∗ tr.[rafthttp.Transport, go!"ClusterID"] ↦□ cid ∗
    tr.[rafthttp.Transport, go!"pipelineRt"] ↦□ rt ∗ http.roundTripperOk (raftHttpNet Rh) rt ∗
    pickerOk pk (peerURL Rh to) ∗
    p.[rafthttp.pipeline, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    p.[rafthttp.pipeline, go!"followerStats"] ↦□ fs ∗
    p.[rafthttp.pipeline, go!"raft"] ↦□ r ∗ netRaftOk Rh.γn id γd R r ∗ pipeReg Rh to)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance pipeFixed_persistent (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF) :
    Persistent (pipeFixed Rh p to R) := by
  unfold pipeFixed; infer_instance

/-- **A started pipeline** (`start`'s postcondition; exclusive): its goroutines' facts (the
message channel a sender sends on), its stop channel not yet closed (`stop` closes it), and its
wait group's four `Done`s, each with one of the `Raft`'s resources `R` (`stop` collects them). -/
def pipeStarted (Rh : RaftHttp GF) (p : Loc) (to : w64) (R : IProp GF) : IProp GF :=
  iprop(pipeHandleOk Rh p to R ∗ ∃ (sc : GoChan) (γs : ChanNames),
    p.[rafthttp.pipeline, go!"stopc"] ↦□ sc ∗ ownBroadcastChan sc γs iprop(True) .Pending ∗
    sync.join.ownAdder (p.[rafthttp.pipeline, go!"wg"]) (W32 4) iprop(True ∗ R ∗ R ∗ R ∗ R))

end defs

end EtcdGrove
end Perennial
