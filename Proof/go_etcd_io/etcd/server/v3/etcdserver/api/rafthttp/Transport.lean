/-
**The transport and its peers' shared definitions** (rafthttp stage 6; D34). Lean-first.
* `trFixed`: the transport's fields after `Start`, read-only (its logger, id, URLs, cluster id,
  `Raft`, `ErrorC`, round trippers, dial-retry rate, stats), the network's stream registry, the
  registration of every member's hosts (`pipeReg`) and `RaftStreamPrefix`'s value: what the peers,
  remotes and handlers read.
* `peerOk` (persistent): a started peer of `pid` (`startPeer`'s): its fields, its status, picker,
  stream writers, pipeline, snapshot sender, stream readers, receive channels and lock (`paused`);
  `peerStop`, the right to stop it once.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Snapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Peer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Handle
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ReaderRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PeerStatus

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

/-- **The transport `t`'s fixed fields** (persistent) of the member `lid`, whose `Raft` calls
borrow an `R`: see the file header. -/
def trFixed (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) : IProp GF :=
  iprop(∃ (lg ls ss : Loc) (urls : GoSlice) (uvs : List net.url.URL)
      (cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (r : GoInterface) (ec : GoChan)
      (srt prt : GoInterface) (drf : w64),
    t.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    t.[rafthttp.Transport, go!"ID"] ↦□ lid ∗
    t.[rafthttp.Transport, go!"URLs"] ↦□ urls ∗ urls ↦*□ uvs ∗
    t.[rafthttp.Transport, go!"ClusterID"] ↦□ cid ∗
    t.[rafthttp.Transport, go!"Raft"] ↦□ r ∗ netRaftOk Rh.γn lid γd R r ∗
    t.[rafthttp.Transport, go!"ErrorC"] ↦□ ec ∗
    t.[rafthttp.Transport, go!"streamRt"] ↦□ srt ∗ http.roundTripperOk (raftHttpNet Rh) srt ∗
    t.[rafthttp.Transport, go!"pipelineRt"] ↦□ prt ∗ http.roundTripperOk (raftHttpNet Rh) prt ∗
    t.[rafthttp.Transport, go!"DialRetryFrequency"] ↦□ drf ∗
    t.[rafthttp.Transport, go!"LeaderStats"] ↦□ ls ∗ ⌜ls ≠ null⌝ ∗
    t.[rafthttp.Transport, go!"ServerStats"] ↦□ ss ∗ ⌜ss ≠ null⌝ ∗
    streamRegInv Rh ∗ (□ ∀ pid : w64, pipeReg Rh pid) ∗
    globalAddr rafthttp.RaftStreamPrefix ↦□ go!"/raft/stream")

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance trFixed_persistent (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) :
    Persistent (trFixed Rh t lid γd R) := by
  unfold trFixed; infer_instance

/-- What the peer `p`'s mutex guards: `paused`. -/
def peerLockInv (p : Loc) : IProp GF :=
  iprop(∃ b : Bool, p.[rafthttp.peer, go!"paused"] ↦ b)

/-- **A started peer `p` of `pid` at the member `lid`** (persistent): see the file header. -/
def peerOk (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF) (p : Loc) : IProp GF :=
  iprop(∃ (lg ps pk cw2 cw1 pl ss cr2 cr1 : Loc) (r : GoInterface) (rc pc : GoChan),
    p.[rafthttp.peer, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    p.[rafthttp.peer, go!"localID"] ↦□ lid ∗ p.[rafthttp.peer, go!"id"] ↦□ pid ∗
    p.[rafthttp.peer, go!"r"] ↦□ r ∗ netRaftOk Rh.γn lid γd R r ∗
    p.[rafthttp.peer, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    p.[rafthttp.peer, go!"picker"] ↦□ pk ∗ pickerOk pk (peerURL Rh pid) ∗
    p.[rafthttp.peer, go!"msgAppV2Writer"] ↦□ cw2 ∗ swFixed Rh .msgAppV2 lid pid R cw2 ∗
    p.[rafthttp.peer, go!"writer"] ↦□ cw1 ∗ swFixed Rh .message lid pid R cw1 ∗
    p.[rafthttp.peer, go!"pipeline"] ↦□ pl ∗ pipeHandleOk Rh pl pid R ∗
    p.[rafthttp.peer, go!"snapSender"] ↦□ ss ∗ snapSenderOk Rh pid ss ∗
    p.[rafthttp.peer, go!"msgAppV2Reader"] ↦□ cr2 ∗ srFixed Rh lid pid γd cr2 ∗ srStopRight cr2 ∗
    p.[rafthttp.peer, go!"msgAppReader"] ↦□ cr1 ∗ srFixed Rh lid pid γd cr1 ∗ srStopRight cr1 ∗
    p.[rafthttp.peer, go!"recvc"] ↦□ rc ∗ p.[rafthttp.peer, go!"propc"] ↦□ pc ∗
    sync.isMutex (p.[rafthttp.peer, go!"mu"]) (peerLockInv p))

set_option synthInstance.maxHeartbeats 4000000 in
set_option synthInstance.maxSize 32768 in
instance peerOk_persistent (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF)
    (p : Loc) : Persistent (peerOk Rh lid pid γd R p) := by
  unfold peerOk; infer_instance

/-- **The right to stop the peer `p`** (exclusive, once: `stop` closes `stopc` and stops its
writers, pipeline and snapshot sender). -/
def peerStop (Rh : RaftHttp GF) (pid : w64) (R : IProp GF) (p : Loc) : IProp GF :=
  iprop(∃ (cw2 cw1 pl ss : Loc) (sc : GoChan) (γs : ChanNames) (cf : GoFunc)
      (γc : context.ContextNames),
    p.[rafthttp.peer, go!"stopc"] ↦□ sc ∗ ownBroadcastChan sc γs iprop(True) .Pending ∗
    p.[rafthttp.peer, go!"cancel"] ↦□ cf ∗ context.cancelSpec cf γc iprop(True) ∗
    p.[rafthttp.peer, go!"msgAppV2Writer"] ↦□ cw2 ∗ swStopRight cw2 ∗
    p.[rafthttp.peer, go!"writer"] ↦□ cw1 ∗ swStopRight cw1 ∗
    p.[rafthttp.peer, go!"pipeline"] ↦□ pl ∗ pipeStarted Rh pl pid R ∗
    p.[rafthttp.peer, go!"snapSender"] ↦□ ss ∗ snapSenderStop ss)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A started peer's stream writers (what the stream handler's `Get` gives). -/
theorem peerStreams_of_peerOk (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF)
    (p : Loc) : peerOk Rh lid pid γd R p ⊢ peerStreams Rh lid pid p := by
  iintro #H
  iunfold peerOk at H
  icases H with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rc, %pc, #Hlg, %Hlgnn, -, -, -,
    -, -, -, -, -, #Hw2, #Hf2, #Hw1, #Hf1, -⟩
  iunfold peerStreams
  iexists lg, cw2, cw1, R, R
  iframe #
  ipureintro; exact Hlgnn

end lemmas

end EtcdGrove
end Perennial
