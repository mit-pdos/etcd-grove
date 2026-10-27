/-
**The transport and its peers' shared definitions** (rafthttp stage 6; D39). Lean-first.
* `trFixed`: the transport's fields after `Start`, read-only (its logger, id, URLs, cluster id,
  `Raft`, `ErrorC`, round trippers, dial-retry rate, stats), the network's stream registry, the
  registration of every member's hosts (`pipeReg`), `RaftStreamPrefix`'s value and (stage 6d) that
  the transport's member is one of the network's (`Rh.member`, a request's sender): what the
  peers, remotes and handlers read.
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
public import Spec.github_com.xiang90.probing.NewProber

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

/-- **A method-set premise** (as `ErrorStringLeaf`; stage 6c): `*peer` implements `Pausable` (it
has `Pause` and `Resume`, `peer.go`): what `CutPeer`'s and `MendPeer`'s `p.(Pausable)` reads.
`methodSet` is uninterpreted in the model, so the results that reach it take it as a premise. -/
class PeerPausable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  pausable : go.typeSetContains (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer.ty)
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Pausable.ty = true

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The transport `t`'s probers** (persistent; what `Stop` reads, `Start`'s). -/
def trProbers (t : Loc) : IProp GF :=
  iprop(∃ pp sp : GoInterface,
    t.[rafthttp.Transport, go!"pipelineProber"] ↦□ pp ∗ probing.proberOk pp ∗
    t.[rafthttp.Transport, go!"streamProber"] ↦□ sp ∗ probing.proberOk sp)

instance trProbers_persistent (t : Loc) : Persistent (trProbers (GF := GF) t) := by
  unfold trProbers; infer_instance

/-- **The transport `t`'s fixed fields** (persistent) of the member `lid`, whose `Raft` calls
borrow an `R`: see the file header. -/
def trFixed (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) : IProp GF :=
  iprop(∃ (lg ls ss : Loc) (urls : GoSlice) (uvs : List net.url.URL)
      (cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (r : GoInterface) (ec : GoChan)
      (srt prt : GoInterface) (drf : w64) (pp sp : GoInterface),
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
    t.[rafthttp.Transport, go!"pipelineProber"] ↦□ pp ∗
    t.[rafthttp.Transport, go!"streamProber"] ↦□ sp ∗
    streamRegInv Rh ∗ (□ ∀ pid : w64, ⌜Rh.member pid ∧ pid ≠ lid⌝ -∗ pipeReg Rh pid) ∗
    globalAddr rafthttp.RaftStreamPrefix ↦□ go!"/raft/stream" ∗ ⌜Rh.member lid⌝)

set_option synthInstance.maxHeartbeats 8000000 in
set_option synthInstance.maxSize 65536 in
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


/-- **A message for the peer `pid` of the member `lid`** (what `peer.send` takes; stage 6b): read-only,
marshalable, for `pid`, not a snapshot, without responses, with its bundle; a `MsgApp` of raft's
shape from `lid` (what the msgappv2 stream encodes: `V2EncOk`); its encoding below `2^50` bytes
(`swMsgBound`: `swMsgBound_phys`, the user's choice in stage 6d). -/
def peerMsg (Rh : RaftHttp GF) (lid pid : w64) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn ml DFrac.discard st ∗ □ Rh.γn.N.P st ∗ Rh.γn.N.O st ∗
    ⌜MsgMarshals st ∧ st.msg.To' = pid ∧ st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧
      (st.msg.Type' = MsgApp → AppShape st ∧ st.msg.From' = lid) ∧ swMsgBound ml⌝)

/-- **A started remote `g` of `pid` at the member `lid`** (persistent; `startRemote`'s): its logger,
ids, status and started pipeline (never restarted: a remote is never paused, `CutPeer`'s premise). -/
def remoteOk (Rh : RaftHttp GF) (lid pid : w64) (R : IProp GF) (g : Loc) : IProp GF :=
  iprop(∃ (lg ps pl : Loc),
    g.[rafthttp.remote, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    g.[rafthttp.remote, go!"localID"] ↦□ lid ∗ g.[rafthttp.remote, go!"id"] ↦□ pid ∗
    g.[rafthttp.remote, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    g.[rafthttp.remote, go!"pipeline"] ↦□ pl ∗ pipeHandleOk Rh pl pid R)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance remoteOk_persistent (Rh : RaftHttp GF) (lid pid : w64) (R : IProp GF) (g : Loc) :
    Persistent (remoteOk Rh lid pid R g) := by
  unfold remoteOk; infer_instance

/-- **The right to stop the remote `g`** (exclusive, once: its pipeline's). -/
def remoteStop (Rh : RaftHttp GF) (pid : w64) (R : IProp GF) (g : Loc) : IProp GF :=
  iprop(∃ pl : Loc, g.[rafthttp.remote, go!"pipeline"] ↦□ pl ∗ pipeStarted Rh pl pid R)

/-- **A message the member `lid` sends** (what `Transport.Send` takes; stage 6c): `peerMsg`'s but
for its recipient, `Send`'s routing (by `To`). -/
def sendMsg (Rh : RaftHttp GF) (lid : w64) (ml : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn ml DFrac.discard st ∗ □ Rh.γn.N.P st ∗ Rh.γn.N.O st ∗
    ⌜MsgMarshals st ∧ st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧
      (st.msg.Type' = MsgApp → AppShape st ∧ st.msg.From' = lid) ∧ swMsgBound ml⌝)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary: no raft message's encoding reaches `2^50` bytes** (2026-10-24, rafthttp
stage 6d, the user's choice): the encoding of a read-only message is below `2^50` bytes (a
petabyte; `swMsgBound`), a physical fact, like `netProcSlots`: no machine holds a message that
large. The stream writer sums the sizes of up to 2049 messages into an `int` it adds to a
prometheus counter, whose `Add` panics on a negative value; the sum stays below `2^62`. (Stage 6's
choice (3), a panicking `Add` the writer's goroutine may reach, is not provable: Perennial's
`wp_fork` asks a goroutine not to panic.) Not derivable in the logic, which can allocate a slice of
any `w64` length: `pbEnc_ok` bounds the encoding by `2^63` only (an `int`, Go's semantics). -/
axiom swMsgBound_phys (ml : Loc) (st : MsgSt) :
    msgOwn (GF := GF) ml DFrac.discard st ⊢ ⌜swMsgBound ml⌝

/-- **A message in the network's bundle is one the transport's `Send` takes** (stage 6d): the
bundle's facts (`netBundle`), and its encoding's bound (`swMsgBound_phys`). -/
theorem sendMsg_of_netBundle (Rh : RaftHttp GF) (lid : w64) (ml : Loc) :
    netBundle Rh.γn.N lid ml ⊢ sendMsg Rh lid ml := by
  iintro Hb
  iunfold netBundle at Hb
  icases Hb with ⟨%st, #Hm, #HP, HO, %H⟩
  ihave %Hbd := swMsgBound_phys ml st $$ Hm
  iunfold sendMsg
  iexists st
  iframe; iframe #
  ipureintro
  exact ⟨H.2.1, H.1, H.2.1, H.2.2, Hbd⟩

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

/-- A peer's message is the pipeline's. -/
theorem pipeMsg_of_peerMsg (Rh : RaftHttp GF) (lid pid : w64) (ml : Loc) :
    peerMsg Rh lid pid ml ⊢ pipeMsg Rh pid ml := by
  iintro Hpm
  iunfold peerMsg at Hpm
  icases Hpm with ⟨%st, Hm, #HP, HO, %H⟩
  iunfold pipeMsg
  iexists st
  iframe; iframe #
  ipureintro; exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩

/-- A peer's message is the message stream's. -/
theorem swMsg_message_of_peerMsg (Rh : RaftHttp GF) (lid pid : w64) (ml : Loc) :
    peerMsg Rh lid pid ml ⊢ swMsg Rh .message lid pid ml := by
  iintro Hpm
  iunfold peerMsg at Hpm
  icases Hpm with ⟨%st, Hm, #HP, HO, %H⟩
  iunfold swMsg
  iexists st
  iframe; iframe #
  ipureintro
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, fun h => absurd h (by decide), H.2.2.2.2.2⟩

/-- A peer's `MsgApp` (its type known of the message's state) is the msgappv2 stream's. -/
theorem swMsg_v2_of_peerMsg (Rh : RaftHttp GF) (lid pid : w64) (ml : Loc) (st : MsgSt)
    (Hm : MsgMarshals st ∧ st.msg.To' = pid ∧ st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧
      (st.msg.Type' = MsgApp → AppShape st ∧ st.msg.From' = lid) ∧ swMsgBound ml)
    (hty : st.msg.Type' = MsgApp) :
    ⊢ msgOwn ml DFrac.discard st -∗ □ Rh.γn.N.P st -∗ Rh.γn.N.O st -∗
      swMsg Rh .msgAppV2 lid pid ml := by
  iintro Hm' #HP HO
  iunfold swMsg
  iexists st
  iframe; iframe #
  ipureintro
  obtain ⟨hmar, hto, hns, hrs, happ, hb⟩ := Hm
  obtain ⟨hsh, hfr⟩ := happ hty
  exact ⟨hmar, hto, hns, hrs, fun _ => ⟨hmar, Or.inr ⟨hty, hsh, hfr, hto⟩⟩, hb⟩

end lemmas

end EtcdGrove
end Perennial
