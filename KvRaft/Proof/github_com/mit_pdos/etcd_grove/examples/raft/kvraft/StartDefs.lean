/-
# kvraft's start resource: what `StartNode` starts a generation from (2026-11-22)

`notes/kvraft-part.md`, "`StartNode` and the crash frame". `StartNode.spec`/`Run.spec`/`RunNode.spec` are
stated at an abstract start resource `S id dir opts M` (ledger 2026-11-22, kvraft's `StartNode`); this is
the one `StartNode`'s proof instantiates it with, `kvNodeStart γ vs dir0 id dir opts M`:

* the generation's boot (`kvStart`, `BootLemmas.lean`: the file invariant allocated with its crash
  token, the writer's half, the file's handle, raft's armed vacancy);
* the cluster's allocation facts the start needs (kvdurable's `isClusterC`'s: a duplicating cluster, no
  bootstrap log, untraced, no snapshot directories, no data bound, at most `2^32` replicas, `readyFits`, the storage invariant)
  and the globals the transport and the replica read;
* the options: what raft's `RestartNode` takes of them (`kvOptsOk`), the voters `1..opts.Voters` the
  bootstrap configuration `StartNode` builds (`vs`);
* every other replica's address protocol in the address map `M` (`newTransport`'s premise).

`kvStp γ vs dir` (2026-11-24, G5: `notes/kvraft-g5-stop.md`) is the node's incarnation stopper at the
store (`NodeDefs.lean`'s `stp`): the replica's stopper (`repStopper`: `Replica.stop` gives `kvStart`
back), the transport's `stop` (`ptStop`), and the persistent rest of `kvNodeStart`, so that
`stopIncarnation` gives `kvNodeStart` back.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.StartLemmas
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Facts
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **The options raft's `RestartNode` takes** (kvdurable's `kdOptsOk`, without its replica bound): at
least one voter, in-flight messages positive and within `RestartNode`'s `2^62`, and a size limit set.
(`ValidCluster` checks `MaxInflightMsgs < 2^62` too.) -/
def kvOptsOk (o : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Options) : Prop :=
  1 ≤ uint.Z o.Voters' ∧ uint.Z o.Voters' < 2 ^ 32 ∧
  0 < sint.Z o.MaxInflightMsgs' ∧ sint.Z o.MaxInflightMsgs' < 2 ^ 62 ∧
  (o.MaxCommittedSizePerReady' ≠ W64 0 ∨ o.MaxSizePerMsg' ≠ W64 0)

/-- **The cluster's facts a start needs** (persistent; kvdurable's `isClusterC`'s, without the cluster
object): see the file header. -/
def kvStartGlobals (γ : KdNames) : IProp GF :=
  iprop(⌜γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧ Cluster.trace γ.r.cluster = none ∧
      γ.r.cluster.snapLoc = (fun _ => none) ∧ γ.r.cluster.maxData = none ∧ γ.max < 2 ^ 32⌝ ∗
    readyFits γ.r.cluster kdRaftN ∗ kdStorInv ∗ context.isClosedchanInit ∗
    (∃ et : GoInterface, globalAddr net.errTimeout ↦□ et) ∗
    (∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed))

instance kvStartGlobals_persistent (γ : KdNames) : Persistent (kvStartGlobals (GF := GF) γ) := by
  unfold kvStartGlobals; infer_instance

/-- **The other replicas' addresses** (persistent): every address of `M` but `id`'s is valid and has the
protocols of its replica (`newTransport`'s premise). -/
def kvPeerAddrs (γ : KdNames) (id : w64) (M : GMap w64 GoString) : IProp GF :=
  iprop(□ (∀ (pid : w64) (a : GoString), ⌜M !! pid = some a ∧ pid ≠ id⌝ -∗
    addrProto a (kvP (kvFacts γ (fun _ => True)) pid) (kvQ (kvFacts γ (fun _ => True)) pid) ∗
    ⌜addrOk a = true⌝))

instance kvPeerAddrs_persistent (γ : KdNames) (id : w64) (M : GMap w64 GoString) :
    Persistent (kvPeerAddrs (GF := GF) γ id M) := by
  unfold kvPeerAddrs; infer_instance

/-- **What `StartNode` starts replica `id` from** (see the file header): `StartNode.spec`'s `S`, at the
store's names `γ`, the bootstrap voters `vs` and the replicas' directory `dir0` (the store's seam
`kvRep γ vs dir0` names it: the configuration's directory is it). -/
def kvNodeStart (γ : KdNames) (vs : List w64) (dir0 : GoString) (id : w64) (dir : GoString)
    (opts : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Options) (M : GMap w64 GoString) :
    IProp GF :=
  iprop(⌜dir = dir0⌝ ∗ ∃ (fl : KdFileNames) (qc : Qp), kvStart γ vs dir id fl qc ∗ kvStartGlobals γ ∗
    kvPeerAddrs γ id M ∗
    ⌜kvOptsOk opts ∧ vs = raft_kvreconf.bootVoters (uint.nat opts.Voters')⌝)

/-- **The node's incarnation stopper at the store** (see the file header). -/
def kvStp (γ : KdNames) (vs : List w64) (dir : GoString) : NodeStopper GF :=
  fun cfg M r tv => iprop(repStopper γ vs dir cfg.ID' r ∗ ptStop tv ∗ ⌜cfg.Dir' = dir⌝ ∗
    kvStartGlobals γ ∗ kvPeerAddrs γ cfg.ID' M ∗
    ⌜kvOptsOk cfg.Opts' ∧ vs = raft_kvreconf.bootVoters (uint.nat cfg.Opts'.Voters')⌝)

end defs

end kvraft
end EtcdGrove
end Perennial
