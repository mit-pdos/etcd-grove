/-
# kvnet's start resource: what `StartNode` starts a generation from (2026-11-22)

`notes/kvnet-part.md`, "`StartNode` and the crash frame". `StartNode.spec`/`Run.spec`/`RunNode.spec` are
stated at an abstract start resource `S id dir opts M` (ledger 2026-11-22, kvnet's `StartNode`); this is
the one `StartNode`'s proof instantiates it with, `kvNodeStart γ vs id dir opts M`:

* the generation's boot (`kvStart`, `BootLemmas.lean`: the file invariant allocated with its crash
  token, the writer's half, the file's handle, raft's armed vacancy);
* the cluster's allocation facts the start needs (kvdurable's `isClusterC`'s: a duplicating cluster, no
  bootstrap log, untraced, no snapshot directories, no data bound, `readyFits`, the storage invariant)
  and the globals the transport and the replica read;
* the options: what raft's `RestartNode` takes of them (`kvOptsOk`), the voters `1..opts.Voters` the
  bootstrap configuration `StartNode` builds (`vs`);
* every other replica's address protocol in the address map `M` (`newTransport`'s premise).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartLemmas
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Facts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **The options raft's `RestartNode` takes** (kvdurable's `kdOptsOk`, without its replica bound): at
least one voter, in-flight messages positive and within `RestartNode`'s `2^62`, and a size limit set.
(`ValidCluster` checks only `MaxInflightMsgs < 2^63`: the top-level statement's premise gives the rest.) -/
def kvOptsOk (o : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options) : Prop :=
  1 ≤ uint.Z o.Voters' ∧ uint.Z o.Voters' < 2 ^ 32 ∧
  0 < sint.Z o.MaxInflightMsgs' ∧ sint.Z o.MaxInflightMsgs' < 2 ^ 62 ∧
  (o.MaxCommittedSizePerReady' ≠ W64 0 ∨ o.MaxSizePerMsg' ≠ W64 0)

/-- **The cluster's facts a start needs** (persistent; kvdurable's `isClusterC`'s, without the cluster
object): see the file header. -/
def kvStartGlobals (γ : KdNames) : IProp GF :=
  iprop(⌜γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧ Cluster.trace γ.r.cluster = none ∧
      γ.r.cluster.snapLoc = (fun _ => none) ∧ γ.r.cluster.maxData = none⌝ ∗
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

/-- **What `StartNode` starts replica `id` from** (see the file header): `StartNode.spec`'s `S`, at the
store's names `γ` and the bootstrap voters `vs`. -/
def kvNodeStart (γ : KdNames) (vs : List w64) (id : w64) (dir : GoString)
    (opts : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options) (M : GMap w64 GoString) :
    IProp GF :=
  iprop(∃ (fl : KdFileNames) (qc : Qp), kvStart γ vs dir id fl qc ∗ kvStartGlobals γ ∗
    kvPeerAddrs γ id M ∗
    ⌜kvOptsOk opts ∧ vs = raft_kvreconf.bootVoters (uint.nat opts.Voters')⌝)

end defs

end raft_kvnet
end EtcdGrove
end Perennial
