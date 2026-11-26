/-
`RunNode(id, addrs, dir, voters, preVote, checkQuorum, stepDownOnRemoval, maxSizePerMsg,
maxCommittedSizePerReady, maxInflightMsgs)` (`examples/raft/kvraft/node.go`): a replica's process,
as the top-level theorem runs it: the cluster's addresses split (`SplitAddrs`) and checked
(`runNodeOk`: `ValidCluster`, `id` among the replicas, `dir` shorter than `MaxDirLen`; else it returns
at once), the address map built (replica `i` at the `i`-th address), then `Run`. Every configuration
is allowed: the resources `Run` needs, the protocols of `id`'s address (`Run`'s, whose seams `rep`,
`cf` are passed through) and the start resources `S` (at the id, the directory, the options built and
every address map holding exactly the addresses: `addrMapOk`), are needed only if the check passes.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.NodeDefs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev RunNode.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (id : w64) (addrs dir : GoString) (voters : w64) (pv cq sd : Bool)
    (msz mcs mif : w64) (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      (⌜runNodeOk (splitAddrs addrs) (uint.nat id) dir (uint.nat voters) (uint.nat msz)
          (uint.nat mcs) (uint.nat mif)⌝ -∗
        (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
          addrProto a (kvP F id) (kvQ F id)) ∗
        (∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗
          S id dir ⟨voters, pv, cq, sd, msz, mcs, mif⟩ M)) ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit }}
    (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RunNode)) (Val #id))
      (Val #addrs)) (Val #dir)) (Val #voters)) (Val #pv)) (Val #cq)) (Val #sd))
      (Val #msz)) (Val #mcs)) (Val #mif))
  {{ RET #(); True }}

end spec

end kvraft
end EtcdGrove
end Perennial
