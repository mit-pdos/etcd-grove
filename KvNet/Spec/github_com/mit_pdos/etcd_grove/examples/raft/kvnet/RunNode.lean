/-
`RunNode(id, addrs, dir, voters, preVote, checkQuorum, stepDownOnRemoval, maxSizePerMsg,
maxCommittedSizePerReady, maxInflightMsgs)` (`examples/raft/kvnet/node.go`): a replica's process,
as the top-level theorem runs it: the cluster's addresses split (`SplitAddrs`), checked
(`ValidCluster`, and `id` one of the replicas: else a panic, which the premises exclude), the
address map built (replica `i` at the `i`-th address), then `Run`. The premises are the top-level
theorem's: a valid cluster, `id` among its replicas, and the protocols of `id`'s address (`Run`'s,
whose seams `rep`, `cf` are passed through, and whose start resources `S` are given at the id, the
directory, the options built and every address map holding exactly the addresses: `addrMapOk`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev RunNode.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (id : w64) (addrs dir : GoString) (voters : w64) (pv cq sd : Bool)
    (msz mcs mif : w64) (eof ed : GoInterface),
  validCluster (splitAddrs addrs) (uint.nat voters) (uint.nat msz) (uint.nat mcs) (uint.nat mif)
    = true →
  1 ≤ uint.nat id → uint.nat id ≤ (splitAddrs addrs).length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
        addrProto a (kvP F id) (kvQ F id)) ∗
      (∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗
        S id dir ⟨voters, pv, cq, sd, msz, mcs, mif⟩ M) ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit }}
    (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunNode)) (Val #id))
      (Val #addrs)) (Val #dir)) (Val #voters)) (Val #pv)) (Val #cq)) (Val #sd))
      (Val #msz)) (Val #mcs)) (Val #mif))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
