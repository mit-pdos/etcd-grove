/-
`r.read(seq, key, timeout)` (`examples/raft/kvnet/replica.go`): a linearizable read of `key` at
the replica `r` of id `id`, by a read index whose context the client minted (`F.readOk id seq key`,
what a `ReqRead` frame carries); with `ok`, the value `v` with the protocol's answer fact
(`F.ansRead id seq key v`). **A spec at the store's seam** `rep` (as `Replica.propose`'s).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

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

/-- See the file header. -/
abbrev Replica.read.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) : Prop :=
  ∀ (r : Loc) (id seq : w64) (key : GoString) (tmo : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ □ rep r id ∗ F.readOk id seq key }}
    (App (App (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica.ty @!! go!"read")) (Val #seq))
      (Val #key)) (Val #tmo))
  {{ (v : GoString) (ok : Bool), RET (PairV #v #ok);
      if ok then F.ansRead id seq key v else iprop(True) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
