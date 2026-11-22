/-
`r.propose(op, timeout)` (`examples/raft/kvnet/replica.go`): the operation `d` (a minted one:
`F.opOk d`, what a `ReqPropose` frame carries) proposed at the replica `r` of id `id`; with `ok`, the
answer `v` with the protocol's answer fact (`F.ansOp d v`). **A spec at the store's seam**: `rep` is
the store's replica predicate (`NodeDefs.lean`); its proof is the store layer's (kvdurable's
`Replica.propose`, after decision B). `Node.handle`'s proof takes it as a callee.
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
abbrev Replica.propose.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF) : Prop :=
  ∀ (r : Loc) (id : w64) (opsl : GoSlice) (d : List w8) (dq : DFrac)
    (tmo : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ □ rep r id ∗ opsl ↦*{dq} d ∗ F.opOk d }}
    (App (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica.ty @!! go!"propose")) (Val #opsl))
      (Val #tmo))
  {{ (v : GoString) (ok : Bool), RET (PairV #v #ok);
      if ok then F.ansOp d v else iprop(True) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
