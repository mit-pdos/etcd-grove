/-
`GetConfChange(b)` (`examples/raft/kvnet/client.go`): reads back what `PutConfChange` wrote, all of
`b`; with `ok`, a configuration change `c` of which `cf c pl` holds. **A spec at the store's seam**:
`cf` is what the change read back is (its content as `node.ProposeConfChange` takes it), fixed with
the proof of this spec (a pure model of `PutConfChange`'s bytes; not yet written).
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
abbrev GetConfChange.spec (cf : GoInterface → List w8 → IProp GF) : Prop :=
  ∀ (b : GoSlice) (pl : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ b ↦*{dq} pl }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.GetConfChange)) (Val #b))
  {{ (c : GoInterface) (ok : Bool), RET (PairV #c #ok); if ok then cf c pl else iprop(True) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
