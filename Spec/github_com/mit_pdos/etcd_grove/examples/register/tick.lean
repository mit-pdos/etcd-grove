/- Lean-first (no Rocq counterpart).

`tick(nd)` (cluster.go): `ticksN` ticks of node `nd`, one tick credit each.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

/-- See the file header. -/
abbrev tick.spec : Prop :=
  ∀ (γn : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ isNode γn id n ∗ tickCred γn.bud ticksN }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.tick))
      (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n)))
  {{ RET #(); True }}

end spec

end register
end EtcdGrove
end Perennial
