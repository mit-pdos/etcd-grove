/- Lean-first (no Rocq counterpart).

`(*transfers).take()` (cluster.go), 2026-10-13: under the lock, one of the `MsgTimeoutNow`
the transport may still pass on is used up, if one is left. With the transfer budget
(`isTransfers`): `true` with one tick credit of the term budget (what `Node.Step` takes with
a `MsgTimeoutNow`), or `false`.
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
abbrev transfers.take.spec : Prop :=
  ∀ (bud : BudgetNames) (tr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
      isTransfers bud tr }}
    (App (Val (tr @!! go.GoType.PointerType rTransfersTy @!! go!"take")) (Val #()))
  {{ (b : Bool), RET #b; if b then tickCred bud 1 else True }}

end spec

end register
end EtcdGrove
end Perennial
