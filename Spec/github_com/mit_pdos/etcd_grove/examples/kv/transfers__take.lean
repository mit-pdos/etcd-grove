/- Lean-first (no Rocq counterpart).

`(*transfers).take()` (cluster.go), 2026-10-13: under the lock, one of the `MsgTimeoutNow`
the transport may still pass on is used up, if one is left. With the transfer budget
(`isTransfers`): `true` with one tick credit of the term budget (what `Node.Step` takes with
a `MsgTimeoutNow`), or `false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [StorageModel GF]

/-- See the file header. -/
abbrev transfers.take.spec : Prop :=
  ∀ (γ : Draft.Cluster) (tr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isTransfers γ tr }}
    (App (Val (tr @!! go.GoType.PointerType rTransfersTy @!! go!"take")) (Val #()))
  {{ (b : Bool), RET #b; if b then Draft.tickCredit γ 1 else True }}

end spec

end kv
end EtcdGrove
end Perennial
