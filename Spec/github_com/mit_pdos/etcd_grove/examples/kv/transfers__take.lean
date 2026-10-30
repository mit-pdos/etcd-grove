/- Lean-first (no Rocq counterpart).

`(*transfers).take()` (cluster.go), 2026-10-13: under the lock, one of the `MsgTimeoutNow`
the transport may still pass on is used up, if one is left (`true`), or none is (`false`).
Nothing more is promised (2026-10-30, stage F of the client repair: `Node.Step` takes a
`MsgTimeoutNow` with no tick credit since raft's credits are gone; until then `true` came with
one tick credit, `tickCredit`).
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
  ∀ (γ : Cluster) (tr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isTransfers γ tr }}
    (App (Val (tr @!! go.GoType.PointerType rTransfersTy @!! go!"take")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end kv
end EtcdGrove
end Perennial
