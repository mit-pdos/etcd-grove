/-
`(clientv3.CompactOp).toRequest` (`client/v3/compact_op.go`).

Users: `kv.Compact`.

Proof sketch: a fresh request (`compactReqOwn_unfold`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/CompactOp__toRequest.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.toRequest()`: a fresh `CompactionRequest`. -/
def CompactOp.toRequest.spec : Prop :=
  ∀ (op : go_etcd_io.etcd.client.v3.CompactOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (op @!! go_etcd_io.etcd.client.v3.CompactOp.ty @!! go!"toRequest")) (Val #()))
  {{ (p : Loc), RET #p; compactReqOwn p (DFrac.own 1) (sint.Z op.revision') op.physical' }}

end spec

end ClientV3
end EtcdGrove
end Perennial
