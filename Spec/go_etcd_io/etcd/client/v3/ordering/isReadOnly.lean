/-
`ordering.isReadOnly(op)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart); see `InvOrdering.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.InvOrdering

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI go_etcd_io.etcd.client.v3.ordering

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

/-- `ordering.isReadOnly(op)`: recursively checks whether `op` (represented by operation tree `t`)
is read-only (`isReadOnlyM t`), i.e., every leaf in `t` is an `OpGet` (`o.t = W64 1`). -/
abbrev isReadOnly.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (t : OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      opTAtC false opv t }}
    (App (Val (@! isReadOnly)) (Val #opv))
  {{ RET #(isReadOnlyM t); True }}

end spec

end ordering
end EtcdGrove
end Perennial
