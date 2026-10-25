/-
`kv.GetStream(ctx, key, opts...)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart); see `InvOrdering.lean`.
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

/-- `kv.GetStream(ctx, key, opts...)`: not supported by `kvOrdering`; returns a nil channel and
`status.Error(codes.Unimplemented, "GetStream is not supported by kvOrdering")`. -/
abbrev kvOrdering.GetStream.spec : Prop :=
  ∀ (kvp : Loc) (ctx : GoInterfaceOk) (key : GoString) (sl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering }}
    (App (App (App (Val (kvp @!! go.GoType.PointerType kvOrdering.ty @!! go!"GetStream"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
  {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err); ⌜ch = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end ordering
end EtcdGrove
end Perennial
