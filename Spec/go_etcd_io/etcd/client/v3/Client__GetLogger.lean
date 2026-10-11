/-
`clientv3.Client.GetLogger()` (`client/v3/client.go`, translated for `client/v3/concurrency`). Lean-first (no
Rocq counterpart); see `InvClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `client.GetLogger()` (`c.lg.Load()`): some non-nil logger. -/
abbrev Client.GetLogger.spec : Prop :=
  ∀ (cl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClientLogger cl }}
    (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"GetLogger")) (Val #()))
  {{ (lg : Loc), RET #lg; ⌜lg ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
