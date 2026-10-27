/-
`rp.String()` (`client/v3/retry.go`, a value receiver; unit P3a). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk backoffOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `rp.String()` returns some string (`"repeatable"`, `"nonRepeatable"` or `"UNKNOWN"`). -/
abbrev retryPolicy.String.spec : Prop :=
  ∀ (rp : go_etcd_io.etcd.client.v3.retryPolicy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val #(methods go_etcd_io.etcd.client.v3.retryPolicy.ty go!"String" #rp)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
