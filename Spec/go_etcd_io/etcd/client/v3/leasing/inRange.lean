/-
`inRange(k, begin, end)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`inRange(k, begin, end)`**: `leaseInRange` (with `strings.Compare`). -/
abbrev inRange.spec : Prop :=
  ∀ (k b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.inRange)) (Val #k)) (Val #b)) (Val #e))
  {{ RET #(leaseInRange k b e); True }}

end spec

end leasing
end EtcdGrove
end Perennial
