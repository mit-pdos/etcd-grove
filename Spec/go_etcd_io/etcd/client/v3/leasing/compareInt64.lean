/-
`compareInt64(a, b)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`compareInt64(a, b)`**: `-1`, `0` or `1` (`compareInt64M`). -/
abbrev compareInt64.spec : Prop :=
  ∀ (a b : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.compareInt64)) (Val #a)) (Val #b))
  {{ RET #(compareInt64M a b); True }}

end spec

end leasing
end EtcdGrove
end Perennial
