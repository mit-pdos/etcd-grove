/-
`membership.StoreClusterVersionKey`: the trust boundary (`membership`'s `StoreClusterVersionKey`
is names-only; returns `apply.storeClusterVersionKey`, `go!"/0/version"`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `membership.StoreClusterVersionKey()` returns `apply.storeClusterVersionKey` (`"/0/version"`). -/
abbrev membership.StoreClusterVersionKey.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership }}
    (App (Val (@! membership.StoreClusterVersionKey)) (Val #()))
  {{ RET #(apply.storeClusterVersionKey); True }}

end spec

end EtcdGrove
end Perennial
