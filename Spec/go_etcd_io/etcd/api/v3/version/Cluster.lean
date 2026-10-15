/-
`version.Cluster(v)` (`api/v3/version`): names-only (the server's `start` logs it). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `version.Cluster(v)` returns some string (names-only: the major and minor of `v`). -/
abbrev version.Cluster.spec : Prop :=
  ∀ (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version }}
    (App (Val (@! go_etcd_io.etcd.api.v3.version.Cluster)) (Val #v))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
