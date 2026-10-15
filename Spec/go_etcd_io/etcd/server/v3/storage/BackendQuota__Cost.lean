/-
`storage.BackendQuota.Cost`: the trust boundary (`server/v3/storage` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `q.Cost(r)` on one of the three request types the appliers pass (it panics on any other)
returns some integer, whatever `*q` holds (it reads only the request: the capped applier's `q`
is a zero `BackendQuota`). -/
abbrev storage.BackendQuota.Cost.spec : Prop :=
  ∀ (q : Loc) (t : go.GoType) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ ⌜apply.quotaReqTy t⌝ }}
    (App (Val (q @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendQuota.ty
      @!! go!"Cost")) (Val #(interface.mkOk t #r)))
  {{ (c : w64), RET #c; True }}

end spec

end EtcdGrove
end Perennial
