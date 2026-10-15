/-
`exceedsRequestLimit(ai, ci, r, enable)` (`util.go`): the request limit. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `exceedsRequestLimit(ai, ci, r, enable)`: `exceedsLimit` (`InvProposer.lean`), the priority
being a lease revocation. -/
abbrev exceedsRequestLimit.spec : Prop :=
  ∀ (ai ci : w64) (p : Loc) (rq : apply.IRRModel) (enable : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ irrNoHdrIs p rq }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.exceedsRequestLimit))
      (Val #ai)) (Val #ci)) (Val #p)) (Val #enable))
  {{ RET #(exceedsLimit ai ci rq.leaseRevoke.isSome enable); True }}

end spec

end EtcdGrove
end Perennial
