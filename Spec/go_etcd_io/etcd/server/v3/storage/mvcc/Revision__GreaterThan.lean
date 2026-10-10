/-
`Revision.GreaterThan` (`revision.go`). Lean-first (no Rocq counterpart); see `Model.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `a.GreaterThan(b)` decides `Rev.gt`: `(main, sub)` lexicographically. -/
abbrev mvcc.Revision.GreaterThan.spec : Prop :=
  ∀ (a b : Revision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (a @!! Revision.ty @!! go!"GreaterThan")) (Val #b))
  {{ RET #(mvcc.Rev.gt (mvcc.revOf a) (mvcc.revOf b)); True }}

end spec

end EtcdGrove
end Perennial
