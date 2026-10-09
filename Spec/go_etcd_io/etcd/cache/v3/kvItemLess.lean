/-
`kvItemLess(a, b)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `kvItemLess(a, b)` is `a.key < b.key`, i.e. `kvLess`. -/
abbrev kvItemLess.spec : Prop :=
  ∀ (a b : Loc) (ea eb : KvEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ kvItemIs a ea ∗ kvItemIs b eb }}
    (App (App (Val (@! kvItemLess)) (Val #a)) (Val #b))
  {{ RET #(decide (kvLess ea eb)); True }}

end spec

end EtcdGrove
end Perennial
