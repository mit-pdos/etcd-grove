/-
`etcdserverpb.Compare.GetTarget()` (`api/etcdserverpb/rpc.pb.go`, translated for `client/v3/leasing`'s
`evalCmp`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `c.GetTarget()` of a non-nil comparison: its `Target` field (read-only). -/
abbrev Compare.GetTarget.spec : Prop :=
  ∀ (p : Loc) (v : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.Compare go!"Target" p ↦□ v }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.Compare.ty @!! go!"GetTarget")) (Val #()))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
