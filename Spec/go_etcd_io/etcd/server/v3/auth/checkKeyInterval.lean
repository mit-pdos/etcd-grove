/-
`checkKeyInterval` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `checkKeyInterval(lg, p, key, rangeEnd, permtyp)`: the tree of the permission type queried with the interval (its slices kept); `permtyp` `READ` or `WRITE`. -/

abbrev auth.checkKeyInterval.spec : Prop :=
  ∀ (lg p : Loc) (key re : GoSlice) (k e : List w8) (dk de : DFrac) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ permsOk p ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyInterval)) (Val #lg))
      (Val #p)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e }}

end spec

end EtcdGrove
end Perennial
