/-
`checkKeyPoint` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
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

/-- `checkKeyPoint(lg, p, key, permtyp)`: the tree of the permission type queried with the point `key` (its slice kept); `permtyp` `READ` or `WRITE` (otherwise `lg.Panic`). -/

abbrev auth.checkKeyPoint.spec : Prop :=
  ∀ (lg p : Loc) (key : GoSlice) (k : List w8) (dk : DFrac) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ permsOk p ∗ key ↦*{dk} k ∗ ⌜permTypOk pt⌝ ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyPoint)) (Val #lg)) (Val #p))
      (Val #key)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k }}

end spec

end EtcdGrove
end Perennial
