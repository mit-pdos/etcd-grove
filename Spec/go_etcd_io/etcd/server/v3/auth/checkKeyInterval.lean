/-
`checkKeyInterval` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (unit P2; the auth plan's S2, 2026-10-23).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `checkKeyInterval(lg, p, key, rangeEnd, permtyp)`: the tree of the permission type (`READ`
the read tree, `WRITE` the write tree; otherwise `lg.Panic`) queried with `[key, rangeEnd)`
(`rangeEnd` `nil` when open-ended, `queryIvl`; `Contains`): `adt.containsT` of the query on that
tree, for every query; the slices kept. -/
abbrev auth.checkKeyInterval.spec : Prop :=
  ∀ (lg p : Loc) (Tr Tw : adt.RbT adt.Entry) (key re : GoSlice) (k e : GoString) (dk de : DFrac)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ permsAt p Tr Tw ∗
      key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.checkKeyInterval)) (Val #lg))
      (Val #p)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜b = adt.containsT (queryIvl k e) (if pt = W32 0 then Tr else Tw)⌝ }}

end spec

end EtcdGrove
end Perennial
