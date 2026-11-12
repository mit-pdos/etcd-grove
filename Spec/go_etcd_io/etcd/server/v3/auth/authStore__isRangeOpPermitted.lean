/-
`(*authStore).isRangeOpPermitted` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.isRangeOpPermitted(user, key, rangeEnd, permtyp)` (read-locks `rangePermCacheMu`): the
user's cache entry queried with the point `key` (`rangeEnd` empty) or the interval; no entry, `false`.
The verdict in the mode (`cacheVerdict`); the slices kept. -/
abbrev auth.authStore.isRangeOpPermitted.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (user : GoString) (key re : GoSlice)
    (k e : GoString) (dk de : DFrac) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      cacheRd st M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isRangeOpPermitted"))
      (Val #user)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; cacheRd st M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      cacheVerdict M user k e pt b }}

end spec

end EtcdGrove
end Perennial
