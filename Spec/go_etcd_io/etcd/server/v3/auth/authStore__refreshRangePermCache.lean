/-
`(*authStore).refreshRangePermCache` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.refreshRangePermCache(tx)`, `tx` an `UnsafeAuthReader` holding the state `sta` of the mode
(`authReaderOk`, `authSnap`): write-locks `rangePermCacheMu` and replaces the cache's map with one
built from the transaction's users (`UnsafeGetAllUsers`, `getMergedPerms` for each): the new map is
`cacheOk` of `sta` (its keys `sta`'s users, each entry the user's permissions); the token kept. -/
abbrev auth.authStore.refreshRangePermCache.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (ti : GoInterfaceOk)
    (Hs : auth.AuthState → IProp GF) (sta : auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authReaderOk ti Hs ∗ Hs sta ∗ authSnap M sta ∗ ⌜permsFit sta⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"refreshRangePermCache"))
      (Val #(GoInterface.ok ti)))
  {{ RET #(); Hs sta }}

end spec

end EtcdGrove
end Perennial
