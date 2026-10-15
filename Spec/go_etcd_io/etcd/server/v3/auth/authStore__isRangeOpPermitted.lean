/-
`(*authStore).isRangeOpPermitted` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.isRangeOpPermitted(user, key, rangeEnd, permtyp)` (read-locks `rangePermCacheMu`): some boolean; the slices kept. -/

abbrev auth.authStore.isRangeOpPermitted.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (user : GoString) (key re : GoSlice) (k e : List w8) (dk de : DFrac)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R ∗ cacheRd st ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isRangeOpPermitted")) (Val #user)) (Val #key)) (Val #re)) (Val #pt))
  {{ (b : Bool), RET #b; cacheRd st ∗ key ↦*{dk} k ∗ re ↦*{de} e }}

end spec

end EtcdGrove
end Perennial
