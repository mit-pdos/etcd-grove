/-
`authStore.isOpPermitted` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.isOpPermitted(user, rev, key, rangeEnd, permtyp)`: `nil` or one of the package's errors; the slices and the reader resource kept. -/

abbrev auth.authStore.isOpPermitted.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (user : GoString) (rev : w64) (key re : GoSlice) (k e : List w8)
    (dk de : DFrac) (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ authRd st R M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜permTypOk pt⌝ ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"isOpPermitted")) (Val #user)) (Val #rev)) (Val #key)) (Val #re))
      (Val #pt))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ authErrIs err }}

end spec

end EtcdGrove
end Perennial
