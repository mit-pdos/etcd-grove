/-
`authStore.IsPutPermitted` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.IsPutPermitted(authInfo, ...)`: `isOpPermitted` of the caller's user and revision (the key's length below `2^63 - 1`: `NewBytesAffinePoint`'s `make`). -/

abbrev auth.authStore.IsPutPermitted.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (a : Loc) (info : AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8) (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsPutPermitted")) (Val #a)) (Val #key))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ authErrIs err }}

end spec

end EtcdGrove
end Perennial
