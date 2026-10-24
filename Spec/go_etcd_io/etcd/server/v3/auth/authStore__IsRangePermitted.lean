/-
`authStore.IsRangePermitted` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
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

/-- `as.IsRangePermitted(authInfo, key, rangeEnd)`: `isOpPermitted` of the caller's user and revision
(the key's length below `2^63 - 1`: `NewBytesAffinePoint`'s `make`), with the mode's verdict on
a read of the range `[key, rangeEnd)` (`permVerdict`; the auth plan's S3). -/

abbrev auth.authStore.IsRangePermitted.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (a : Loc) (info : AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗ authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsRangePermitted")) (Val #a)) (Val #key)) (Val #re))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ authErrIs err ∗
      permVerdict M info k e .read err }}

end spec

end EtcdGrove
end Perennial
