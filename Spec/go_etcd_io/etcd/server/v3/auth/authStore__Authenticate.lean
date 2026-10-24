/-
`authStore.Authenticate` (`server/auth/store.go`). Lean-first (no Rocq counterpart); the auth
plan's S5 (2026-10-24; `notes/decisions.md`, "S5 of the auth plan").
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

/-- `as.Authenticate(ctx, username, password)`, in the apply thread (the admin side's authority
`hs` and write resource, as the admin requests, S4): `ErrAuthNotEnabled` with auth disabled; else
the user read from the backend (`GetUser`: the latest state's), `ErrAuthFailed` if absent or a
no-password user; else a token from the provider's `assign` for the user (its error, or a response
holding a token issued to the user: `authenticated`). -/
abbrev auth.authStore.Authenticate.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (ctx : GoInterface) (username password : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      enabledRd st M ∗ authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post }}
    (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Authenticate"))
      (Val #ctx)) (Val #username)) (Val #password))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ enabledRd st M ∗
      authOwn M hs ∗ authWR st M P f T ∗ authenticated M hs username resp err }}

end spec

end EtcdGrove
end Perennial
