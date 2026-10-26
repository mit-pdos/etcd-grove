/-
`authStore.RoleList` (`server/auth/store.go`): the latest state's roles (the auth plan's E2j,
2026-10-26). Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/Reads.lean`
(the replies) and `InvAuth.lean` (the backend's reads, `authBackendReads`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Reads

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.RoleList(r)`**, with the admin side's authority at `hs`: the backend's `GetAllRoles` (its
batch transaction: the lock runs the hook, `Post`) and the latest state's roles' names
(`roleListOut`); the authority and the write resource kept. -/
abbrev auth.authStore.RoleList.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleList")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); Post ∗ authOwn M hs ∗
      authWR st M P f T ∗ ∃ sta : AuthState, ⌜histLast M hs sta⌝ ∗ roleListOut sta resp err }}

end spec

end EtcdGrove
end Perennial
