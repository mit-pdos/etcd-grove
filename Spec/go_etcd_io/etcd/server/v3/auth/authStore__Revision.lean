/-
`authStore.Revision` (`server/auth/store.go`). Lean-first (no Rocq counterpart); see
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.Revision()` (loads the atomic): the mode's verdict on the value (`revisionVerdict`: in
`on γa` a recorded state's revision; the auth plan's S3); with the admin side's authority `hs`
(`hsO = some hs`; S4), the latest state's revision exactly. -/
abbrev auth.authStore.Revision.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hsO : Option (List auth.AuthState)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwnOpt M hsO }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Revision")) (Val #()))
  {{ (x : w64), RET #x; authOwnOpt M hsO ∗ revisionVerdict M x ∗
      ⌜∀ (hs : List auth.AuthState) (stl : auth.AuthState), hsO = some hs → histLast M hs stl →
        M.isOn = true → M ≠ .any → uint.nat x = stl.revision⌝ }}

end spec

end EtcdGrove
end Perennial
