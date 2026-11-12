/-
`getMergedPerms` (`server/auth/range_perm_cache.go`). Lean-first (no Rocq counterpart); see
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

/-- `getMergedPerms(tx, userName)`, `tx` an `UnsafeAuthReader` holding the state `st`
(`authReaderOk`): `nil` when the state has no such user; else a new `unifiedRangePermissions`
(`permsAt`, read-only) whose read tree holds the intervals of the user's permissions granting
reads and whose write tree those granting writes (`cacheEntryIs`: a missing role contributes
nothing, a permission of an unknown type nothing); the user's permissions fit the trees'
counts (`permsFit`). -/
abbrev auth.getMergedPerms.spec : Prop :=
  ∀ (ti : GoInterfaceOk) (Hs : auth.AuthState → IProp GF) (st : auth.AuthState) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authReaderOk ti Hs ∗
      Hs st ∗ ⌜permsFit st⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.getMergedPerms)) (Val #(GoInterface.ok ti)))
      (Val #name))
  {{ (p : Loc), RET #p; Hs st ∗
      (⌜p = null ∧ st.users !! name = none⌝ ∨
        ∃ Lr Lw, permsAt p Lr Lw ∗ ⌜cacheEntryIs st name Lr Lw⌝) }}

end spec

end EtcdGrove
end Perennial
