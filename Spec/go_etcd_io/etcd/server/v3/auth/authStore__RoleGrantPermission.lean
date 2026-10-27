/-
`authStore.RoleGrantPermission` (`server/auth/store.go`): the admin side (the auth plan's S4d,
2026-10-24). Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`
(the write side's contracts) and `Steps.lean` (the model's steps).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`authpb.Permission_Type_name` holds a map, read-only** (`RoleGrantPermission` looks the
granted type's name up for its log line): `authpb`'s fact gives it (`typeNamesOk_of_init`; until the
auth plan's S4e, 2026-10-24, a premise of the spec, the map literal untranslated). -/
def auth.typeNamesOk : IProp GF :=
  iprop(∃ (mp : Loc) (Mn : GMap w32 GoString),
    globalAddr authpb.Permission_Type_name ↦□ mp ∗ mp ↦$□ Mn)

instance auth.typeNamesOk_persistent : Persistent (auth.typeNamesOk (GF := GF)) := by
  unfold auth.typeNamesOk; infer_instance

/-- `authpb`'s fact (`authpbInit`) gives `typeNamesOk`. -/
theorem auth.typeNamesOk_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb ⊢ auth.typeNamesOk (GF := GF) := by
  iintro #Hp
  ihave Hi : (go_etcd_io.etcd.cache.v3.authpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hi with ⟨%mp, %Mn, #H1, #H2, -⟩
  unfold auth.typeNamesOk
  iexists mp, Mn
  iframe #

variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.RoleGrantPermission(r)`** for a request naming the role `name` (within bbolt's key
bound) and the wire permission `w` (or none): the step `roleGrantPermissionR name w`. -/
abbrev auth.authStore.RoleGrantPermission.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (r : Loc) (name : GoString) (w : Option PermW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      roleGrantPermissionReqIs r name w ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗
      authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post ∗
      ⌜stepOk M hs (roleGrantPermissionR name w)⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"RoleGrantPermission")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); (Post ∨ Pre) ∗ authWR st M P f T ∗
      respOk etcdserverpb.AuthRoleGrantPermissionResponse resp err ∗
      adminOut M hs (roleGrantPermissionR name w) noExtra err }}

end spec

end EtcdGrove
end Perennial
