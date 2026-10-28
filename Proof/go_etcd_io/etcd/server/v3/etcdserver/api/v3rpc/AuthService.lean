/-
**etcd's specs of the Auth service's admin methods** (the auth plan's E3za, 2026-10-27): the specs
the server registers for `UserAdd`, `UserGrantRole`, `RoleAdd`, `RoleGrantPermission` and
`AuthEnable` (`GrpcSpec`s over the client's wire models, `client/v3/InvAuthConn.lean`), what a run
holds (`authSlot`), and what the server's answers give of them. Lean-first (no Rocq counterpart);
the design is in `notes/decisions.md`, "E3za of the auth plan".

**A reply** (`adminReplied E ρ rq`, persistent): the request `rq` the client asked for (at some
header, its wire form `rq'`) was applied at the committed prefix `L` before its entry, its admin
step succeeding there (`adminDoneM`), the auth state after it published (`pubAfterM`) and its step
determinate there (`adminQh`): what `raftRequest.specM true` answers on success (`adminOutOn`),
less the response's memory and the store's certificates. For `UserAdd`, some model of the request
with the name asked for, the password choice `false` (the client sends no options) and a
password that cannot fail (`userAddReplied`).

**The specs** ask the client for no resource: the names' bound the server's admission needs
(`maxKeySize`), and the caller's postcondition from the reply. The server holds the rest: per run
its slot (`authSlot`: a reader slot of `s.leadTimeMu` and the apply environment's `E.RD`, both
back on every answer), the id budget and the index certificate (minted, `idxCert_nil`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthServer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a run of an Auth admin method holds** (see the file header). -/
def authSlot (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ E.RD)

/-- **What a successful admin call of `rq` tells the client** (persistent; see the file
header). -/
def adminReplied (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (L : List EntryModel),
    ⌜irrWireOf (apply.withHeader rq hm) rq' ∧ adminDoneM true ρ.kv rq' L⌝ ∗
    srvRLogLb ρ.raft L ∗ pubAfterM true E ρ rq' L ∗ adminQh ρ.kv rq hm L)

instance adminReplied_persistent (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) :
    Persistent (adminReplied E ρ rq) := by
  unfold adminReplied adminQh adminPropRes; infer_instance

/-- **What a successful `UserAdd` of `name` tells the client** (persistent; see the file
header). -/
def userAddReplied (E : apply.AEnv GF) (ρ : ReqNames) (name : GoString) : IProp GF :=
  iprop(∃ um : apply.UserAddModel, ⌜um.name = name ∧ um.noPassword = false ∧ um.pwSure⌝ ∗
    adminReplied E ρ (irrUserAdd um))

instance userAddReplied_persistent (E : apply.AEnv GF) (ρ : ReqNames) (name : GoString) :
    Persistent (userAddReplied E ρ name) := by
  unfold userAddReplied; infer_instance

/-- **etcd's spec of `Auth.UserAdd`** (see the file header). -/
def etcdUserAddSpec (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpec (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse :=
  fun (m : UserAddW) (Φ : Unit → IProp GF) =>
    iprop(⌜m.name.length ≤ backend.maxKeySize⌝ ∗ (userAddReplied E ρ m.name -∗ Φ ()))

/-- **etcd's spec of `Auth.UserGrantRole`** (see the file header). -/
def etcdUserGrantRoleSpec (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpec (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse :=
  fun (ur : GoString × GoString) (Φ : Unit → IProp GF) =>
    iprop(⌜ur.1.length ≤ backend.maxKeySize⌝ ∗
      (adminReplied E ρ (irrUserGrantRole ur.1 ur.2) -∗ Φ ()))

/-- **etcd's spec of `Auth.RoleAdd`** (see the file header). -/
def etcdRoleAddSpec (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpec (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse :=
  fun (name : GoString) (Φ : Unit → IProp GF) =>
    iprop(⌜name.length ≤ backend.maxKeySize⌝ ∗ (adminReplied E ρ (irrRoleAdd name) -∗ Φ ()))

/-- **etcd's spec of `Auth.RoleGrantPermission`** (see the file header). -/
def etcdRoleGrantPermissionSpec (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpec (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse :=
  fun (nw : GoString × auth.PermW) (Φ : Unit → IProp GF) =>
    iprop(⌜nw.1.length ≤ backend.maxKeySize⌝ ∗
      (adminReplied E ρ (irrRoleGrantPermission nw.1 (some nw.2)) -∗ Φ ()))

/-- **etcd's spec of `Auth.AuthEnable`** (see the file header). -/
def etcdAuthEnableSpec (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpec (GF := GF) pbAuthEnableRequest pbAuthEnableResponse :=
  fun (_ : Unit) (Φ : Unit → IProp GF) => iprop(adminReplied E ρ irrAuthEnable -∗ Φ ())

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An admin answer gives the run's slot back and, on success, the reply** (`adminOutOn`'s
success: `appliedOkM true`'s `adminDoneM`, the log's bound, the publication, the step's
determinacy). -/
theorem adminOutOn_reply (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel)
    (F : mvcc.Log) (T : go.GoType) (l : Loc) (err : GoInterface) :
    adminOutOn s E ρ rq F (adminQh ρ.kv rq) T l err ⊢
      authSlot s E ∗ (⌜err = GoInterface.nil⌝ -∗ adminReplied E ρ rq) := by
  iintro H
  iunfold adminOutOn at H
  icases H with ⟨Hlt, Hrd, H⟩
  unfold authSlot
  icases H with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hap, #Hpub, #Hq⟩ | ⟨%He, -⟩)
  · iunfold appliedOkM at Hap
    icases Hap with ⟨%x, %x', %o, %skip, %Hp, -⟩
    iframe Hlt Hrd
    iintro -
    unfold adminReplied
    iexists hm, rq', L
    iframe #
    ipureintro; exact ⟨Hw, Hp.2.2.2.2⟩
  · iframe Hlt Hrd
    iintro %He'
    exact absurd He' He

/-- **The `AuthServer`'s answer to an admin request** (`authWrapOut` over `adminOutOn`): the slot
back and, on `nil`, the reply. -/
theorem authWrapOut_admin (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel)
    (F : mvcc.Log) (T : go.GoType) (resp : Loc) (err : GoInterface) :
    authWrapOut (adminOutOn s E ρ rq F (adminQh ρ.kv rq) T) resp err ⊢
      authSlot s E ∗ (⌜err = GoInterface.nil⌝ -∗ adminReplied E ρ rq) := by
  iintro H
  iunfold authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, %e0, %He0, H⟩)
  · subst He
    iapply (adminOutOn_reply s E ρ rq F T resp GoInterface.nil) $$ H
  · ihave ⟨Hs, -⟩ := adminOutOn_reply s E ρ rq F T null e0 $$ H
    iframe Hs
    iintro %He
    exact absurd He Hr.2

end lemmas

end v3rpc
end EtcdGrove
end Perennial
