/-
**etcd's specs of the Auth service's admin methods** (the auth plan's E3za, 2026-10-27): the specs
the server registers for `UserAdd`, `UserGrantRole`, `RoleAdd`, `RoleGrantPermission` and
`AuthEnable` (`GrpcSpec`s over the client's wire models, `client/v3/InvAuthConn.lean`), what a run
holds (`authSlot`), and what the server's answers give of them. Lean-first (no Rocq counterpart);
the design is in `notes/decisions.md`, "E3za of the auth plan".

**A reply** (`adminReplied s E ρ tok rq Q`, persistent): the request `rq` the client asked for (at
some header, its wire form `rq'`) was applied at the committed prefix `L` before its entry, its
admin step succeeding there (`adminDoneM`), the auth state after it published (`pubAfterM`), its
step determinate there and, if its entry is recorded in the auth history, the result `Q` of the
client's update (`adminQh`), the header bound to the call's token `tok` (`hdrBoundT`): what
`raftRequest.specM true` answers on success (`adminOutOn`), less the response's memory and the
store's certificates. For `UserAdd`, some model of the request with the name asked for, the
password choice `false` (the client sends no options) and a password that cannot fail
(`userAddReplied`).

**The specs** (metadata-indexed: the auth-mode merge's 5b, 2026-10-29) ask the client for its
update of the auth history (`histAu`, at the header bound to the attempt's token; for `UserAdd`,
at every model of the request), the names' bound the server's admission needs (`maxKeySize`), and
the caller's postcondition from the reply. The server holds the rest: per run
its slot (`authSlot`: a reader slot of `s.leadTimeMu` and the apply environment's `E.RD`, both
back on every answer), the id budget and the index certificate (minted, `idxCert_nil`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn

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
def adminReplied (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (L : List EntryModel),
    ⌜irrWireOf (apply.withHeader rq hm) rq' ∧ adminDoneM true ρ.kv rq' L⌝ ∗
    srvRLogLb ρ.raft L ∗ pubAfterM true E ρ rq' L ∗ adminQh ρ.kv rq Q hm L ∗
    hdrBoundT s E.authMode tok hm)

instance adminReplied_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (adminReplied s E ρ tok rq Q) := by
  unfold adminReplied adminQh adminPropRes; infer_instance

/-- **What a successful `UserAdd` of `name` tells the client** (persistent; see the file
header). -/
def userAddReplied (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (name : GoString) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ um : apply.UserAddModel, ⌜um.name = name ∧ um.noPassword = false ∧ um.pwSure⌝ ∗
    adminReplied s E ρ tok (irrUserAdd um) Q)

instance userAddReplied_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (name : GoString) (Q : List auth.AuthState → IProp GF) :
    Persistent (userAddReplied s E ρ tok name Q) := by
  unfold userAddReplied; infer_instance

/-- **A client's update of the auth history by `rq`, at the token `tok`** (persistent; 5b):
`histAu` with the header bound to `tok` (`hdrBoundT`). -/
def authHistAuT (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  histAu ρ.raft ρ.kv srvAuthSt0 (hdrBoundT s E.authMode tok) rq Q

instance authHistAuT_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (authHistAuT s E ρ tok rq Q) := by
  unfold authHistAuT; infer_instance

/-- **etcd's spec of `Auth.UserAdd`** (see the file header). -/
def etcdUserAddSpec (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse :=
  fun md (m : UserAddW) (Φ : Unit → IProp GF) =>
    iprop(∃ Q : List auth.AuthState → IProp GF, ⌜m.name.length ≤ backend.maxKeySize⌝ ∗
      □ (∀ um : apply.UserAddModel, ⌜um.name = m.name ∧ um.noPassword = false ∧ um.pwSure⌝ →
        authHistAuT s E ρ (auth.mdTokenOf md) (irrUserAdd um) Q) ∗
      (userAddReplied s E ρ (auth.mdTokenOf md) m.name Q -∗ Φ ()))

/-- **etcd's spec of `Auth.UserGrantRole`** (see the file header). -/
def etcdUserGrantRoleSpec (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse :=
  fun md (ur : GoString × GoString) (Φ : Unit → IProp GF) =>
    iprop(∃ Q : List auth.AuthState → IProp GF, ⌜ur.1.length ≤ backend.maxKeySize⌝ ∗
      authHistAuT s E ρ (auth.mdTokenOf md) (irrUserGrantRole ur.1 ur.2) Q ∗
      (adminReplied s E ρ (auth.mdTokenOf md) (irrUserGrantRole ur.1 ur.2) Q -∗ Φ ()))

/-- **etcd's spec of `Auth.RoleAdd`** (see the file header). -/
def etcdRoleAddSpec (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse :=
  fun md (name : GoString) (Φ : Unit → IProp GF) =>
    iprop(∃ Q : List auth.AuthState → IProp GF, ⌜name.length ≤ backend.maxKeySize⌝ ∗
      authHistAuT s E ρ (auth.mdTokenOf md) (irrRoleAdd name) Q ∗
      (adminReplied s E ρ (auth.mdTokenOf md) (irrRoleAdd name) Q -∗ Φ ()))

/-- **etcd's spec of `Auth.RoleGrantPermission`** (see the file header). -/
def etcdRoleGrantPermissionSpec (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse :=
  fun md (nw : GoString × auth.PermW) (Φ : Unit → IProp GF) =>
    iprop(∃ Q : List auth.AuthState → IProp GF, ⌜nw.1.length ≤ backend.maxKeySize⌝ ∗
      authHistAuT s E ρ (auth.mdTokenOf md) (irrRoleGrantPermission nw.1 (some nw.2)) Q ∗
      (adminReplied s E ρ (auth.mdTokenOf md) (irrRoleGrantPermission nw.1 (some nw.2)) Q -∗
        Φ ()))

/-- **etcd's spec of `Auth.AuthEnable`** (see the file header). -/
def etcdAuthEnableSpec (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthEnableRequest pbAuthEnableResponse :=
  fun md (_ : Unit) (Φ : Unit → IProp GF) =>
    iprop(∃ Q : List auth.AuthState → IProp GF,
      authHistAuT s E ρ (auth.mdTokenOf md) irrAuthEnable Q ∗
      (adminReplied s E ρ (auth.mdTokenOf md) irrAuthEnable Q -∗ Φ ()))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server's update from the client's** at the call's context: the bound the server
stamps a header under (`hdrBoundM true`) is one bound to the context's token (`hdrBoundM_tok`). -/
theorem adminHistAu_of_tok (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    authHistAuT (GF := GF) s E ρ (auth.ctxTokenOf (GoInterface.ok ctx)) rq Q ⊢
      adminHistAu s E ρ ctx rq Q := by
  unfold authHistAuT adminHistAu
  exact histAu_mono _ _ _ _ _ _ _ (fun hm => hdrBoundM_tok s E _ hm)

/-- **An admin answer gives the run's slot back and, on success, the reply** (`adminOutOn`'s
success: `appliedOkM true`'s `adminDoneM`, the log's bound, the publication, the step's
determinacy and the history update's result, the header's bound). -/
theorem adminOutOn_reply (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (F : mvcc.Log) (T : go.GoType) (l : Loc) (err : GoInterface) :
    adminOutOn s E ρ ctx rq F (adminQh ρ.kv rq Q) T l err ⊢
      authSlot s E ∗
        (⌜err = GoInterface.nil⌝ -∗ adminReplied s E ρ (auth.ctxTokenOf (GoInterface.ok ctx)) rq Q) := by
  iintro H
  iunfold adminOutOn at H
  icases H with ⟨Hlt, Hrd, H⟩
  unfold authSlot
  icases H with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hap, #Hpub, #Hq, #Hhb⟩ | ⟨%He, -⟩)
  · iunfold appliedOkM at Hap
    icases Hap with ⟨%x, %x', %o, %skip, %Hp, -⟩
    iframe Hlt Hrd
    iintro -
    unfold adminReplied
    iexists hm, rq', L
    ihave #Hhb' := hdrBoundM_tok s E _ hm $$ Hhb
    iframe #
    ipureintro; exact ⟨Hw, Hp.2.2.2.2⟩
  · iframe Hlt Hrd
    iintro %He'
    exact absurd He' He

/-- **The `AuthServer`'s answer to an admin request** (`authWrapOut` over `adminOutOn`): the slot
back and, on `nil`, the reply. -/
theorem authWrapOut_admin (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (F : mvcc.Log) (T : go.GoType) (resp : Loc) (err : GoInterface) :
    authWrapOut (adminOutOn s E ρ ctx rq F (adminQh ρ.kv rq Q) T) resp err ⊢
      authSlot s E ∗
        (⌜err = GoInterface.nil⌝ -∗ adminReplied s E ρ (auth.ctxTokenOf (GoInterface.ok ctx)) rq Q) := by
  iintro H
  iunfold authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, %e0, %He0, H⟩)
  · subst He
    iapply (adminOutOn_reply s E ρ ctx rq Q F T resp GoInterface.nil) $$ H
  · ihave ⟨Hs, -⟩ := adminOutOn_reply s E ρ ctx rq Q F T null e0 $$ H
    iframe Hs
    iintro %He
    exact absurd He Hr.2

end lemmas

end v3rpc
end EtcdGrove
end Perennial
