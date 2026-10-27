/-
**The admin proposers with auth on** (the auth plan's E3w, 2026-10-27; `notes/decisions.md`, "E3w
of the auth plan"). An Auth entry point (`EtcdServer.AuthEnable`, ...) takes `raftRequest` on its
request as the contract `authRaftOk` (`AuthEntry.lean`); in the mode `on`, `raftRequest.specM true`
covers the admin requests the mode admits (`reqPropOkOn`'s third case, `adminPropOk`: `AuthEnable`,
`UserAdd`, `RoleAdd`, `UserGrantRole`), and `dispatch`'s answer to one is a response of its type
(`apply.dispatchAnswer`). Here the contract's instance:

- `adminRespTy`: the response type of an admitted admin request's kind.
- `adminPreOn`, `adminOutOn`: `raftRequest.specM true`'s pre (but for the request and its
  permission) and post, as the contract's `P` and `Q` (the post at the typed response's pointer);
  `adminQh`: the proposal's result, the step's determinacy at the commit (`adminPropRes`).
- `reqPropOkM_true_admin`: an admin request meeting `adminPropOk` has `reqPropOkM true`, its result
  the step's determinacy at the commit (`adminPropRes`).
- `authRaftOk_on`: `raftRequest.specM true` gives the contract, for any `Q` `adminOutOn` gives.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthEntry
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthShape
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The response type of an admin request the mode `on` admits** (`apply.adminKindOk`, but for
`RoleGrantPermission`, which `adminPropOk` leaves out): what `dispatch` answers it with
(`apply.dispatchAnswer`) and its entry point asserts. -/
def adminRespTy : apply.ReqKind → Option go.GoType
  | .authEnable => some etcdserverpb.AuthEnableResponse.ty
  | .authUserAdd => some etcdserverpb.AuthUserAddResponse.ty
  | .authRoleAdd => some etcdserverpb.AuthRoleAddResponse.ty
  | .authUserGrantRole => some etcdserverpb.AuthUserGrantRoleResponse.ty
  | _ => none

/-- The server's starting auth state has its users' roles sorted. -/
theorem rolesSorted_srvAuthSt0 : rolesSorted srvAuthSt0 :=
  rolesSorted_bump _ rolesSorted_bootState

/-! The four admitted admin requests of the entry points: admitted (`adminPropOk`), with no range
end `[0]` and the id `0` (the server stamps the id). -/

theorem adminPropOk_authEnable : adminPropOk srvAuthSt0 irrAuthEnable :=
  ⟨by simp [apply.adminKindOk, apply.dispatchKind, irrAuthEnable, apply.irrEmpty],
   by simp [apply.noSideEffect, irrAuthEnable, apply.irrEmpty],
   by simp [apply.needAdminPermission, irrAuthEnable, apply.irrEmpty],
   by simp [irrAuthEnable, apply.irrEmpty], by simp [irrAuthEnable, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_userAdd (m : apply.UserAddModel) (hn : m.name.length ≤ backend.maxKeySize)
    (hpw : m.pwSure) : adminPropOk srvAuthSt0 (irrUserAdd m) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrUserAdd, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro m' h; cases h; exact ⟨hn, hpw⟩,
   by simp [apply.noSideEffect, irrUserAdd, apply.irrEmpty],
   by simp [apply.needAdminPermission, irrUserAdd, apply.irrEmpty],
   by intro m' h; simp only [irrUserAdd, Option.some.injEq] at h; subst h; exact hpw,
   by simp [irrUserAdd, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_roleAdd (name : GoString) (hn : name.length ≤ backend.maxKeySize) :
    adminPropOk srvAuthSt0 (irrRoleAdd name) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrRoleAdd, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro n h; cases h; exact hn,
   by simp [apply.noSideEffect, irrRoleAdd, apply.irrEmpty],
   by simp [apply.needAdminPermission, irrRoleAdd, apply.irrEmpty],
   by simp [irrRoleAdd, apply.irrEmpty], by simp [irrRoleAdd, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_userGrantRole (user role : GoString) (hn : user.length ≤ backend.maxKeySize) :
    adminPropOk srvAuthSt0 (irrUserGrantRole user role) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrUserGrantRole, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro u ro h; cases h; exact hn,
   by simp [apply.noSideEffect, irrUserGrantRole, apply.irrEmpty],
   by simp [apply.needAdminPermission, irrUserGrantRole, apply.irrEmpty],
   by simp [irrUserGrantRole, apply.irrEmpty], by simp [irrUserGrantRole, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

/-- An admin request (no KV field) has no range end `[0]`. -/
theorem irrNoZeroEnd_admin (rq : apply.IRRModel) (h1 : rq.range = none)
    (h2 : rq.deleteRange = none) (h3 : rq.txn = none) : irrNoZeroEnd rq := by
  refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp_all

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What `raftRequest.specM true` needs besides the request and its permission** (the contract's
`P`; the permission of an admitted admin request is free, `reqPropOkM_true_admin`). -/
def adminPreOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
    isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
    context.isContext ctx cd ∗ mvcc.idxCert E.γ.idx F)

/-- **An admitted admin request's proposal result** at the stamped header `hm` and the committed
prefix `L` before its entry: its step determinate at the model's auth state there
(`adminPropRes`). -/
def adminQh (γk : KVNames) (rq : apply.IRRModel) (hm : apply.HeaderModel) (L : List EntryModel) :
    IProp GF :=
  adminPropRes γk srvAuthSt0 (apply.withHeader rq hm) L

/-- **What `raftRequest.specM true` answers, at the entry point's response** (the contract's `Q`):
on `nil`, the request applied at the committed prefix `L` before its entry (`appliedOkM true`, at
the response `*T` pointing to `l`; with E3x's `adminDoneM`: its step from the state `L` reaches
succeeded, `adminStepOk`), the auth state after it published (`pubAfterM true`) and the
proposal's result `Qh`; else the error the apply thread answered with, or the request perhaps
proposed. -/
def adminOutOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (rq : apply.IRRModel) (F : mvcc.Log)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (T : go.GoType) (l : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ E.RD ∗
    ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel)
        (L : List EntryModel),
        ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ srvRLogLb ρ.raft L ∗
        appliedOkM true E ρ rq' F (interface.mkOk (go.GoType.PointerType T) #l) L ∗
        pubAfterM true E ρ rq' L ∗ □ Qh hm L) ∨
     (⌜err ≠ GoInterface.nil⌝ ∗
       ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
        srvMaybeDeposited ρ rq))))

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **An admin request's proposal in the mode `on`**: meeting `adminPropOk`, at any header, its
result the step's determinacy at the commit (`adminPropRes`). -/
theorem reqPropOkM_true_admin (γk : KVNames) (rq : apply.IRRModel)
    (ha : adminPropOk srvAuthSt0 rq) (hz : irrNoZeroEnd rq) :
    ⊢ reqPropOkM (GF := GF) true γk rq (adminQh γk rq) := by
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  iright
  iright
  ipureintro
  exact ⟨ha, hz, rfl⟩

/-- **`dispatch`'s answer to an admitted admin request is a response of its type.** -/
theorem dispatchAnswer_admin (rq : apply.IRRModel) (log : mvcc.Log) (skip : Bool)
    (resp err : GoInterface) (o : apply.Outcome) (T : go.GoType)
    (hT : adminRespTy (apply.dispatchKind rq) = some T) :
    apply.dispatchAnswer (GF := GF) rq log skip resp err o ⊢
      apply.dispatchAnswer rq log skip resp err o ∗
        ⌜∃ r : Loc, resp = interface.mkOk (go.GoType.PointerType T) #r⌝ := by
  unfold apply.dispatchAnswer
  revert hT
  cases apply.dispatchKind rq <;> intro hT <;> simp only [adminRespTy, reduceCtorEq] at hT <;>
    (cases hT; iintro ⟨%r, %h⟩; isplitl
     · iexists r; ipureintro; exact h
     ipureintro; exact ⟨r, h⟩)

/-- **The Auth entry points' contract, in the mode `on`** (see the file header): for an admitted
admin request (`adminRespTy`, `adminPropOk`), `raftRequest.specM true` is `authRaftOk` over
`adminPreOn`, answering any `Q` that `adminOutOn` gives. -/
theorem authRaftOk_on (hRR : EtcdServer.raftRequest.specM (GF := GF) (hG := hG) true)
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (rq : apply.IRRModel) (F : mvcc.Log) (T : go.GoType)
    (Q : Loc → GoInterface → IProp GF)
    (hid : rq.id = W64 0) (hT : adminRespTy (apply.dispatchKind rq) = some T)
    (ha : adminPropOk srvAuthSt0 rq) (hz : irrNoZeroEnd rq)
    (hQ : ∀ l err, adminOutOn s E ρ rq F (adminQh ρ.kv rq) T l err ⊢ Q l err) :
    ⊢ authRaftOk (GF := GF) s ctx rq T (adminPreOn s E ρ ctx cd F) Q := by
  iunfold authRaftOk
  iintro %p !> %Φ ⟨HP, Hirr, Hh⟩ HΦ
  iunfold adminPreOn at HP
  icases HP with ⟨#Hpkg, #Hsrv, Hrd, Hard, Hcred, #Hctx, #HF⟩
  ihave Hperm : reqPropOkM true ρ.kv rq (adminQh ρ.kv rq) $$ []
  · iapply reqPropOkM_true_admin (GF := GF) ρ.kv rq ha hz
  wp_apply hRR s E ρ ctx cd p rq (adminQh ρ.kv rq) F hid $$ [Hrd Hard Hcred Hirr Hh Hperm]
      as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe # Hrd Hard Hcred Hirr Hperm Hh
  icases Hres with (⟨%Herr, %hm, %rq', %L, %Hwire, #HL, Hok, #HpAf, #HQh⟩ | ⟨⟨%Hre, %Hne⟩, #HaE, Hfail⟩)
  · subst Herr
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hstep, Hans, Hok⟩
    have hT' : adminRespTy (apply.dispatchKind rq') = some T := by rw [Hwire.2.2.1]; exact hT
    ihave ⟨Hans, %Hty⟩ := dispatchAnswer_admin rq' x.log skip resp GoInterface.nil o T hT' $$ Hans
    obtain ⟨l, rfl⟩ := Hty
    iapply HΦ
    isplitl []
    · iapply applyErrIs_nil
    ileft
    isplitr
    · ipureintro; rfl
    iexists l
    isplitr
    · ipureintro; rfl
    iapply hQ
    iunfold adminOutOn
    iframe Hrd Hard
    ileft
    isplitr
    · ipureintro; rfl
    iexists hm, rq', L
    iframe #
    isplitr
    · ipureintro; exact Hwire
    iunfold appliedOkM
    iexists x, x', o, skip
    iframe Hans Hok
    ipureintro; exact Hstep
  · subst Hre
    iapply HΦ
    iframe HaE
    iright
    isplitr
    · ipureintro; exact ⟨rfl, Hne⟩
    iapply hQ
    iunfold adminOutOn
    iframe Hrd Hard
    iright
    isplitr
    · ipureintro; exact Hne
    iexact Hfail

end lemmas

end EtcdGrove
end Perennial
