/-
**The admin proposers with auth on** (the auth plan's E3w, 2026-10-27; `notes/decisions.md`, "E3w
of the auth plan"). An Auth entry point (`EtcdServer.AuthEnable`, ...) takes `raftRequest` on its
request as the contract `authRaftOk` (`AuthEntry.lean`); in the mode `on`, `raftRequest.specM true`
covers the admin requests the mode admits (`reqPropOkOn`'s third case, `adminPropOk`: `AuthEnable`,
`UserAdd`, `RoleAdd`, `UserGrantRole` and, since E3z, `RoleGrantPermission`), and `dispatch`'s answer to one is a response of its type
(`apply.dispatchAnswer`). Here the contract's instance:

- `adminRespTy`: the response type of an admitted admin request's kind.
- `adminPreOn`, `adminOutOn`: `raftRequest.specM true`'s pre (but for the request and its
  permission; with, 5b, what gives the client's history update) and post, as the contract's `P`
  and `Q` (the post at the typed response's pointer); `adminQh`: the proposal's result, the step's
  determinacy at the commit (`adminPropRes`) and the history update's result (`adminRecRes`).
- `reqPropOkM_true_admin`: an admin request meeting `adminPropOk`, with its client's history update
  (`histAu`), has `reqPropOkM true`, its result `adminQh`.
- `authRaftOk_on`: `raftRequest.specM true` gives the contract, for any `Q` `adminOutOn` gives.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
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

/-- **The response type of an admin request the mode `on` admits** (`apply.adminKindOk`): what
`dispatch` answers it with (`apply.dispatchAnswer`) and its entry point asserts. -/
def adminRespTy : apply.ReqKind → Option go.GoType
  | .authEnable => some etcdserverpb.AuthEnableResponse.ty
  | .authUserAdd => some etcdserverpb.AuthUserAddResponse.ty
  | .authRoleAdd => some etcdserverpb.AuthRoleAddResponse.ty
  | .authUserGrantRole => some etcdserverpb.AuthUserGrantRoleResponse.ty
  | .authRoleGrantPermission => some etcdserverpb.AuthRoleGrantPermissionResponse.ty
  | _ => none

/-- **An admin request is within protobuf's recursion limit** (`proto.MarshalIRR`'s premise):
`dispatch` tests `.txn` before the admin kinds (`apply.dispatchKind`), so it has no
transaction. -/
theorem irrDepthOk_of_adminRespTy {rq : apply.IRRModel} {T : go.GoType}
    (h : adminRespTy (apply.dispatchKind rq) = some T) : apply.irrDepthOk rq := by
  apply apply.irrDepthOk_of_txn_none
  apply apply.txn_none_of_dispatchKind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he <;> rw [he] at h <;> simp [adminRespTy] at h

/-- The server's starting auth state has its users' roles sorted. -/
theorem rolesSorted_srvAuthSt0 : rolesSorted srvAuthSt0 :=
  rolesSorted_bump _ rolesSorted_bootState

/-! The five admitted admin requests of the entry points: admitted (`adminPropOk`), with no range
end `[0]` and the id `0` (the server stamps the id). -/

theorem adminPropOk_authEnable : adminPropOk srvAuthSt0 irrAuthEnable :=
  ⟨by simp [apply.adminKindOk, apply.dispatchKind, irrAuthEnable, apply.irrEmpty],
   by simp [apply.noSideEffect, irrAuthEnable, apply.irrEmpty],
   by simp [irrAuthEnable, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_userAdd (m : apply.UserAddModel) (hn : m.name.length ≤ backend.maxKeySize)
    (hpw : m.pwSure) : adminPropOk srvAuthSt0 (irrUserAdd m) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrUserAdd, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro m' h; cases h; exact ⟨hn, hpw⟩,
   by simp [apply.noSideEffect, irrUserAdd, apply.irrEmpty],
   by intro m' h; simp only [irrUserAdd, Option.some.injEq] at h; subst h; exact hpw,
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_roleAdd (name : GoString) (hn : name.length ≤ backend.maxKeySize) :
    adminPropOk srvAuthSt0 (irrRoleAdd name) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrRoleAdd, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro n h; cases h; exact hn,
   by simp [apply.noSideEffect, irrRoleAdd, apply.irrEmpty],
   by simp [irrRoleAdd, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_userGrantRole (user role : GoString) (hn : user.length ≤ backend.maxKeySize) :
    adminPropOk srvAuthSt0 (irrUserGrantRole user role) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrUserGrantRole, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro u ro h; cases h; exact hn,
   by simp [apply.noSideEffect, irrUserGrantRole, apply.irrEmpty],
   by simp [irrUserGrantRole, apply.irrEmpty],
   rolesSorted_srvAuthSt0⟩

theorem adminPropOk_roleGrantPermission (name : GoString) (w : Option auth.PermW)
    (hn : name.length ≤ backend.maxKeySize) :
    adminPropOk srvAuthSt0 (irrRoleGrantPermission name w) :=
  ⟨by simp only [apply.adminKindOk]
      simp only [apply.dispatchKind, irrRoleGrantPermission, apply.irrEmpty]
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte]
      intro n w' h; cases h; exact hn,
   by simp [apply.noSideEffect, irrRoleGrantPermission, apply.irrEmpty],
   by simp [irrRoleGrantPermission, apply.irrEmpty],
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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **What `raftRequest.specM true` needs besides the request and its permission** (the contract's
`P`; the permission of an admitted admin request is its client's update of the auth history,
`reqPropOkM_true_admin`): (5b) `□ Hh`, which gives that update (`histAu`, at the server's header
bound for `ctx`) for the request proposed (`authRaftOk_on`'s `hh`; `UserAdd`'s for every model of
its request). -/
def adminPreOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) (Hh : IProp GF) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
    isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
    context.isContext ctx cd ∗ mvcc.idxCert E.γ.idx F ∗ □ Hh)

/-- **An admin request's client update of the auth history, at the server's header bound for
`ctx`** (persistent; 5b): `histAu` with `Gb` the bound the server stamps a header under
(`hdrBoundM true`). -/
def adminHistAu (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  histAu ρ.raft ρ.kv srvAuthSt0 (hdrBoundM true s E (GoInterface.ok ctx)) rq Q

instance adminHistAu_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (adminHistAu (GF := GF) s E ρ ctx rq Q) := by
  unfold adminHistAu; infer_instance

/-- **An admitted admin request's proposal result** at the stamped header `hm` and the committed
prefix `L` before its entry: its step determinate at the model's auth state there
(`adminPropRes`), and (5b) its client's history update's result if the entry is recorded
(`adminRecRes`). -/
def adminQh (γk : KVNames) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) : IProp GF :=
  iprop(adminPropRes γk srvAuthSt0 (apply.withHeader rq hm) L ∗
    adminRecRes γk srvAuthSt0 (apply.withHeader rq hm) Q L)

/-- **What `raftRequest.specM true` answers, at the entry point's response** (the contract's `Q`):
on `nil`, the request applied at the committed prefix `L` before its entry (`appliedOkM true`, at
the response `*T` pointing to `l`; with E3x's `adminDoneM`: its step from the state `L` reaches
succeeded, `adminStepOk`), the auth state after it published (`pubAfterM true`), the
proposal's result `Qh` and (5b) the header bound to the call's context `ctx` (`hdrBoundM`); else
the error the apply thread answered with, or the request perhaps proposed. -/
def adminOutOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (rq : apply.IRRModel) (F : mvcc.Log)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (T : go.GoType) (l : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ E.RD ∗
    ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel)
        (L : List EntryModel),
        ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ srvRLogLb ρ.raft L ∗
        appliedOkM true E ρ rq' F (interface.mkOk (go.GoType.PointerType T) #l) L ∗
        pubAfterM true E ρ rq' L ∗ □ Qh hm L ∗ hdrBoundM true s E (GoInterface.ok ctx) hm) ∨
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

/-- **An admin request's proposal in the mode `on`**: meeting `adminPropOk` and needing the admin
permission, at any header, with its client's update of the auth history (`histAu`; 5b); its result
the step's determinacy at the commit and the update's result (`adminQh`). -/
theorem reqPropOkM_true_admin (γ : ServerRaftNames) (γk : KVNames)
    (Gb : apply.HeaderModel → IProp GF) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (ha : adminPropOk srvAuthSt0 rq) (hz : irrNoZeroEnd rq)
    (hna : apply.needAdminPermission rq = true) :
    histAu (GF := GF) γ γk srvAuthSt0 Gb rq Q ⊢ reqPropOkM true γ γk Gb rq (adminQh γk rq Q) := by
  iintro #Hha
  iunfold reqPropOkM
  iintro %hm
  iunfold reqPropOkOn
  iright
  iright
  iright
  iexists Q
  iframe Hha
  ipureintro
  exact ⟨ha, hz, hna, rfl⟩

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
`adminPreOn` (its `□ Hh` giving the request's history update, `hh`; 5b), answering any `Q` that
`adminOutOn` gives. -/
theorem authRaftOk_on (hRR : EtcdServer.raftRequest.specM (GF := GF) (hG := hG) true)
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (rq : apply.IRRModel) (F : mvcc.Log) (T : go.GoType)
    (Hh : IProp GF) (Qa : List auth.AuthState → IProp GF) (Q : Loc → GoInterface → IProp GF)
    (hid : rq.id = W64 0) (hT : adminRespTy (apply.dispatchKind rq) = some T)
    (ha : adminPropOk srvAuthSt0 rq) (hz : irrNoZeroEnd rq)
    (hna : apply.needAdminPermission rq = true)
    (hh : Hh ⊢ adminHistAu s E ρ ctx rq Qa)
    (hQ : ∀ l err, adminOutOn s E ρ ctx rq F (adminQh ρ.kv rq Qa) T l err ⊢ Q l err) :
    ⊢ authRaftOk (GF := GF) s ctx rq T (adminPreOn s E ρ ctx cd F Hh) Q := by
  iunfold authRaftOk
  iintro %p !> %Φ ⟨HP, Hirr, Hh⟩ HΦ
  iunfold adminPreOn at HP
  icases HP with ⟨#Hpkg, #Hsrv, Hrd, Hard, Hcred, #Hctx, #HF, #Hhh⟩
  ihave Hperm : reqPropOkM true ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) rq
      (adminQh ρ.kv rq Qa) $$ []
  · iapply reqPropOkM_true_admin (GF := GF) ρ.raft ρ.kv _ rq Qa ha hz hna
    ihave Hau := hh $$ Hhh
    iunfold adminHistAu at Hau
    iexact Hau
  wp_apply hRR s E ρ ctx cd p rq (adminQh ρ.kv rq Qa) F hid (irrDepthOk_of_adminRespTy hT) $$ [Hrd Hard Hcred Hirr Hh Hperm]
      as %resp %err ⟨Hrd, Hard, Hres⟩
  · iframe # Hrd Hard Hcred Hirr Hperm Hh
  icases Hres with (⟨%Herr, %hm, %rq', %L, %Hwire, #HL, Hok, #HpAf, #HQh, #Hhb⟩ | ⟨⟨%Hre, %Hne⟩, #HaE, Hfail⟩)
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
    icases Hfail with (⟨%hm, %rq', %Hwire, Herr, -⟩ | Hdep)
    · ileft; iexists hm, rq'; iframe Herr; ipureintro; exact Hwire
    · iright; iexact Hdep

end lemmas

end EtcdGrove
end Perennial
