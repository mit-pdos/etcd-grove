/-
**The admin requests through the applier chain in the mode `on`** (the auth plan's E2m,
2026-10-26; `notes/decisions.md`, "E2m of the auth plan"). Lean-first (no Rocq counterpart).

E2l's fuel triples (`AuthFuel.lean`) are the backend applier's (`applierV3backend.X.fuelSpec`): in
the mode `on γa`, from the admin side's authority with its fuel (`auth.authOwnFu γa hs`), one time
receipt and the store's write resource `W`, the request performs the model's step or its refusal
(`auth.adminOutFu`). Here they are lifted to an applier value of any chain (`applierAdmin E c a W`):
none of the wrappers overrides the five requests `examples/authkv`'s `SetUp` sends (`UserAdd`,
`RoleAdd`, `UserGrantRole`, `RoleGrantPermission`, `AuthEnable`: `quota.go`, `capped.go`,
`corrupt.go`, `auth.go`), so each wrapper's method is the inner applier's (promoted), and the triple
of the wrapper follows from the inner's with the wrapper's field `applierV3` read-only
(`applierAdmin_quota`, `_capped`, `_corrupt`, `_auth`). The backend's is E2l's
(`applierAdmin_backend`).

It is a separate persistent fact beside `applierSpec` (as `isAuthSteps` beside `isAuthStore`):
the admin side's authority, its fuel and `W` are the apply thread's resources (`srvAuthApplyRes`,
`InvApplier.lean`'s `srvApplyKV`), which `applierSpec`'s 28 users do not have, and `applierSpec`'s
admin clauses stay what the mode `off` needs. What is left to `dispatch` (not done): taking the
receipt at a Go step and these triples for the admin kinds in the mode `on`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthFuel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthStepsX
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver.apply
  go_etcd_io.etcd.api.v3

/-- **An admin request of `SetUp`'s five** (the auth plan's E2m), with its arguments. -/
inductive AdminReq where
  | userAdd (name : GoString)
  | roleAdd (name : GoString)
  | userGrantRole (user role : GoString)
  | roleGrantPermission (name : GoString) (w : Option auth.PermW)
  | authEnable

/-- The applier's method the request runs. -/
@[reducible] def AdminReq.method : AdminReq → GoString
  | .userAdd _ => go!"UserAdd"
  | .roleAdd _ => go!"RoleAdd"
  | .userGrantRole _ _ => go!"UserGrantRole"
  | .roleGrantPermission _ _ => go!"RoleGrantPermission"
  | .authEnable => go!"AuthEnable"

/-- The request's name within bbolt's key bound (the step specs' premise; `AuthEnable` has none). -/
@[reducible] def AdminReq.nameOk : AdminReq → Prop
  | .userAdd n => n.length ≤ backend.maxKeySize
  | .roleAdd n => n.length ≤ backend.maxKeySize
  | .userGrantRole u _ => u.length ≤ backend.maxKeySize
  | .roleGrantPermission n _ => n.length ≤ backend.maxKeySize
  | .authEnable => True

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The method's argument: the request `r`, or none (`AuthEnable()`). -/
@[reducible] def AdminReq.arg (r : Loc) : AdminReq → val
  | .authEnable => #()
  | _ => #r

/-- The request `r` holds the request (read-only: the auth package's request models). -/
@[reducible] def AdminReq.reqIs (r : Loc) : AdminReq → IProp GF
  | .userAdd n => iprop(auth.userAddReqIs r n ∗ auth.userAddSure r)
  | .roleAdd n => auth.roleAddReqIs r n
  | .userGrantRole u ro => auth.userGrantRoleReqIs r u ro
  | .roleGrantPermission n w => auth.roleGrantPermissionReqIs r n w
  | .authEnable => iprop(True)

/-- **The request's result** with the error `err` for the authority family `Own` (E2l's
`adminOutFu` at `Own = auth.authOwnFu`; E2v: an authority carrying a resource of its history,
`auth.adminOutX`): the step on the latest recorded state (`Own` after it), or the model's
refusal. -/
@[reducible] def AdminReq.result (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (γa : auth.AuthNames) (M : auth.AuthMode) (hs : List auth.AuthState)
    (err : GoInterface) : AdminReq → IProp GF
  | .userAdd n => auth.adminOutX (.on γa) (Own γa) hs (auth.stepOf (auth.userAddF n)) auth.noExtra err
  | .roleAdd n => auth.adminOutX (.on γa) (Own γa) hs (auth.stepOf (auth.roleAddF n)) auth.noExtra err
  | .userGrantRole u ro => auth.adminOutX (.on γa) (Own γa) hs (auth.userGrantRoleR u ro) auth.noExtra err
  | .roleGrantPermission n w =>
      auth.adminOutX (.on γa) (Own γa) hs (auth.roleGrantPermissionR n w) auth.noExtra err
  | .authEnable => iprop(∃ en : Bool, auth.enabledVerdict M en ∗
      auth.adminOutX (.on γa) (Own γa) hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err)

/-- **The admin triples of the `applierV3` value `ai` of the chain `c`** in the mode `on γa`
(see the file header), with the store's write resource `W` and the authority family `Own` (E2l's
`auth.authOwnFu`, or E2v's with the tie). -/
def adminTriples (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) : IProp GF :=
  iprop(□ ∀ (ar : AdminReq) (r : Loc) (γa : auth.AuthNames) (hs : List auth.AuthState)
      (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
    ⌜E.authMode = .on γa ∧ receiptBound GF ≤ 2 ^ 48 ∧ ar.nameOk⌝ -∗
    {{ ar.reqIs r ∗ Own γa hs ∗ ⧗ 1 ∗ W ∗ mPre E c (.ok ai) info log Pre Q Post }}
      (App (Val #(methods ai.ty ar.method ai.v)) (Val (ar.arg r)))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      mPost E c (.ok ai) log Pre Post ∗ applyErrIs err ∗ W ∗ ar.result Own γa E.authMode hs err }})

instance adminTriples_persistent (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    Persistent (adminTriples E c ai W Own) := by
  unfold adminTriples; infer_instance

/-- **The `applierV3` value `a` of the chain `c`'s admin triples** (see the file header). -/
def applierAdmin (E : AEnv GF) (c : Chain) (a : GoInterface) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗ adminTriples E c ai W Own)

instance applierAdmin_persistent (E : AEnv GF) (c : Chain) (a : GoInterface) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    Persistent (applierAdmin E c a W Own) := by
  unfold applierAdmin; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The backend applier's admin triples**: E2l's fuel triples. -/
theorem applierAdmin_backend
    (hUA : applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG))
    (E : AEnv GF) (W : IProp GF) (p : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      backendIs E p ∗ backendAuthSteps E p W ⊢
      applierAdmin E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) W
        auth.authOwnFu := by
  iintro ⟨#Hpkg, #Hb, #Hs⟩
  iunfold applierAdmin
  iexists ⟨go.GoType.PointerType applierV3backend.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold adminTriples
  iintro !> %ar %r %γa %hs %log %Pre %Q %Post %info %hh
  obtain ⟨hM, hb, hn⟩ := hh
  cases ar with
  | userAdd n =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result,
      ← auth.adminOutFu_eq_X]
    iintro !> %Φ ⟨⟨Hr, Hsure⟩, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hUA E γa W p r log Pre Q Post info hs n hM hb hn) $$ [Hr Hsure Ho Hrc HW Hm] HΦ
    iframe Hr Hsure Ho Hrc HW Hm
    iframe #
  | roleAdd n =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result,
      ← auth.adminOutFu_eq_X]
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hRA E γa W p r log Pre Q Post info hs n hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | userGrantRole u ro =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result,
      ← auth.adminOutFu_eq_X]
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hUGR E γa W p r log Pre Q Post info hs u ro hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | roleGrantPermission n w =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result,
      ← auth.adminOutFu_eq_X]
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hRGP E γa W p r log Pre Q Post info hs n w hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | authEnable =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result,
      ← auth.adminOutFu_eq_X]
    iintro !> %Φ ⟨-, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hAE E γa W p log Pre Q Post info hs hM hb) $$ [Ho Hrc HW Hm] HΦ
    iframe Ho Hrc HW Hm
    iframe #

/-- **The quota layer's admin triples**: the inner applier's (promoted). -/
theorem applierAdmin_quota (E : AEnv GF) (c : Chain) (p : Loc) (inner : GoInterface) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W Own -∗
      applierAdmin E (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) W Own := by
  iintro #Hf #Hin
  iunfold applierAdmin at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold applierAdmin
  iexists ⟨go.GoType.PointerType quotaApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold adminTriples
  iintro !> %ar %r %γa %hs %log %Pre %Q %Post %info %hh
  cases ar <;> simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result] <;>
  · iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty)]
    wp_call
    wp_auto
    iunfold mPre at Hm
    icases Hm with ⟨Hkv, Hres, Hcs⟩
    ihave Hres := chainRes_quota_out c p (.ok bi) info $$ Hf Hres
    iunfold adminTriples at Ht
    iapply Ht $$ %_ %r %γa %hs %log %Pre %Q %Post %info %hh [Hr Ho Hrc HW Hkv Hres Hcs]
    · iframe Hr Ho Hrc HW
      iunfold mPre
      iframe
    inext
    iintro %resp %err ⟨Hpost, #HeI, HW, HR⟩
    iapply HΦ
    iunfold mPost at Hpost
    iunfold mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe HeI Hkv HPP HW HR
    iapply chainResAny_quota_in c p (.ok bi) $$ Hf Hres

/-- **The capped layer's admin triples**: the inner applier's (promoted). -/
theorem applierAdmin_capped (E : AEnv GF) (c : Chain) (p : Loc) (inner : GoInterface) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W Own -∗
      applierAdmin E (.capped c) (interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p) W Own := by
  iintro #Hf #Hin
  iunfold applierAdmin at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold applierAdmin
  iexists ⟨go.GoType.PointerType applierV3Capped.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold adminTriples
  iintro !> %ar %r %γa %hs %log %Pre %Q %Post %info %hh
  cases ar <;> simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result] <;>
  · iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty)]
    wp_call
    wp_auto
    iunfold mPre at Hm
    icases Hm with ⟨Hkv, Hres, Hcs⟩
    ihave Hres := chainRes_capped_out c p (.ok bi) info $$ Hf Hres
    iunfold adminTriples at Ht
    iapply Ht $$ %_ %r %γa %hs %log %Pre %Q %Post %info %hh [Hr Ho Hrc HW Hkv Hres Hcs]
    · iframe Hr Ho Hrc HW
      iunfold mPre
      iframe
    inext
    iintro %resp %err ⟨Hpost, #HeI, HW, HR⟩
    iapply HΦ
    iunfold mPost at Hpost
    iunfold mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe HeI Hkv HPP HW HR
    iapply chainResAny_capped_in c p (.ok bi) $$ Hf Hres

/-- **The corrupt layer's admin triples**: the inner applier's (promoted). -/
theorem applierAdmin_corrupt (E : AEnv GF) (c : Chain) (p : Loc) (inner : GoInterface) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W Own -∗
      applierAdmin E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) W Own := by
  iintro #Hf #Hin
  iunfold applierAdmin at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold applierAdmin
  iexists ⟨go.GoType.PointerType applierV3Corrupt.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold adminTriples
  iintro !> %ar %r %γa %hs %log %Pre %Q %Post %info %hh
  cases ar <;> simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result] <;>
  · iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
    wp_call
    wp_auto
    iunfold mPre at Hm
    icases Hm with ⟨Hkv, Hres, Hcs⟩
    ihave Hres := chainRes_corrupt_out c p (.ok bi) info $$ Hf Hres
    iunfold adminTriples at Ht
    iapply Ht $$ %_ %r %γa %hs %log %Pre %Q %Post %info %hh [Hr Ho Hrc HW Hkv Hres Hcs]
    · iframe Hr Ho Hrc HW
      iunfold mPre
      iframe
    inext
    iintro %resp %err ⟨Hpost, #HeI, HW, HR⟩
    iapply HΦ
    iunfold mPost at Hpost
    iunfold mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe HeI Hkv HPP HW HR
    iapply chainResAny_corrupt_in c p (.ok bi) $$ Hf Hres

/-- **The auth layer's admin triples**: the inner applier's (promoted; the admin check is its
`Apply`'s, before the `applyFunc`: A3's `adminPass`). -/
theorem applierAdmin_auth (E : AEnv GF) (on : Bool) (c : Chain) (p : Loc) (inner : GoInterface)
    (W : IProp GF) (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W Own -∗
      applierAdmin E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) W
        Own := by
  iintro #Hf #Hin
  iunfold applierAdmin at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold applierAdmin
  iexists ⟨go.GoType.PointerType authApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold adminTriples
  iintro !> %ar %r %γa %hs %log %Pre %Q %Post %info %hh
  cases ar <;> simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result] <;>
  · iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
    wp_call
    wp_auto
    iunfold mPre at Hm
    icases Hm with ⟨Hkv, Hres, Hcs⟩
    ihave ⟨Hi, Hres⟩ := chainRes_auth_out c p (.ok bi) info $$ Hf Hres
    iunfold chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    iunfold adminTriples at Ht
    iapply Ht $$ %_ %r %γa %hs %log %Pre %Q %Post %info' %hh [Hr Ho Hrc HW Hkv Hres Hcs]
    · iframe Hr Ho Hrc HW
      iunfold mPre
      iframe
    inext
    iintro %resp %err ⟨Hpost, #HeI, HW, HR⟩
    iapply HΦ
    iunfold mPost at Hpost
    iunfold mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe HeI Hkv HPP HW HR
    iapply chainResAny_auth_in c p (.ok bi) info $$ Hf Hi Hres

/-- **The base chain's admin triples, from its backend's** (E2m, continued; generic in the
authority family, E2v): `newApplierV3`'s applier (its shape, `baseShape`), given the backend
applier's admin triples from its options and a persistent fact `S` about them (`hB`). -/
theorem applierAdmin_baseG (E : AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (S : IProp GF) [Persistent S]
    (opts : ApplierOptions) (a : GoInterface)
    (hB : ∀ pb : Loc, isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      backendIs E pb ∗ structFieldRef applierV3backend go!"options" pb ↦□ opts ∗ S ⊢
      applierAdmin E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #pb) W Own) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      baseShape opts a ∗ backendOptsOk E opts ∗ S ⊢
      applierAdmin E (baseChain E.authOn) a W Own := by
  iintro ⟨#Hpkg, #Hsh, #Hopts, #Hst⟩
  iunfold baseShape at Hsh
  icases Hsh with ⟨%pa, %pq, %pb, %Ha, #Hpa, #Hpq, #Hpb⟩
  subst Ha
  ihave #Hbk : backendIs E pb $$ []
  · iunfold backendIs; iexists opts; iframe Hpb Hopts
  ihave #Hb := hB pb $$ [Hpkg Hbk Hpb Hst]
  · iframe #
  ihave #Hq := applierAdmin_quota E .backend pq _ W Own $$ Hpq Hb
  unfold baseChain
  iapply applierAdmin_auth E E.authOn (.quota .backend) pa _ W Own $$ Hpa Hq

/-- **The base chain's admin triples** (E2m, continued): `newApplierV3`'s applier (its shape,
`baseShape`), whose backend's options hold the store `opts.AuthStore'` with its admin steps at `W`
(`isAuthSteps`, of the real store `isAuthSteps_of_authInv`). -/
theorem applierAdmin_base
    (hUA : applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG))
    (E : AEnv GF) (W : IProp GF) (opts : ApplierOptions) (a : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      baseShape opts a ∗ backendOptsOk E opts ∗ isAuthSteps opts.AuthStore' E.P E.f E.authMode W ⊢
      applierAdmin E (baseChain E.authOn) a W auth.authOwnFu := by
  apply applierAdmin_baseG E W auth.authOwnFu (isAuthSteps opts.AuthStore' E.P E.f E.authMode W) opts a
  intro pb
  iintro ⟨#Hpkg, #Hbk, #Hpb, #Hst⟩
  ihave #Hbs : backendAuthSteps E pb W $$ []
  · iunfold backendAuthSteps; iexists opts; iframe Hpb Hst
  iapply applierAdmin_backend hUA hRA hUGR hRGP hAE E W pb $$ [Hpkg Hbk Hbs]
  iframe #

/-- **The backend applier's admin triples carrying `X`** (the auth plan's E2v): `AuthStepsX.lean`'s
fuel triples, for the authority with its fuel and `X` (`auth.authOwnFu γa h ∗ X h`). -/
theorem applierAdmin_backendX
    (hUA : applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      backendIs E p ∗ backendAuthStepsX E p X W ⊢
      applierAdmin E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) W
        (fun γa h => iprop(auth.authOwnFu γa h ∗ X h)) := by
  iintro ⟨#Hpkg, #Hb, #Hs⟩
  iunfold applierAdmin
  iexists ⟨go.GoType.PointerType applierV3backend.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold adminTriples
  iintro !> %ar %r %γa %hs %log %Pre %Q %Post %info %hh
  obtain ⟨hM, hb, hn⟩ := hh
  cases ar with
  | userAdd n =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨⟨Hr, Hsure⟩, ⟨Ho, HX⟩, Hrc, HW, Hm⟩ HΦ
    iapply (hUA E γa X W p r log Pre Q Post info hs n hM hb hn) $$ [Hr Hsure Ho HX Hrc HW Hm] HΦ
    iframe Hr Hsure Ho HX Hrc HW Hm
    iframe #
  | roleAdd n =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨Hr, ⟨Ho, HX⟩, Hrc, HW, Hm⟩ HΦ
    iapply (hRA E γa X W p r log Pre Q Post info hs n hM hb hn) $$ [Hr Ho HX Hrc HW Hm] HΦ
    iframe Hr Ho HX Hrc HW Hm
    iframe #
  | userGrantRole u ro =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨Hr, ⟨Ho, HX⟩, Hrc, HW, Hm⟩ HΦ
    iapply (hUGR E γa X W p r log Pre Q Post info hs u ro hM hb hn) $$ [Hr Ho HX Hrc HW Hm] HΦ
    iframe Hr Ho HX Hrc HW Hm
    iframe #
  | roleGrantPermission n w =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨Hr, ⟨Ho, HX⟩, Hrc, HW, Hm⟩ HΦ
    iapply (hRGP E γa X W p r log Pre Q Post info hs n w hM hb hn) $$ [Hr Ho HX Hrc HW Hm] HΦ
    iframe Hr Ho HX Hrc HW Hm
    iframe #
  | authEnable =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨-, ⟨Ho, HX⟩, Hrc, HW, Hm⟩ HΦ
    iapply (hAE E γa X W p log Pre Q Post info hs hM hb) $$ [Ho HX Hrc HW Hm] HΦ
    iframe Ho HX Hrc HW Hm
    iframe #

/-- **The base chain's admin triples carrying `X`** (the auth plan's E2v): as `applierAdmin_base`,
from the store's `isAuthStepsX` (of the real store with the tie, `isAuthStepsX_of_authInvT`). -/
theorem applierAdmin_baseX
    (hUA : applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (opts : ApplierOptions)
    (a : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      baseShape opts a ∗ backendOptsOk E opts ∗ isAuthStepsX opts.AuthStore' E.P E.f E.authMode X W ⊢
      applierAdmin E (baseChain E.authOn) a W (fun γa h => iprop(auth.authOwnFu γa h ∗ X h)) := by
  apply applierAdmin_baseG E W _ (isAuthStepsX opts.AuthStore' E.P E.f E.authMode X W) opts a
  intro pb
  iintro ⟨#Hpkg, #Hbk, #Hpb, #Hst⟩
  ihave #Hbs : backendAuthStepsX E pb X W $$ []
  · iunfold backendAuthStepsX; iexists opts; iframe Hpb Hst
  iapply applierAdmin_backendX hUA hRA hUGR hRGP hAE E X W pb $$ [Hpkg Hbk Hbs]
  iframe #

/-- **The uber-applier's base applier's admin triples** (E2m, continued; generic, E2v): from
`uberIs` and its options' store's fact `S` giving the base chain's (`applierAdmin_base`,
`applierAdmin_baseX`). -/
theorem applierAdmin_uberG (E : AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (S : GoInterface → IProp GF)
    [∀ x, Persistent (S x)] (p : Loc) (opts : ApplierOptions)
    (hB : ∀ a : GoInterface, isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      baseShape opts a ∗ backendOptsOk E opts ∗ S opts.AuthStore' ⊢
      applierAdmin E (baseChain E.authOn) a W Own) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      uberIs E p opts ∗ S opts.AuthStore' ⊢
      ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        applierAdmin E (baseChain E.authOn) base W Own := by
  iintro ⟨#Hpkg, #Hu, #Hst⟩
  iunfold uberIs at Hu
  icases Hu with ⟨-, #Hopts, -, -, -, %base, #Hbf, -, #Hsh⟩
  iexists base
  iframe Hbf
  iapply hB base $$ [Hpkg Hsh Hopts Hst]
  iframe #

/-- **The uber-applier's base applier's admin triples** (E2m, continued): from `uberIs`. -/
theorem applierAdmin_uber
    (hUA : applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG))
    (E : AEnv GF) (W : IProp GF) (p : Loc) (opts : ApplierOptions) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      uberIs E p opts ∗ isAuthSteps opts.AuthStore' E.P E.f E.authMode W ⊢
      ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        applierAdmin E (baseChain E.authOn) base W auth.authOwnFu :=
  applierAdmin_uberG E W auth.authOwnFu (fun st => isAuthSteps st E.P E.f E.authMode W) p opts
    (fun a => applierAdmin_base hUA hRA hUGR hRGP hAE E W opts a)

/-- **The uber-applier's base applier's admin triples carrying `X`** (the auth plan's E2v). -/
theorem applierAdmin_uberX
    (hUA : applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (E : AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p : Loc)
    (opts : ApplierOptions) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      uberIs E p opts ∗ isAuthStepsX opts.AuthStore' E.P E.f E.authMode X W ⊢
      ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        applierAdmin E (baseChain E.authOn) base W (fun γa h => iprop(auth.authOwnFu γa h ∗ X h)) :=
  applierAdmin_uberG E W _ (fun st => isAuthStepsX st E.P E.f E.authMode X W) p opts
    (fun a => applierAdmin_baseX hUA hRA hUGR hRGP hAE E X W opts a)

/-- **The alarms' wrappers' admin triples** (the auth plan's E2o): the base applier's, through
`restoreAlarms`' capped and corrupt wrappers (`alarmShape`). -/
theorem applierAdmin_alarm (E : AEnv GF) (ns cr : Bool) (base a : GoInterface) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    alarmShape ns cr base a ⊢ applierAdmin E (baseChain E.authOn) base W Own -∗
      applierAdmin E (alarmChain E.authOn ns cr) a W Own := by
  iintro #Hsh #Hb
  iunfold alarmShape at Hsh
  icases Hsh with ⟨%a1, #H1, #H2⟩
  ihave #Ha1 : applierAdmin E (if ns then Chain.capped (baseChain E.authOn) else baseChain E.authOn)
      a1 W Own $$ []
  · cases ns
    · iunfold cappedShape at H1
      icases H1 with %h1
      subst h1
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hb
    · iunfold cappedShape at H1
      icases H1 with ⟨%pc, %h1, #Hc⟩
      subst h1
      iunfold cappedIs at Hc
      simp only [↓reduceIte]
      iapply applierAdmin_capped E _ pc base W Own $$ Hc Hb
  unfold alarmChain
  cases cr
  · iunfold corruptShape at H2
    icases H2 with %h2
    subst h2
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Ha1
  · iunfold corruptShape at H2
    icases H2 with ⟨%pr, %h2, #Hc⟩
    subst h2
    iunfold corruptIs at Hc
    simp only [↓reduceIte]
    iapply applierAdmin_corrupt E _ pr a1 W Own $$ Hc Ha1

/-- **The current applier's admin triples, from the base applier's** (the auth plan's E2o;
generic, E2v): the uber-applier's base applier's admin triples and the current applier's shape
(`uberShape`, kept in `uberOwn`). -/
theorem applierAdmin_curG (E : AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (p : Loc) (c : Chain) (a : GoInterface) :
    (∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        applierAdmin E (baseChain E.authOn) base W Own) ∗ uberShape E p c a ⊢
      applierAdmin E c a W Own := by
  iintro ⟨⟨%base, #Hbf, #Hb⟩, #Hsh⟩
  iunfold uberShape at Hsh
  icases Hsh with ⟨%base', %ns, %cr, %hc, #Hbf', #Has⟩
  icombine Hbf Hbf' gives %hb
  subst hb hc
  iapply applierAdmin_alarm E ns cr base a W Own $$ Has Hb

/-- **The current applier's admin triples** (the auth plan's E2o): from the uber-applier's base
applier's (`applierAdmin_uber`) and the current applier's shape (`uberShape`, kept in
`uberOwn`). -/
theorem applierAdmin_cur
    (hUA : applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG))
    (hRA : applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG))
    (hUGR : applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG))
    (hRGP : applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG))
    (hAE : applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG))
    (E : AEnv GF) (W : IProp GF) (p : Loc) (opts : ApplierOptions) (c : Chain) (a : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      uberIs E p opts ∗ isAuthSteps opts.AuthStore' E.P E.f E.authMode W ∗ uberShape E p c a ⊢
      applierAdmin E c a W auth.authOwnFu := by
  iintro ⟨#Hpkg, #Hu, #Hst, #Hsh⟩
  ihave #Hb := applierAdmin_uber hUA hRA hUGR hRGP hAE E W p opts $$ [Hpkg Hu Hst]
  · iframe #
  iapply applierAdmin_curG E W auth.authOwnFu p c a $$ [Hb Hsh]
  iframe #

end proof

end apply
end EtcdGrove
end Perennial
