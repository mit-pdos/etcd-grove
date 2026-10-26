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
  | .userAdd n => auth.userAddReqIs r n
  | .roleAdd n => auth.roleAddReqIs r n
  | .userGrantRole u ro => auth.userGrantRoleReqIs r u ro
  | .roleGrantPermission n w => auth.roleGrantPermissionReqIs r n w
  | .authEnable => iprop(True)

/-- **The request's result** with the error `err` (E2l's `adminOutFu`): the step on the latest
recorded state (the authority with its fuel after it), or the model's refusal. -/
@[reducible] def AdminReq.result (γa : auth.AuthNames) (M : auth.AuthMode) (hs : List auth.AuthState)
    (err : GoInterface) : AdminReq → IProp GF
  | .userAdd n => auth.adminOutFu γa hs (auth.stepOf (auth.userAddF n)) (fun e => e = .noPasswordUser) err
  | .roleAdd n => auth.adminOutFu γa hs (auth.stepOf (auth.roleAddF n)) auth.noExtra err
  | .userGrantRole u ro => auth.adminOutFu γa hs (auth.userGrantRoleR u ro) auth.noExtra err
  | .roleGrantPermission n w => auth.adminOutFu γa hs (auth.roleGrantPermissionR n w) auth.noExtra err
  | .authEnable => iprop(∃ en : Bool, auth.enabledVerdict M en ∗
      auth.adminOutFu γa hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err)

/-- **The admin triples of the `applierV3` value `ai` of the chain `c`** in the mode `on γa`
(see the file header), with the store's write resource `W`. -/
def adminTriples (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) (W : IProp GF) : IProp GF :=
  iprop(□ ∀ (ar : AdminReq) (r : Loc) (γa : auth.AuthNames) (hs : List auth.AuthState)
      (log : mvcc.Log) (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
    ⌜E.authMode = .on γa ∧ receiptBound GF ≤ 2 ^ 48 ∧ ar.nameOk⌝ -∗
    {{ ar.reqIs r ∗ auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W ∗ mPre E c (.ok ai) info log Pre Q Post }}
      (App (Val #(methods ai.ty ar.method ai.v)) (Val (ar.arg r)))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      mPost E c (.ok ai) log Pre Post ∗ applyErrIs err ∗ W ∗ ar.result γa E.authMode hs err }})

instance adminTriples_persistent (E : AEnv GF) (c : Chain) (ai : GoInterfaceOk) (W : IProp GF) :
    Persistent (adminTriples E c ai W) := by
  unfold adminTriples; infer_instance

/-- **The `applierV3` value `a` of the chain `c`'s admin triples** (see the file header). -/
def applierAdmin (E : AEnv GF) (c : Chain) (a : GoInterface) (W : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗ adminTriples E c ai W)

instance applierAdmin_persistent (E : AEnv GF) (c : Chain) (a : GoInterface) (W : IProp GF) :
    Persistent (applierAdmin E c a W) := by
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
      applierAdmin E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) W := by
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
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hUA E γa W p r log Pre Q Post info hs n hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | roleAdd n =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hRA E γa W p r log Pre Q Post info hs n hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | userGrantRole u ro =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hUGR E γa W p r log Pre Q Post info hs u ro hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | roleGrantPermission n w =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨Hr, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hRGP E γa W p r log Pre Q Post info hs n w hM hb hn) $$ [Hr Ho Hrc HW Hm] HΦ
    iframe Hr Ho Hrc HW Hm
    iframe #
  | authEnable =>
    simp only [AdminReq.method, AdminReq.arg, AdminReq.reqIs, AdminReq.result]
    iintro !> %Φ ⟨-, Ho, Hrc, HW, Hm⟩ HΦ
    iapply (hAE E γa W p log Pre Q Post info hs hM hb) $$ [Ho Hrc HW Hm] HΦ
    iframe Ho Hrc HW Hm
    iframe #

/-- **The quota layer's admin triples**: the inner applier's (promoted). -/
theorem applierAdmin_quota (E : AEnv GF) (c : Chain) (p : Loc) (inner : GoInterface) (W : IProp GF) :
    structFieldRef quotaApplierV3 go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W -∗
      applierAdmin E (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) W := by
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
theorem applierAdmin_capped (E : AEnv GF) (c : Chain) (p : Loc) (inner : GoInterface) (W : IProp GF) :
    structFieldRef applierV3Capped go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W -∗
      applierAdmin E (.capped c) (interface.mkOk (go.GoType.PointerType applierV3Capped.ty) #p) W := by
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
theorem applierAdmin_corrupt (E : AEnv GF) (c : Chain) (p : Loc) (inner : GoInterface) (W : IProp GF) :
    structFieldRef applierV3Corrupt go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W -∗
      applierAdmin E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) W := by
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
    (W : IProp GF) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      applierAdmin E c inner W -∗
      applierAdmin E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) W := by
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
      applierAdmin E (baseChain E.authOn) a W := by
  iintro ⟨#Hpkg, #Hsh, #Hopts, #Hst⟩
  iunfold baseShape at Hsh
  icases Hsh with ⟨%pa, %pq, %pb, %Ha, #Hpa, #Hpq, #Hpb⟩
  subst Ha
  ihave #Hbk : backendIs E pb $$ []
  · iunfold backendIs; iexists opts; iframe Hpb Hopts
  ihave #Hbs : backendAuthSteps E pb W $$ []
  · iunfold backendAuthSteps; iexists opts; iframe Hpb Hst
  ihave #Hb := applierAdmin_backend hUA hRA hUGR hRGP hAE E W pb $$ [Hpkg Hbk Hbs]
  · iframe #
  ihave #Hq := applierAdmin_quota E .backend pq _ W $$ Hpq Hb
  unfold baseChain
  iapply applierAdmin_auth E E.authOn (.quota .backend) pa _ W $$ Hpa Hq

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
        applierAdmin E (baseChain E.authOn) base W := by
  iintro ⟨#Hpkg, #Hu, #Hst⟩
  iunfold uberIs at Hu
  icases Hu with ⟨-, #Hopts, -, -, -, %base, #Hbf, -, #Hsh⟩
  iexists base
  iframe Hbf
  iapply applierAdmin_base hUA hRA hUGR hRGP hAE E W opts base $$ [Hpkg Hsh Hopts Hst]
  iframe #

end proof

end apply
end EtcdGrove
end Perennial
