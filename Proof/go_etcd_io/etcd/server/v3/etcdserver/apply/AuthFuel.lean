/-
**The apply layer's admin steps with the receipts' budget** (the auth plan's E2l, 2026-10-26;
`notes/decisions.md`, "E2l of the auth plan"). Lean-first (no Rocq counterpart).

`AuthSteps.lean`'s step triples (`applierV3backend.X.stepSpec`) take S4's premise `stepOk` at the
authority's history. In the mode `on γa` the apply thread holds, with the authority, its fuel
(`auth.authOwnFu`, `auth/Fuel.lean`): time receipts counting the admin side's revision, and the
latest state's size. With one more receipt (the request's own, from a Go step of the apply
thread before the call, as an applied entry's write token is paid, `srvWTPool_take_extra`) the
premise holds under the receipts' bound `receiptBound GF ≤ 2 ^ 48` (`auth.stepOk_of_fuel`), and the
fuel follows the authority to the step's result (`auth.adminOutFu`). The triples here are those
of the requests `examples/authkv`'s `SetUp` sends (`UserAdd`, `RoleAdd`, `UserGrantRole`,
`RoleGrantPermission`, `AuthEnable`), each derived from its step triple.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthSteps
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel

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

section fuelSpecs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`a.UserAdd(r)` in the mode `on γa`, from the fuel** (see the file header). -/
abbrev applierV3backend.UserAdd.fuelSpec : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.userAddReqIs r name ∗
        auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutFu γa hs (auth.stepOf (auth.userAddF name)) (fun e => e = .noPasswordUser) err }}

/-- **`a.RoleAdd(r)` in the mode `on γa`, from the fuel**. -/
abbrev applierV3backend.RoleAdd.fuelSpec : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.roleAddReqIs r name ∗
        auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleAdd")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutFu γa hs (auth.stepOf (auth.roleAddF name)) auth.noExtra err }}

/-- **`a.UserGrantRole(r)` in the mode `on γa`, from the fuel** (the user's roles below `2 ^ 62`
from the latest state's size). -/
abbrev applierV3backend.UserGrantRole.fuelSpec : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (user role : GoString),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → user.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.userGrantRoleReqIs r user role ∗
        auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"UserGrantRole")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutFu γa hs (auth.userGrantRoleR user role) auth.noExtra err }}

/-- **`a.RoleGrantPermission(r)` in the mode `on γa`, from the fuel**. -/
abbrev applierV3backend.RoleGrantPermission.fuelSpec : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (W : IProp GF) (p r : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState) (name : GoString) (w : Option auth.PermW),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 → name.length ≤ backend.maxKeySize →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.roleGrantPermissionReqIs r name w ∗
        auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"RoleGrantPermission")) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      auth.adminOutFu γa hs (auth.roleGrantPermissionR name w) auth.noExtra err }}

/-- **`a.AuthEnable()` in the mode `on γa`, from the fuel**. -/
abbrev applierV3backend.AuthEnable.fuelSpec : Prop :=
  ∀ (E : AEnv GF) (γa : auth.AuthNames) (W : IProp GF) (p : Loc) (log : mvcc.Log)
    (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hs : List auth.AuthState),
    E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        apply.backendIs E p ∗ backendAuthSteps E p W ∗ auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W ∗
        apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post }}
      (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthEnable")) (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗
      applyErrIs err ∗ W ∗
      ∃ en : Bool, auth.enabledVerdict E.authMode en ∗
        auth.adminOutFu γa hs (auth.stepOf (auth.authEnableF en)) auth.noExtra err }}

end fuelSpecs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem applierV3backend.UserAdd.wp_fuel
    (h : applierV3backend.UserAdd.stepSpec (GF := GF) (hG := hG)) :
    applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG) := by
  intro E γa W p r log Pre Q Post info hs name hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.stepOf (auth.userAddF name)) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_userAdd name hn) Hfk Hlt
  iapply (h E W p r log Pre Q Post info hs name hn hok) $$ [Hr Ho HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOut_fu γa hs _ _ err (auth.stepSmall_userAdd name hn) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.RoleAdd.wp_fuel
    (h : applierV3backend.RoleAdd.stepSpec (GF := GF) (hG := hG)) :
    applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG) := by
  intro E γa W p r log Pre Q Post info hs name hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.stepOf (auth.roleAddF name)) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_roleAdd name) Hfk Hlt
  iapply (h E W p r log Pre Q Post info hs name hn hok) $$ [Hr Ho HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOut_fu γa hs _ _ err (auth.stepSmall_roleAdd name) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.UserGrantRole.wp_fuel
    (h : applierV3backend.UserGrantRole.stepSpec (GF := GF) (hG := hG)) :
    applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG) := by
  intro E γa W p r log Pre Q Post info hs user role hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.userGrantRoleR user role) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_userGrantRole user role) Hfk Hlt
  have hroles : ∀ (sta : auth.AuthState) (u : auth.User), auth.histLast E.authMode hs sta →
      sta.users !! user = some u → u.length < 2 ^ 62 := by
    intro sta u hl hu
    rw [hM] at hl
    obtain ⟨h1, h2⟩ := auth.fuelOk_last γa hs k sta Hfk hl
    have := h2.roles user u hu
    omega
  iapply (h E W p r log Pre Q Post info hs user role hn hroles hok) $$ [Hr Ho HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOut_fu γa hs _ _ err (auth.stepSmall_userGrantRole user role) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.RoleGrantPermission.wp_fuel
    (h : applierV3backend.RoleGrantPermission.stepSpec (GF := GF) (hG := hG)) :
    applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG) := by
  intro E γa W p r log Pre Q Post info hs name w hM hb hn
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, Hr, HOF, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : auth.stepOk E.authMode hs (auth.roleGrantPermissionR name w) :=
    hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_roleGrantPermission name w) Hfk Hlt
  iapply (h E W p r log Pre Q Post info hs name w hn hok) $$ [Hr Ho HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, Hout⟩
  rw [hM]
  ihave Hout := auth.adminOut_fu γa hs _ _ err (auth.stepSmall_roleGrantPermission name w) $$
    [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

theorem applierV3backend.AuthEnable.wp_fuel
    (h : applierV3backend.AuthEnable.stepSpec (GF := GF) (hG := hG)) :
    applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG) := by
  intro E γa W p log Pre Q Post info hs hM hb
  iintro %Φ ⟨#Hpkg, #Hb, #Hs, HOF, Hrc, HW, Hpre⟩ HΦ
  iunfold auth.authOwnFu at HOF
  icases HOF with ⟨Ho, Hf⟩
  ihave Hf := auth.authFuel_charge hs $$ [Hf Hrc]
  · iframe
  icases auth.authFuelT_fuel hs hb $$ Hf with ⟨Hf, %Hk⟩
  obtain ⟨k, Hfk, Hlt⟩ := Hk
  have hok : ∀ en : Bool, auth.stepOk E.authMode hs (auth.stepOf (auth.authEnableF en)) :=
    fun en => hM ▸ auth.stepOk_of_fuel γa hs _ k (auth.stepSmall_authEnable en) Hfk Hlt
  have hon : E.authMode.isOn = true := by rw [hM]; rfl
  iapply (h E W p log Pre Q Post info hs hon hok) $$ [Ho HW Hpre]
  · rw [hM]; iframe; iframe #
  iintro !> %resp %err ⟨Hpost, #He, HW, %en, #Hv, Hout⟩
  rw [hM] at *
  ihave Hout := auth.adminOut_fu γa hs _ _ err (auth.stepSmall_authEnable en) $$ [Hf Hout]
  · iframe
  iapply HΦ
  iframe; iframe #

end proof

end apply
end EtcdGrove
end Perennial
