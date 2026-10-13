/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__doSerialize.lean`. Lean-first (no
Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions] in
/-- An auth info's fields (`authInfoIs`) are its struct points-to, read-only. -/
theorem authInfoIs_ptsto (a : Loc) (user : GoString) (rev : w64) :
    authInfoIs (GF := GF) a user rev ⊢
      a ↦□ ({ Username' := user, Revision' := rev } : go_etcd_io.etcd.server.v3.auth.AuthInfo) := by
  iunfold authInfoIs
  iintro ⟨%Hn, #Hu, #Hr⟩
  rw [typedPointsto_unseal_eq a]
  isplitl
  · simp only [typedPointstoDef]
    iframe Hu Hr
  · ipureintro; exact Hn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.doSerialize.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG)) :
    EtcdServer.doSerialize.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd chk get G Q
  wp_start as ⟨#Hsrv, #Hrd, #Hctx, #Hchk, #Hget, HG⟩
  iunfold isServerReq at Hsrv
  icases Hsrv with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, #Hcca, -, -,
    #Has, #Hras, -, -, -, -, -, -, -, -, -, -⟩
  iunfold isServerRead at Hrd
  icases Hrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, #Has2, #Hauth, -⟩
  ihave #Ptu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  wp_auto
  wp_apply hGet ctx cd $$ [] as %tr %Htr
  · iframe #
  wp_apply hAI s v.auth v.cca ctx cd $$ [] as %a %err ⟨Ha, #HaE⟩
  · iframe #
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iframe HaE; ileft; iexact HG
  | nil =>
    wp_auto
    wp_join iprop(∃ (a' : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        ai_ptr ↦ a' ∗ a' ↦{dq} info) with [ai Ha] as ⟨%a', %info, %dq, ai, Hai⟩
    · iunfold authInfoOpt at Ha
      icases Ha with (%Han | ⟨%user, %rev, Hai0⟩)
      · exact absurd Han Hif
      ihave #Hp := authInfoIs_ptsto a user rev $$ Hai0
      iexists a, _, DFrac.discard
      iframe ai Hp
    wp_bind (App (Val #chk) (Val #a'))
    iapply Hchk $$ Hai
    inext
    iintro %err' ⟨Hai, #HcE⟩
    wp_auto
    cases err' with
    | ok ei =>
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe HcE; ileft; iexact HG
    | nil =>
      wp_auto
      wp_apply hStep tr _ _ $$ []
      · iframe #; ipureintro; exact Htr
      wp_bind (App (Val #get) (Val #()))
      iapply Hget $$ HG
      inext
      iintro HQ
      wp_auto
      iStructNamed Hai
      icombine Has Has2 gives %Heq
      iunfold apply.isAuthStore at Hauth
      icases Hauth with ⟨%ai0, %Hst, -, -, -, -, -, -, #HRev, -⟩
      icases Hinit with ⟨-, ⟨-, -, -, -, ⟨-, -, -, -, -, -, -, #HOld, -⟩⟩, -⟩
      ihave ⟨%eOld, #HeOld, #HaOld⟩ := errVarLeaf_get _ $$ HOld
      rw [Heq, Hst]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        ileft
        iframe HQ
        ipureintro; rfl
      · wp_apply HRev as %x -
        wp_if_destruct
        · iapply HΦ
          ileft
          iframe HQ
          ipureintro; rfl
        · iapply HΦ
          iright
          isplitr
          · ipureintro; intro h; cases h
          iframe HaOld; iright; iexact HQ

end proof

end EtcdGrove
end Perennial
