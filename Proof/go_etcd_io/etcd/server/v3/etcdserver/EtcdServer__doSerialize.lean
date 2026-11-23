/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__doSerialize.lean`. Lean-first (no
Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthWhy
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- `AuthInfoFromCtx`'s error is the request side's reason (`serialWhy`'s first case). -/
theorem serialWhy_of_ctxErr (s : Loc) (M : auth.AuthMode) (on : Bool) (hon : M.isOn = true → on = true)
    (n : Nat) (tok : Option GoString) (err : GoInterface)
    (R : go_etcd_io.etcd.server.v3.auth.AuthInfo → GoInterface → IProp GF) (herr : err ≠ GoInterface.nil) :
    □ (⌜on = true⌝ → ∀ _ : err ≠ GoInterface.nil,
        auth.authErrOf .invalidAuthToken err ∗ auth.enabledVerdictFrom M n true ∗
          auth.tokRefusedFrom M n tok) ⊢ serialWhy (GF := GF) s M n tok err R := by
  cases M with
  | on γa =>
    iintro #H
    ihave ⟨#Hit, #Hen, #Htk⟩ := H $$ %(hon rfl) %herr
    unfold serialWhy reqSideWhy
    ileft; iframe Hen; iright; iframe Hit Htk
  | _ => iintro -; unfold serialWhy; itrivial

/-- `chk`'s refusal of the auth info the request side gave (`serialWhy`'s second case). -/
theorem serialWhy_of_chk (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (R : go_etcd_io.etcd.server.v3.auth.AuthInfo → GoInterface → IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    □ (⌜M.isOn = true⌝ → infoWhy s M n tok info) ∗ R info err ⊢
      serialWhy (GF := GF) s M n tok err R := by
  cases M with
  | on γa =>
    iintro ⟨#Hi, HR⟩
    ihave #Hi' := Hi $$ %rfl
    unfold serialWhy
    iright; ileft; iexists info; iframe Hi' HR
  | _ => iintro -; unfold serialWhy; itrivial

/-- The revision re-check's refusal (`serialWhy`'s third case): the auth info's non-zero revision,
not the revision read at a state no older than `n`. -/
theorem serialWhy_of_oldRev (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString) (err : GoInterface)
    (R : go_etcd_io.etcd.server.v3.auth.AuthInfo → GoInterface → IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (x : w64) (h0 : info.Revision' ≠ W64 0)
    (hx : info.Revision' ≠ x) :
    □ (⌜M.isOn = true⌝ → ⌜info.Revision' ≠ W64 0⌝ → principalBound (srvTLSId s) M tok (some info) ∗
        (auth.enabledVerdictFrom M n true ∨ srvTLSId s)) ∗
      auth.revisionVerdictFrom M n x ∗ auth.authErrOf .authOldRevision err ⊢
      serialWhy (GF := GF) s M n tok err R := by
  cases M with
  | on γa =>
    iintro ⟨#Hb, #Hv, #He⟩
    ihave ⟨#Hpb, #Hen⟩ := Hb $$ %rfl %h0
    unfold auth.revisionVerdictFrom
    icases Hv with ⟨%j, %st, #Hst, %Hj⟩
    unfold serialWhy oldRevWhy
    iright; iright
    iframe He
    iexists info
    iframe Hpb Hen
    isplitr
    · ipureintro; intro h; apply h0; exact uint_nat_inj _ _ (by rw [h]; rfl)
    · iexists j, st; iframe Hst; ipureintro
      refine ⟨Hj.1, ?_⟩
      rw [← Hj.2]; intro h; exact hx (uint_nat_inj _ _ h.symm)
  | _ => iintro -; unfold serialWhy; itrivial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.doSerialize.wp_proof
    (hGet : traceutil.Get.spec (GF := GF) (hG := hG))
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG)) :
    EtcdServer.doSerialize.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd tok chk get G Q C hC R t e n
  wp_start as ⟨#Hsrv, #Hrd, #HaLb, #Hpub, #Hctx, #Hlib, #HtokC, #Hct, #Hchk, #Hget, HG, Htrc, Hard⟩
  ihave ⟨⟨%v, #Hv⟩, #HsrvB⟩ := (isServerReqM_split _ _ _ _).1 $$ Hsrv
  iunfold srvReqFieldsAtM at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, #Hcca, -, -,
    #Has, #Hras, -, -, -, -, -, -, -, -, -, -⟩
  iunfold isServerReadM at Hrd
  icases Hrd with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, #Has2, #Hauth, -⟩
  ihave #Ptu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  wp_auto
  wp_apply hGet ctx (some t) $$ [$Hct] as %tr ⟨%Htr, %Hteq⟩
  subst tr
  wp_apply EtcdServer.AuthInfoFromCtx.wpMLb E.authOn hAI s E v.auth v.cca ctx cd n tok $$ [Hard]
    as %a %err ⟨Hard, Ha, #HaE, #Hab, #Hz, #Hne, #Hnn⟩
  · iframe; iframe #
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ
    iframe Hard
    iright
    isplitr
    · ipureintro; intro h; cases h
    iframe HaE
    isplitr
    · iapply (serialWhy_of_ctxErr s E.authMode E.authOn (fun h => h) n _ _ R (by intro h; cases h)) $$ Hne
    ileft; iframe HG Htrc
  | nil =>
    wp_auto
    wp_join iprop(∃ (a' : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        ai_ptr ↦ a' ∗ a' ↦{dq} info ∗ infoBoundM E.authOn s E tok info ∗
        □ (⌜E.authMode.isOn = true⌝ → infoWhy s E.authMode n tok info) ∗
        □ (⌜E.authMode.isOn = true⌝ → ⌜info.Revision' ≠ W64 0⌝ →
          principalBound (srvTLSId s) E.authMode tok (some info) ∗
          (auth.enabledVerdictFrom E.authMode n true ∨ srvTLSId s)))
      with [ai Ha] as ⟨%a', %info, %dq, ai, Hai, #Hib, #Hiw, #Hio⟩
    · iexists «$r0_ptr», _, DFrac.own 1
      iframe ai «$r0»
      isplitr
      · iapply infoBoundM_empty; rfl
      isplitr
      · iintro !> %hon
        unfold infoWhy
        ileft
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        · iapply Hz $$ %hon; exact ⟨rfl, rfl⟩
      · iintro !> - %h0; exact absurd rfl h0
    · iunfold authInfoOpt at Ha
      icases Ha with (%Han | ⟨%user, %rev, #Hai0⟩)
      · exact absurd Han Hif
      ihave #Hp := authInfoIs_ptsto a user rev $$ Hai0
      ihave #Hib := infoBoundM_of_ctxBound E.authOn s E _ a user rev $$ [Hab Hai0]
      · iframe Hai0; iintro %h; iapply Hab $$ %h
      iexists a, _, DFrac.discard
      iframe ai Hp Hib
      isplitr
      · iintro !> %hon
        unfold infoWhy
        iright
        iapply principalBound_of_ctxBoundOrTLS s E.authMode _ a user rev
        iframe Hai0; iapply Hab $$ %hon
      · iintro !> %hon -
        isplitr
        · iapply principalBound_of_ctxBoundOrTLS s E.authMode _ a user rev
          iframe Hai0; iapply Hab $$ %hon
        · iapply Hnn $$ %hon %Hif
    wp_bind (App (Val #chk) (Val #a'))
    iapply Hchk $$ [Hai Hard HG]
    · iframe
    inext
    iintro %err' ⟨Hai, Hard, HG, #HcE, HC, HR⟩
    wp_auto
    cases err' with
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Hard
      iright
      isplitr
      · ipureintro; intro h; cases h
      iframe HcE
      isplitl [HR]
      · iapply (serialWhy_of_chk s E.authMode n _ _ R info)
        iframe Hiw
        iapply HR; intro h; cases h
      ileft; iframe HG Htrc
    | nil =>
      wp_auto
      wp_apply hStep t e _ slice.nil $$ [$Htrc] as Htrc
      · iapply traceutil.ownFields_nil
      ihave #HCi := HC $$ %rfl
      wp_bind (App (Val #get) (Val #()))
      iapply Hget $$ [HG Htrc]
      · iframe HG Htrc
        iexists info; iframe HCi Hib
      inext
      iintro HQ
      wp_auto
      iStructNamed Hai
      icombine Has Has2 gives %Heq
      iunfold apply.isAuthStore at Hauth
      icases Hauth with ⟨%ai0, %Hst, -, -, -, -, -, -, #HRev, -⟩
      icases Hinit with ⟨-, ⟨-, -, -, -, ⟨-, -, -, -, -, -, -, #HOld, -⟩⟩, -⟩
      ihave ⟨%eOld, #HeOld, #HaOld⟩ := errVarLeaf_get _ $$ HOld
      ihave #HaOldA : authApplyErrIs (GoInterface.ok eOld) $$ []
      · iapply apply.errVarLeaf_authApplyErrIs _
          (by simp [go_etcd_io.etcd.server.v3.auth.authErrMsgs]) _ $$ HOld
        iexists eOld; iframe HeOld; ipureintro; rfl
      ihave #HaOldE : auth.authErrOf (GF := GF) .authOldRevision (GoInterface.ok eOld) $$ []
      · iunfold auth.authErrOf; iexists eOld; simp only [auth.AuthErr.var]; iframe HeOld
      rw [Heq, Hst]
      ihave #HRevLb := srvAuthLb_revision s E ai0 n $$ [$HaLb $Hpub $HRev]
      · rw [← Hst, ← Heq]; iexact Has
      wp_auto
      wp_if_destruct
      · iapply HΦ
        iframe Hard
        ileft
        iframe HQ
        isplitr
        · ipureintro; rfl
        iexists _; iframe HCi Hib
      · wp_apply HRevLb as %x #Hx
        wp_if_destruct
        · iapply HΦ
          iframe Hard
          ileft
          iframe HQ
          isplitr
          · ipureintro; rfl
          iexists _; iframe HCi Hib
        · iapply HΦ
          iframe Hard
          iright
          isplitr
          · ipureintro; intro h; cases h
          iframe HaOldA
          isplitr
          · iapply (serialWhy_of_oldRev s E.authMode n _ _ R info x ‹_› ‹_›)
            iframe Hio Hx HaOldE
          iright; iexact HQ

end proof

end EtcdGrove
end Perennial
