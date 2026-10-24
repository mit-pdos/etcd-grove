/-
**The token binding at the watch's check** (the auth plan's E1, 2026-10-24; `notes/decisions.md`,
"E1 of the auth plan"). Lean-first (no Rocq counterpart).

`isWatchPermitted` (A1, A4) checks a create request's interval for the auth info the server's
`AuthInfoFromCtx` gives, or the empty one (`&auth.AuthInfo{}`) when there is none. Its bound variant,
over a server whose store has the bound request side (`srvAuthBound`, `etcdserver/AuthBound.lean`),
says moreover that the principal it checked is the anonymous one (empty user), or a user to whom
some token was issued, or that the server's TLS fallback is on (`principalBoundI`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthBound
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__isWatchPermitted

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A checked principal, the anonymous one allowed** (persistent): the empty user (the check's
`&auth.AuthInfo{}` when the request carried none), or a bound one (`principalBound`). The empty user is the zero string (`zeroValDef`). -/
def principalBoundI (s : Loc) (M : auth.AuthMode) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    IProp GF :=
  iprop(⌜info.Username' = (zeroValDef : GoString)⌝ ∨ principalBound s M (some info))

instance principalBoundI_persistent (s : Loc) (M : auth.AuthMode)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    Persistent (principalBoundI (GF := GF) s M info) := by
  unfold principalBoundI; infer_instance

/-- **`isWatchPermitted` with the binding**: its spec, over a server whose store has the bound
request side too, whose passed check's principal is moreover bound (`principalBoundI`). -/
abbrev v3rpc.serverWatchStream.isWatchPermitted.boundSpec : Prop :=
  ∀ (sws : Loc) (r : v3rpc.WRun GF) (wcr : Loc) (ks es : GoSlice) (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.swsIs sws r ∗ srvAuthBound r.srv.s r.srv.E ∗ r.srv.E.RD ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"Key" wcr ↦{dk} ks ∗ ks ↦*□ k ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" wcr ↦{de} es ∗ es ↦*□ e ∗
      ⌜k.length < 2 ^ 63 - 1⌝ }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"isWatchPermitted"))
      (Val #wcr))
  {{ (err : GoInterface), RET #err; r.srv.E.RD ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"Key" wcr ↦{dk} ks ∗
      structFieldRef etcdserverpb.WatchCreateRequest go!"RangeEnd" wcr ↦{de} es ∗
      applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, ∃ info,
        apply.classRes r.srv.E.authMode info [(k, e, auth.PermType.read)] ∗
        principalBoundI r.srv.s r.srv.E.authMode info) }}

theorem v3rpc.serverWatchStream.isWatchPermitted_bound
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.isWatchPermitted.boundSpec (GF := GF) (hG := hG) := by
  intro sws r wcr ks es k e dk de
  wp_start as ⟨#Hs, #Hbd, HRD, Hk, #Hks, He, #Hes, %Hkl⟩
  iunfold v3rpc.swsIs at Hs
  icases Hs with ⟨%Hnn, -, -, -, -, -, -, #Hag, #Hst, -, -, -, -, -, -, #Hok, #Hstr, -⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨-, -, -, ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hcca, #Has2⟩, -⟩
  iunfold srvAuthBound at Hbd
  icases Hbd with ⟨%st3, #Has3, #Hreqb⟩
  icombine Has Has3 gives %Heq3
  subst Heq3
  iunfold v3rpc.srvStreamIs at Hstr
  icases Hstr with ⟨%si, %Hsi, -, -, #Hctx, #Hic, -⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  rw [Hsi]
  (try wp_auto)
  wp_apply Hctx
  (try wp_auto)
  wp_apply (EtcdServer.AuthInfoFromCtx_bound hAS r.srv.s st r.srv.E.RD r.srv.E.authMode cca
      r.ci r.cd) $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hb⟩
  · iframe #
    iunfold mvcc.txnCtx
    iright; iexact Hic
  (try wp_auto)
  rcases err with _ | ei
  · (try wp_auto)
    iapply HΦ
    iframe
    iframe #
    iintro %h; cases h
  (try wp_auto)
  iunfold apply.isAuthStore at Has2
  icases Has2 with ⟨%ai, %Hai, -, #HIRP, -⟩
  iunfold apply.permCheck3 at HIRP
  ihave %Hksl := ownSlice_len _ _ _ $$ Hks
  iunfold authInfoOpt at Ha
  icases Ha with (%Han | ⟨%user, %rev, Hau⟩)
  · subst Han
    (try wp_auto)
    wp_apply (hAS r.srv.s st)
    · iframe #
    subst Hai
    (try wp_auto)
    wp_apply HIRP $$ [$«$r0» $HRD] as %err2 ⟨-, -, -, HRD, #Herr2, -, #Hv⟩
    · iframe #
      ipureintro; word
    (try wp_auto)
    iapply HΦ
    iframe
    iframe #
    iintro %h
    subst h
    iexists _
    isplitl
    · iapply (apply.classRes_of_permVerdict r.srv.E.authMode _ k e .read) $$ Hv
    iunfold principalBoundI
    ileft; ipureintro; rfl
  · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
    ihave #Hpb := principalBound_of_ctxBoundOrTLS r.srv.s r.srv.E.authMode a user rev $$ [$Hb $Hau]
    iunfold authInfoIs at Hau
    icases Hau with ⟨%Hann, -, -⟩
    (try wp_auto)
    rw [_root_.decide_eq_false Hann]
    (try wp_auto)
    wp_apply (hAS r.srv.s st)
    · iframe #
    subst Hai
    (try wp_auto)
    wp_apply HIRP $$ [$Hap $HRD] as %err2 ⟨-, -, -, HRD, #Herr2, -, #Hv⟩
    · iframe #
      ipureintro; word
    (try wp_auto)
    iapply HΦ
    iframe
    iframe #
    iintro %h
    subst h
    iexists _
    isplitl
    · iapply (apply.classRes_of_permVerdict r.srv.E.authMode _ k e .read) $$ Hv
    iunfold principalBoundI
    iright; iexact Hpb

end proof

end EtcdGrove
end Perennial
