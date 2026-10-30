/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__isWatchPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__recvLoopLemmas

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- An auth info's fields (`authInfoIs`) are its struct points-to, read-only (as
`EtcdServer__doSerialize.lean`'s `authInfoIs_ptsto`). -/
theorem v3rpc.authInfoIs_ptsto' (a : Loc) (user : GoString) (rev : w64) :
    authInfoIs (GF := GF) a user rev ⊢
      a ↦□ ({ Username' := user, Revision' := rev } : go_etcd_io.etcd.server.v3.auth.AuthInfo) := by
  iunfold authInfoIs
  iintro ⟨%Hn, #Hu, #Hr⟩
  rw [typedPointsto_unseal_eq a]
  isplitl
  · simp only [typedPointstoDef]
    iframe Hu Hr
  · ipureintro; exact Hn

/-- One proof for both modes (the auth-mode merge, 2026-10-29: the former `wp_proof` and
(`isWatchPermitted_bound`): the binding under the mode's gate). -/
theorem v3rpc.serverWatchStream.isWatchPermitted.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.isWatchPermitted.spec (GF := GF) (hG := hG) := by
  intro sws r wcr ks es k e dk de n
  wp_start as ⟨#Hs, HRD, #HaLb, #Hpub, Hk, #Hks, He, #Hes, %Hkl⟩
  iunfold v3rpc.swsIs at Hs
  icases Hs with ⟨%Hnn, -, -, -, -, -, -, #Hag, #Hst, -, -, -, -, -, -, #Hok, #Hstr, -⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨-, -, -, ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hreqb, #Hcca, #Has2⟩, -⟩
  iunfold v3rpc.srvStreamIs at Hstr
  icases Hstr with ⟨%si, %Hsi, -, -, #Hctx, #Hic, -⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  iunfold apply.isAuthStore at Has2
  icases Has2 with ⟨%ai, %Hai, -, #HIRP, -⟩
  subst Hai
  -- the store's range check, with auth on at the bound `n` (`srvAuthLb`)
  ihave #HRC := v3rpc.srvRangeCheckFrom r.srv.s r.srv.E ai n $$ [$Has $HaLb $Hpub $HIRP]
  (try wp_auto)
  rw [Hsi]
  (try wp_auto)
  wp_apply Hctx
  (try wp_auto)
  wp_apply (hAI r.srv.s _ r.srv.E.RD r.srv.E.authMode cca
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
  ihave %Hksl := ownSlice_len _ _ _ $$ Hks
  iunfold authInfoOpt at Ha
  icases Ha with (%Han | ⟨%user, %rev, #Hau⟩)
  · subst Han
    (try wp_auto)
    wp_apply (hAS r.srv.s _)
    · iframe #
    (try iintro -)
    (try wp_auto)
    wp_apply HRC $$ [$«$r0» $HRD] as %err2 ⟨-, -, -, HRD, #Herr2a, #Hv⟩
    · iframe #
      ipureintro; word
    ihave #Herr2 := authApplyErrIs_apply err2 $$ Herr2a
    (try wp_auto)
    iapply HΦ
    iframe
    iframe #
    iintro %h
    subst h
    iexists _
    isplitl
    · iapply Hv; ipureintro; rfl
    iintro !> -
    iunfold principalBoundI
    ileft; ipureintro; rfl
  · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
    ihave #Hpb := principalBound_of_ctxBoundOrTLS_gate r.srv.s r.srv.E.authMode (GoInterface.ok r.ci) a user rev $$ [$Hb $Hau]
    iunfold authInfoIs at Hau
    icases Hau with ⟨%Hann, -, -⟩
    (try wp_auto)
    rw [_root_.decide_eq_false Hann]
    (try wp_auto)
    wp_apply (hAS r.srv.s _)
    · iframe #
    (try iintro -)
    (try wp_auto)
    wp_apply HRC $$ [$Hap $HRD] as %err2 ⟨-, -, -, HRD, #Herr2a, #Hv⟩
    · iframe #
      ipureintro; word
    ihave #Herr2 := authApplyErrIs_apply err2 $$ Herr2a
    (try wp_auto)
    iapply HΦ
    iframe
    iframe #
    iintro %h
    subst h
    iexists _
    isplitl
    · iapply Hv; ipureintro; rfl
    iintro !> %h
    iunfold principalBoundI
    iright; iapply Hpb; ipureintro; exact h

end proof

end EtcdGrove
end Perennial
