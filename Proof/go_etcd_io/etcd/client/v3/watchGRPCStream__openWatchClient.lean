/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__openWatchClient.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__openWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__backoffIfUnavailable
public import Spec.go_etcd_io.etcd.client.v3.isHaltErr
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.watchClient__Watch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.openWatchClient.wp_proof
    (wp_Watch : EtcdGrove.watchClient.Watch.spec (GF := GF) (hG := hG))
    (wp_isHaltErr : isHaltErr.spec (GF := GF) (hG := hG))
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_backoff : watchGRPCStream.backoffIfUnavailable.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.openWatchClient.spec (GF := GF) (hG := hG) := by
  intro V wgs ci cd om callSl vs
  wp_start as ⟨Hlt, #Fctx, #Hctx, #Hom, #Fremote, #Fcall, #Hvs, #Hcall, #Hfacts⟩
  ihave #Hfacts' : watchSrvFacts V $$ [Hfacts]
  · iexact Hfacts
  iunfold watchSrvFacts at Hfacts'
  icases Hfacts' with ⟨#Hstub, #Hconn⟩
  -- (SW1) the registration at one content for every member
  ihave #Hreg := watchConnFacts_regW V $$ Hconn
  iunfold watchConnFacts at Hconn
  icases Hconn with ⟨#Hgc, #Hgs, #Hdesc, -, -, -, #Hcea, #Hvars, -⟩
  iunfold ctxErrClientAllW at Hcea
  ihave #Hce := Hcea $$ %ci %cd Hctx
  ihave #HctxO := metadata.outgoingCtxOkC_of_outMD ci om $$ Hom
  ihave #Hcok := ctxOk_of_isContext ci cd $$ [$Hctx $HctxO]
  wp_auto
  simp only [_root_.Perennial.time.Millisecond]
  try wp_auto
  ihave HI : iprop(∃ (b : w64) (e wsv : GoInterface), "backoff" ∷ backoff_ptr ↦ b ∗
      "err" ∷ err_ptr ↦ e ∗ "ws" ∷ ws_ptr ↦ wsv ∗
      "He" ∷ (⌜e = GoInterface.nil⌝ ∨ ⌜e ≠ GoInterface.nil⌝ ∗ closeErrOk e) ∗ "Hlt" ∷ levelTok 0) $$ [backoff err ws Hlt]
  · iexists _, _, _
    iframe
    ileft; ipureintro; rfl
  wp_for HI
  ihave #Hctx2 := Hctx
  iunfold context.isContext at Hctx2
  iunfold context.isContextDef at Hctx2
  iNamed Hctx2
  wp_apply HDone as %dch %γd #Hdone
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
      iprop((∀ (ws err : GoInterface),
        levelTok 0 ∗ (((⌜err = GoInterface.nil⌝ ∗ ∃ (γs : StreamNames)
          (Dn : GoString → GrpcMd → Nat → v3rpc.WatchRespM → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
          v3rpc.cliWatchStreamIs ws γs (watchUpW V) (watchMdW V om) Dn cd' ∗
          cliSendTok (Req := v3rpc.pbWatchRequest) γs [] ∗
          cliRecvTok (Rep := v3rpc.pbWatchResponse) γs [] ∗
          □ (∀ a md, watchMdW V om a md -∗
            v3rpc.watchSpec (V.memOf a) (V.memWOf a) (auth.mdTokenOf md) γs (Dn a md))) ∨
        (⌜ws = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ closeErrOk err))) -∗ Φ (PairV #ws #err)) ∗
        w_ptr ↦ wgs ∗ backoff_ptr ↦ b ∗ err_ptr ↦ e ∗ ws_ptr ↦ wsv ∗
        (⌜e = GoInterface.nil⌝ ∨ ⌜e ≠ GoInterface.nil⌝ ∗ closeErrOk e) ∗ levelTok 0)
      $$ [] [HΦ w backoff err ws He Hlt] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro ⟨HΦ, w, backoff, err, ws, He, Hlt⟩
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
    isplit
    · iintro ⟨-, #Hcl⟩
      icases He with (%He | ⟨%He, #Hse⟩)
      · subst He
        wp_auto
        iunfold ctxErrClient at Hce
        wp_bind (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #()))
        iapply Hce $$ %Broadcast.Done [] 
        · iexact Hcl
        inext
        iintro %err' %Hne %Hcl' #Hse0 #Hcell' -
        ihave %Hp' := errPtrOk_of_cell _ $$ Hcell'
        ihave #Hse' := closeErrOk_intro _ ⟨fun _ => Hcl', Hp'⟩ $$ Hse0
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Hlt
        iright
        iframe #
        ipureintro; exact ⟨rfl, Hne⟩
      · cases e with
        | nil => exact absurd rfl He
        | ok ei =>
        wp_auto
        wp_for_post
        iapply HΦ
        iframe Hlt
        iright
        iframe #
        ipureintro; exact ⟨rfl, He⟩
    · iframe
  · iframe
  · iintro ⟨HΦ, w, backoff, err, ws, He, Hlt⟩ -
    wp_auto
    wp_apply wp_Watch V.wc V.conn V.addrs V.ics (watchUpW V)
      (fun a md => v3rpc.watchSpec (V.memOf a) (V.memWOf a) (auth.mdTokenOf md)) ci cd om callSl vs $$ [Hlt]
      as %cs %err' ⟨Hlt, Hr⟩
    · iframe #
      iframe Hlt
    icases Hr with (⟨%He', %γs, %Dn, %cd', Hcs, Hst, Hrt, #Hspec⟩ | ⟨%Hcs, #Hse⟩)
    · subst He'
      iunfold v3rpc.cliWatchStreamIs at Hcs
      iunfold cliBidiStreamIs at Hcs
      icases Hcs with ⟨%ci', %Hcs', Hcs⟩
      subst Hcs'
      ihave Hcs : v3rpc.cliWatchStreamIs (GoInterface.ok ci') γs (watchUpW V) (watchMdW V om) Dn
          cd' $$ [Hcs]
      · iunfold v3rpc.cliWatchStreamIs
        iunfold cliBidiStreamIs
        iexists ci'
        isplitr
        · ipureintro; rfl
        iexact Hcs
      wp_auto
      wp_for_post
      iapply HΦ
      iframe Hlt
      ileft
      isplitr
      · ipureintro; rfl
      iexists γs, Dn, cd'
      iframe Hcs Hst Hrt
      iintro !> %a %md ⟨%Ha, #Hmd⟩
      ihave Hs := Hspec $$ %a %md [] Hmd
      · ipureintro; exact Ha
      iexact Hs
    · subst Hcs
      ihave #Hse' := Hse
      iunfold cliStreamErr at Hse'
      icases Hse' with ⟨%Hok, #Hst, -⟩
      ihave #Hsec := cliStreamErr_closeErrOk _ $$ Hse
      ihave %Hpc := closeErrOk_pure _ $$ Hsec
      wp_auto
      wp_apply wp_isHaltErr ci cd err' $$ [] as %bh -
      · iframe #
      cases bh
      · wp_auto
        wp_apply wp_backoff wgs ci cd b err' $$ [] as %d -
        · iframe #
        wp_for_post
        iframe
        iexists d, err', GoInterface.nil
        iframe
        iright
        iframe #
        ipureintro; exact Hok.1
      · wp_auto
        ihave ⟨%mR, #HmR⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hst
        wp_apply wp_rpctypes_Error err' mR $$ [] as %err2 ⟨%Hne2, #Hse20, %Hc2, -, -, %Hq2, -⟩
        · iframe #
          ipureintro; exact Hok.1
        ihave #Hse2 := closeErrOk_intro _ ⟨fun _ => Hc2 Hok.2, Hq2 Hpc.2⟩ $$ Hse20
        wp_for_post
        iapply HΦ
        iframe Hlt
        iright
        iframe #
        ipureintro; exact ⟨rfl, Hne2⟩

end proof

end EtcdGrove
end Perennial
