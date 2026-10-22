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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  intro V wgs ci cd callSl vs
  wp_start as ⟨#Fctx, #Hctx, #Fremote, #Fcall, #Hvs, #Hcall, #Hfacts⟩
  ihave #Hfacts' : watchSrvFacts V $$ [Hfacts]
  · iexact Hfacts
  iunfold watchSrvFacts at Hfacts'
  icases Hfacts' with ⟨#Hstub, #Hconn⟩
  iunfold watchConnFacts at Hconn
  icases Hconn with ⟨#Hgc, #Hgs, #Hdesc, -, -, -, #Hcea, #Hvars, -⟩
  iunfold ctxErrClientAllW at Hcea
  ihave #Hce := Hcea $$ %ci %cd Hctx
  ihave #Hcok := ctxOk_of_isContext ci cd $$ Hctx
  wp_auto
  simp only [_root_.Perennial.time.Millisecond]
  wp_auto
  ihave HI : iprop(∃ (b : w64) (e wsv : GoInterface), "backoff" ∷ backoff_ptr ↦ b ∗
      "err" ∷ err_ptr ↦ e ∗ "ws" ∷ ws_ptr ↦ wsv ∗
      "He" ∷ (⌜e = GoInterface.nil⌝ ∨ ⌜e ≠ GoInterface.nil⌝ ∗ statusErrOk e)) $$ [backoff err ws]
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
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (i : Nat) (γs : StreamNames)
          (Dn : Nat → v3rpc.WatchRespM → IProp GF) (cd' : context.ContextDesc (IProp GF)),
          ⌜i < V.nm⌝ ∗ v3rpc.cliWatchStreamIs ws γs (v3rpc.watchUp (V.mem i).2.γ) Dn cd' ∗
          cliSendTok (Req := v3rpc.pbWatchRequest) γs [] ∗
          cliRecvTok (Rep := v3rpc.pbWatchResponse) γs [] ∗ v3rpc.watchSpec (V.mem i).2 γs Dn) ∨
        (⌜ws = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ statusErrOk err)) -∗ Φ (PairV #ws #err)) ∗
        w_ptr ↦ wgs ∗ backoff_ptr ↦ b ∗ err_ptr ↦ e ∗ ws_ptr ↦ wsv ∗
        (⌜e = GoInterface.nil⌝ ∨ ⌜e ≠ GoInterface.nil⌝ ∗ statusErrOk e))
      $$ [] [HΦ w backoff err ws He] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro ⟨HΦ, w, backoff, err, ws, He⟩
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
        iintro %err' %Hne %- #Hse'
        wp_auto
        wp_for_post
        iapply HΦ
        iright
        iframe #
        ipureintro; exact ⟨rfl, Hne⟩
      · cases e with
        | nil => exact absurd rfl He
        | ok ei =>
        wp_auto
        wp_for_post
        iapply HΦ
        iright
        iframe #
        ipureintro; exact ⟨rfl, He⟩
    · iframe
  · iframe
  · iintro ⟨HΦ, w, backoff, err, ws, He⟩ -
    wp_auto
    wp_apply wp_Watch V.wc V.conn V.addrs V.ics (fun a => v3rpc.watchUp (V.memOf a).γ)
      (fun a => v3rpc.watchSpec (V.memOf a)) ci cd callSl vs $$ [] as %cs %err' Hr
    · iframe #
    icases Hr with (⟨%He', %a, %γs, %Dn, %cd', %Ha, Hcs, Hst, Hrt, Hspec⟩ | ⟨%Hcs, #Hse⟩)
    · subst He'
      iunfold v3rpc.cliWatchStreamIs at Hcs
      iunfold cliBidiStreamIs at Hcs
      icases Hcs with ⟨%ci', %Hcs', Hcs⟩
      subst Hcs'
      ihave Hcs : v3rpc.cliWatchStreamIs (GoInterface.ok ci') γs (v3rpc.watchUp (V.memOf a).γ) Dn
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
      ileft
      isplitr
      · ipureintro; rfl
      iexists V.idxOf a, γs, Dn, cd'
      iframe
      ipureintro; exact V.idxOf_lt a Ha
    · subst Hcs
      ihave #Hse' := Hse
      iunfold cliStreamErr at Hse'
      icases Hse' with ⟨%Hok, #Hst, -⟩
      wp_auto
      wp_apply wp_isHaltErr ci cd err' $$ [] as %bh %Hbh
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
        wp_apply wp_rpctypes_Error err' $$ [] as %err2 ⟨%Hne2, #Hse2, -⟩
        · iframe #
          ipureintro; exact Hok.1
        wp_for_post
        iapply HΦ
        iright
        iframe #
        ipureintro; exact ⟨rfl, Hne2⟩

end proof

end EtcdGrove
end Perennial
