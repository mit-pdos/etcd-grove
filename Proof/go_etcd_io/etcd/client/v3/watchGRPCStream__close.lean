/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__close.lean` (the watch slice's unit
W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__close
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas

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

theorem watchGRPCStream.close.wp_proof
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.close.spec (GF := GF) (hG := hG) := by
  intro V G callSl
  wp_start as #Hg
  iunfold isWGS at Hg
  icases Hg with ⟨%Hgnn, #Hcv, #Hsf, %Hlg', #Howner, #Hremote, #Hcallo, #Hctx, #Hckey, #Hcancel,
    #Hreqc, #Hrespc, #Hdonec, #Herrc, #Hclosingc, #Hglg, #HisCtx, #Hcspec, #Hbreq, #Hberr, #Hbcl,
    #Hbdone, -⟩
  iunfold watchSrvFacts at Hsf
  icases Hsf with ⟨-, #Hcf⟩
  iunfold watchConnFacts at Hcf
  icases Hcf with ⟨-, -, -, -, #Heof, -, #Hcea, -, -⟩
  iunfold ctxErrClientAllW at Hcea
  ihave #Hce := Hcea $$ %G.ctx %G.cd HisCtx
  iunfold context.cancelSpec at Hcspec
  wp_auto
  wp_bind (App (Val #G.cancel) (Val #()))
  iapply Hcspec
  · itrivial
  inext
  iintro -
  wp_auto
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hbdone
  wp_bind (App (Val (chan.receive _)) (Val #G.donec))
  wp_apply_core chan.wp_receive (V := Unit) G.donec G.γdone $$ Hdcc
  iintro -
  iapply broadcast_chan_receive G.donec G.γdone (closeErrPub G.wgs) _ .Unknown $$ Hbdone
  iintro ⟨-, -⟩
  wp_auto
  ihave #Hech := is_bag_is_chan G.γerr G.errc (errP G.γr G.γep) $$ Hberr
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc, G.γerr
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hech
      unfold nonblockingRecvAu
      isplit
      · iapply bag_nonblocking_recv_au $$ Hberr
        inext
        iintro %e He0
        iunfold errP at He0
        icases He0 with ⟨%Hne, Hor, #Hse, -⟩
        ihave %Hce : ⌜clientErr e⌝ $$ [Hor]
        · icases Hor with (#Hcs | #He)
          · iunfold cliStreamErr at Hcs
            icases Hcs with ⟨%Hc, -, -⟩
            ipureintro; exact Hc.2
          · iunfold eofOk at Heof
            icases Heof $$ %e He with ⟨%Hc, -⟩
            ipureintro; exact Hc.2
        wp_auto
        wp_apply wp_ContextError G.ctx G.cd e $$ [] as %err' ⟨-, #Hse', -⟩
        · iframe #
          ipureintro; intro _; exact Hce
        iapply HΦ; iexact Hse'
      · itrivial
    · iapply BigAndL.bigAndL_nil.2; itrivial
  · wp_auto
    wp_apply wp_ContextError G.ctx G.cd GoInterface.nil $$ [] as %err' ⟨-, #Hse', -⟩
    · iframe #
      isplitr
      · ipureintro; intro h; exact absurd rfl h
      iapply statusErrOk_nil
    iapply HΦ; iexact Hse'

end proof

end EtcdGrove
end Perennial
