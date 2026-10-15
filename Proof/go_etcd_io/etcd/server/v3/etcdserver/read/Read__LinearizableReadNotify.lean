/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/Read__LinearizableReadNotify.lean`.
Lean-first (no Rocq counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__LinearizableReadNotify
public import Spec.context.ErrDone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

set_option hygiene false in
/-- The notifier's case of the final `select`: its close tells `notified`. -/
local macro "notify_nc_clause" : tactic => `(tactic| (
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply ownBroadcastChan_is_chan $$ Hbc
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
  iintro ⟨#HQ, -⟩
  iunfold notified at HQ
  icases HQ with ⟨%err, #He, #HerrE, #Hor⟩
  icases Hor with (%Hne | #Hfz)
  · wp_auto
    iapply HΦ; iunfold readReader; iframe Hrr HerrE; iintro %h; exact absurd h Hne
  · imod read_frozenOk_readIndexOk γn γr c $$ Hfz Hlb with #Hok
    wp_auto
    iapply HΦ; iunfold readReader; iframe Hrr HerrE; iintro -; iexact Hok))

set_option hygiene false in
/-- The server's `Done()` case of the final `select`: `ErrStopped`. -/
local macro "notify_done_clause" : tactic => `(tactic| (
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chS, γS
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply ownBroadcastChan_is_chan $$ HchS
  iapply broadcast_chan_receive _ _ _ _ _ $$ HchS
  iintro ⟨-, -⟩
  ihave ⟨%eS, #HeS, #HaS⟩ := errVarLeaf_get _ $$ HStop
  wp_auto
  iapply HΦ; iunfold readReader; iframe Hrr HaS; iintro %h; cases h))

theorem read.Read.LinearizableReadNotify.wp_proof
    (hED : context.ErrDone.spec (GF := GF) (hG := hG)) :
    read.Read.LinearizableReadNotify.spec (GF := GF) (hG := hG) := by
  intro r γr ctx cd c
  wp_start as ⟨#Hpre, #Hctx, #Hc, Hrr⟩
  iunfold isReadPre at Hpre
  icases Hpre with ⟨%srv, %wc, %γw, #Hsf, #Hdone, #Hwcf, #Hbag, #Hinv⟩
  iunfold readReader at Hrr
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.RWMutex.wp_RLock (readMuAddr r) (readMuP r γr) $$ [Hrr] as ⟨Hrl, HP⟩
  · iframe #; iexact Hrr
  iunfold readMuP at HP
  icases HP with ⟨%nc, %γn, Hpt, Hg⟩
  wp_auto_lc 3
  imod read_deposit γr _ nc γn c $$ Hinv Hlc1 Hg Hc with ⟨Hg, #Hnis, #Hlb⟩
  wp_apply sync.RWMutex.wp_RUnlock (readMuAddr r) (readMuP r γr) $$ [Hrl Hpt Hg] as Hrr
  · iframe #; iframe Hrl; iunfold readMuP; iexists nc, γn; iframe Hpt Hg
  wp_join iprop(r_ptr ↦ r ∗ ctx_ptr ↦ GoInterface.ok ctx ∗ nc_ptr ↦ nc ∗
      sync.ownRWMutex (readMuAddr r) (readMuP r γr)) at next with [r ctx nc Hrr Hlc2 Hlc3]
    as ⟨r, ctx, nc, Hrr⟩
  · wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.nonblockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, wc, γw, ()
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        isplitr
        · iapply is_bag_is_chan $$ Hbag
        iapply blocking_send_implies_nonblocking
        iapply bag_send_au γw wc _ () _ $$ [$Hlc2 $Hlc3] Hbag []
        · itrivial
        inext
        wp_auto
        wp_join_done
      · iapply BigAndL.bigAndL_nil.2; itrivial
    · wp_auto
      wp_join_done
  iunfold notifierIs at Hnis
  icases Hnis with ⟨%ch, #Hcf, #Hbc⟩
  iunfold bcastChan at Hbc
  icases Hbc with ⟨%γc, #Hbc⟩
  iunfold srvDoneOk at Hdone
  icases Hdone with ⟨%si, %Hsi, #HD⟩
  subst Hsi
  iunfold srvChanOk at HD
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, #HStop, -, -, -, #HCan, #HDE⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  iunfold mvcc.txnCtx at Hctx
  icases Hctx with (#Hnil | #Hcctx)
  · -- a context whose `Done()` is `nil`: never done
    iunfold mvcc.doneNil at Hnil
    wp_apply Hnil
    wp_apply HD as %chS #HchS
    iunfold bcastChan at HchS
    icases HchS with ⟨%γS, #HchS⟩
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft; notify_nc_clause
    iapply BigAndL.bigAndL_cons.2
    isplit
    · iright; iapply chan.nilClausePre_recv Unit _ _ rfl
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft; notify_done_clause
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · ihave #Hcctx' := Hcctx
    iNamed Hcctx'
    wp_apply HDone as %chD %γD #HcD
    wp_apply HD as %chS #HchS
    iunfold bcastChan at HchS
    icases HchS with ⟨%γS, #HchS⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · notify_nc_clause
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the context done: its error
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chD, γD
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply context.isContextDone_is_chan $$ HcD
      iapply context.isContextDone_receive _ _ _ _ $$ HcD
      iintro ⟨#HPD, #HCC⟩
      wp_auto
      wp_apply hED ctx cd $$ [HCC] as %cerr ⟨%Htyped, #Hcv⟩
      · iframe #
      cases cerr with
      | nil => exact absurd Htyped (by simp [context.isTypedErr])
      | ok ce =>
        icases Hcv with (#Hcv | #Hcv)
        · ihave #Ha := errVar_applyErrIs _ (GoInterface.ok ce) $$ HCan
          ihave #Ha' : applyErrIs (GF := GF) (GoInterface.ok ce) $$ []
          · iapply Ha; iexists ce; iframe Hcv; ipureintro; rfl
          iapply HΦ; iunfold readReader; iframe Hrr Ha'; iintro %h; cases h
        · icases HDE with ⟨%eD, #HeD, %HDl, #HDm⟩
          icombine Hcv HeD gives %Hce
          cases Hce
          obtain ⟨hl, hIs, hty, hkey⟩ := HDl
          ihave #Ha := applyErrIs_valLeaf _ hl hIs hty hkey $$ HDm
          iapply HΦ; iunfold readReader; iframe Hrr Ha; iintro %h; cases h
    iapply BigAndL.bigAndL_cons.2
    isplit
    · notify_done_clause
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
