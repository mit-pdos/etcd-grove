/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__syncVictimsLoop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__moveVictims

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.wsWg_mask_victims : (↑mvcc.wsWgWGN : CoPset) ⊆ ⊤ \ ↑mvcc.wsWgN := by
  unfold mvcc.wsWgWGN mvcc.wsWgN
  exact sync.wg_mask_ndot_ne nroot "mvccWaitGroup" "mvccWgCounter" (by decide)

/-- `s.wg.Done()` with a done token. -/
theorem mvcc.wp_wsDone_victims (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ mvcc.wsDone s }}
      (App (Val (mvcc.wsWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, Hd⟩ HΦ
  iunfold mvcc.wsDone at Hd
  icases Hd with ⟨%γwg, %γd, #Hwg, #Hinv, Htok⟩
  iapply sync.WaitGroup.wp_Done (mvcc.wsWgAddr s) γwg mvcc.wsWgWGN $$ [] [Htok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro mvcc.wsWg_mask_victims
  iintro Hmask
  inext
  iunfold mvcc.wsWgInv at Hi
  icases Hi with ⟨%ctr, %n, Hwgo, Hauth, %Hctr⟩
  icombine Hauth Htok gives %Hle
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γd n' $$ Hauth Htok with Hauth
  imod Hclose $$ [Hwgo Hauth] with -
  · inext
    iunfold mvcc.wsWgInv
    iexists ctr - W32 1, n'
    iframe
    ipureintro
    have : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
    omega
  imodintro
  iapply HΦ
  itrivial

theorem mvcc.watchableStore.syncVictimsLoop.wp_proof
    (hMove : mvcc.watchableStore.moveVictims.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.syncVictimsLoop.spec (GF := GF) (hG := hG) := by
  intro s st γ
  wp_start as ⟨#Hws, HR, Hdone⟩
  ihave #Hws0 := Hws
  iunfold mvcc.isWatchableStore at Hws0
  iNamedSuffix Hws0 "W"
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_for
  wp_for
  wp_apply hMove $$ [$Hws $HR] as %moved HR
  split
  · wp_auto
    wp_for_post
    iframe
  split
  rotate_left
  · exfalso
    rename_i h1 h2
    revert h1 h2
    generalize (!decide (moved = W64 0)) = b
    cases b <;> simp
  wp_auto
  iunfold mvcc.watchReader at HR
  icases HR with ⟨Hsr0, Hmur⟩
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hmur] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.watchStoreInv s γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.watchStoreInv at HP
  icases HP with ⟨%σ, HP⟩
  iunfold mvcc.watchStoreBody at HP
  iNamed HP
  wp_auto
  ihave HP : mvcc.watchStoreBody s γ sync.rfrac σ $$
      [Hσ Hwlog Hsynced Hunsynced Hvf Hvs Hvcap Hvbs Hst Hwo Hmeta Hmem]
  · iunfold mvcc.watchStoreBody; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hvlen, Hok⟩
  wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hmur
  · iframe #; inext; iunfold mvcc.watchStoreInv; iexists σ; iexact HP
  wp_auto_lc 2
  wp_join iprop(∃ tc : Loc, tickc_ptr ↦ tc ∗ (⌜tc = chan.nil⌝ ∨
      ∃ γt : ChanNames, isChanBag γt tc (V := time.Time) (fun _ => iprop(True)))) with [tickc]
    as ⟨%tc, tickc, Htc⟩
  · iexists _; iframe; ileft; ipureintro; rfl
  · wp_apply time.wp_After as %ch %γt #Hbag
    wp_join_done
    iexists ch; iframe; iright; iexists γt; iexact Hbag
  ihave #Hstop := HstopW
  iunfold mvcc.isStopChan at Hstop
  icases Hstop with ⟨%γs, #Hstop⟩
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · icases Htc with (%Hnil | ⟨%γt, #Hbag⟩)
    · iright
      iapply chan.nilClausePre_recv time.Time _ _ Hnil
    ileft
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tc, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tm -
    wp_auto
    wp_for_post
    iframe
    simp only [named]
    iunfold mvcc.watchReader
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, vc, γv
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HvcbW
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] HvcbW
    inext
    iintro %u -
    wp_auto
    wp_for_post
    iframe
    simp only [named]
    iunfold mvcc.watchReader
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstop
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstop
    iintro -
    wp_auto
    wp_for_post
    wp_apply mvcc.wp_wsDone_victims s $$ [$Hsync $Hdone]
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
