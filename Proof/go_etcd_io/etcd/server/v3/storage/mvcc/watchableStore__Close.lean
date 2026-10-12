/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas

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

/-- `s.wg.Wait()` by the store's one waiter. -/
theorem mvcc.wp_wsWg_Wait (s : Loc) (γwg : sync.WaitGroupNames) (γd : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (mvcc.wsWgAddr s) γwg mvcc.wsWgWGN ∗
        inv mvcc.wsWgN (mvcc.wsWgInv γwg γd) ∗ sync.ownWaitGroupWaitToken γwg }}
      (App (Val (mvcc.wsWgAddr s @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Wait (mvcc.wsWgAddr s) γwg mvcc.wsWgWGN $$ [Htok] [HΦ]
  · iframe #
    iframe
  iinv Hinv with >Hi Hclose
  · exact mvcc.wsWg_maskN
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold mvcc.wsWgInv at Hi
  icases Hi with ⟨%ctr, %n, Hwgo, Hauth, %Hctr⟩
  iexists ctr
  iframe Hwgo
  iintro %H0 Hwgo
  imod Hmask with -
  imod Hclose $$ [Hwgo Hauth] with -
  · unfold mvcc.wsWgInv
    iexists ctr, n
    iframe
    ipureintro; exact Hctr
  imodintro
  iintro -
  iapply HΦ
  itrivial

theorem mvcc.watchableStore.Close.wp_proof
    (hClose : mvcc.store.Close.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Close.spec (GF := GF) (hG := hG) := by
  intro s st γ
  wp_start as ⟨#Hws, Hcl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  iunfold mvcc.wsCloser at Hcl
  icases Hcl with ⟨%stc, #Hstc, Hstop, Hwait, Hsc⟩
  iunfold mvcc.stopCloser at Hstop
  icases Hstop with ⟨%γc, Hstop⟩
  iunfold mvcc.wsWaiter at Hwait
  icases Hwait with ⟨%γwg, %γd, #HisWg, #Hinv, Hwt⟩
  wp_auto
  wp_apply wp_broadcast_chan_close stc γc iprop(True) $$ [$Hstop] as -
  · imodintro; itrivial
  (try wp_auto)
  iapply fupd_wp
  imod fupd_mask_subseteq (E2 := ↑mvcc.wsWgWGN) CoPset.subseteq_top with Hmask
  imod sync.alloc_wait_token (mvcc.wsWgAddr s) γwg mvcc.wsWgWGN 0 (by decide) $$ HisWg Hwt
    with ⟨-, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply mvcc.wp_wsWg_Wait s γwg γd $$ [$Htok]
  · iframe #
  (try wp_auto)
  wp_apply hClose st γ.st $$ [$Hsc]
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
