/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__CloseLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.Close.wp_proof
    (hClose : mvcc.store.Close.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Close.spec (GF := GF) (hG := hG) := by
  intro s st γ c
  wp_start as ⟨#Hws, Hcl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  icases mvcc.wsCloserM_close s st γ.st c $$ Hcl with ⟨%stc, #Hstc, Hstop, Hwait, Hsc⟩
  iunfold mvcc.stopCloser at Hstop
  icases Hstop with ⟨%γc, Hstop⟩
  iunfold mvcc.wsWaiter at Hwait
  icases Hwait with ⟨%γwg, %γd, %γw, #HisWg, #Hinv, Hwt, Hγw⟩
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
  wp_apply mvcc.wp_wsWg_Wait s st γ.st γwg γd γw $$ [$Htok $Hγw] as Hrds
  · iframe #
  (try wp_auto)
  wp_apply hClose st γ.st c $$ [$Hsc] as ⟨Hjob, Hlc, Hcur⟩
  · iframe #
  iapply HΦ
  iframe Hrds Hjob Hlc Hcur

end proof

end EtcdGrove
end Perennial
