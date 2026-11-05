/-
Proof of the spec of the same name: `WatchStream.RequestProgress.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).

The store's reader slot is borrowed from the handle's pool with the thread token.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgress
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamHandle

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

theorem mvcc.watchStream.RequestProgress.wp_proof :
    mvcc.watchStream.RequestProgress.spec (GF := GF) (hG := hG) := by
  intro w γ ι id
  wp_start as ⟨Hws, Htt⟩
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %γp, %hι, #Hinv, #Hws, #Htp, #Hrp, #Hpf⟩
  obtain ⟨hι, hγ⟩ := hι
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto_lc 1
  iapply fupd_wp
  imod threadPool.borrow_lc mvcc.watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full)
    $$ [$Hlc1 $Hrp $Htt] with ⟨HPR, Hloan⟩
  imodintro
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  have hwi : wi = ⟨go.GoType.PointerType watchableStore.ty, #s⟩ := by
    simp only [interface.mkOk, GoInterface.ok.injEq] at hwa; exact hwa.symm
  subst hwi
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hwm] as Hwm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hacl Hcl]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, closed, cm, wm, CM, WM
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hnn⟩
  cases hk : WM !! id with
  | none =>
    iapply fupd_wp
    imod threadPool.giveBack mvcc.watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full)
      $$ [$Hrp $Hloan $HPR] with Htt
    imodintro
    wp_auto
    iapply HΦ
    iframe Htt
  | some w0 =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    ihave HPR : (mvcc.storeWatchParams s st γw).R $$ [HPR]
    · simp only [mvcc.storeWatchParams]; iexact HPR
    iapply wp_fupd
    wp_apply Hprog $$ [Hws $HPR] as HPR
    · icases Hws $$ %id %w0 %hk with ⟨$, -⟩
    simp only [mvcc.storeWatchParams]
    imod threadPool.giveBack mvcc.watchRdPoolN γp _ ⊤ (fun _ _ => CoPset.mem_full)
      $$ [$Hrp $Hloan $HPR] with Htt
    imodintro
    iapply HΦ
    iframe Htt

end proof

end EtcdGrove
end Perennial
