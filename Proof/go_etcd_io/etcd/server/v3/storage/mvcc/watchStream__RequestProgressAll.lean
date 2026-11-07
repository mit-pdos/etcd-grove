/-
Proof of the spec of the same name: `WatchStream.RequestProgressAll.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).

The store's reader slot is borrowed from the handle's pool with the reader token; the channel's
progress fact is the handle's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgressAll
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

theorem mvcc.watchStream.RequestProgressAll.wp_proof :
    mvcc.watchStream.RequestProgressAll.spec (GF := GF) (hG := hG) := by
  intro w γ ι
  wp_start as ⟨Hws, Hrt⟩
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %hι, #Hinv, #Hws, #Htp, #Hrp, #Hpf⟩
  obtain ⟨hι, hγ⟩ := hι
  generalize hch : (ι : api.WsAbs).ch = ch at hι
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  wp_auto_lc 1
  iapply fupd_wp
  ihave Hrt : ownToks (GF := GF) γw.st.api.rdk 1 $$ [Hrt]
  · iunfold mvcc.api.mvccReaders at Hrt; (try rw [hγ]); iexact Hrt
  imod mvcc.watchReader_lend s st γw $$ [$Hlc1 $Hrp $Hrt] with ⟨HPR, Hloan⟩
  imodintro
  ihave HPR : (mvcc.storeWatchParams s st γw).R $$ [HPR]
  · simp only [mvcc.storeWatchParams]; iexact HPR
  iapply wp_fupd
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  have hwi : wi = ⟨go.GoType.PointerType watchableStore.ty, #s⟩ := by
    simp only [interface.mkOk, GoInterface.ok.injEq] at hwa; exact hwa.symm
  subst hwi
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  -- what the store is lent (K1b): open, the close right with the registered watchers, each in the
  -- map or cancelled for its reason; closed, every watcher of the map cancelled
  ihave #Hws2 : iprop(□ ∀ (id : w64) (w : Loc), ⌜WM !! id = some w⌝ -∗ (mvcc.storeWatchParams s st γw).IW w ∗ (mvcc.storeWatchParams s st γw).OC w γc) $$ []
  · iintro !> %id %w %h
    icases Hws $$ %id %w %h with ⟨#H1, #H2, -⟩
    iframe H1 H2
  cases closed with
  | true =>
    simp only [↓reduceIte]
    icases Hcl with #Hall
    ihave #Hpa := HprogAll $$ %wm %(DFrac.own 1) %WM %γc %false %ch %([] : List Loc)
    wp_apply Hpa $$ [$Hwm $Hws2 $Hpf $HPR]
      as %b ⟨Hwm, -, HPR⟩
    · iunfold mvcc.progCompl
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro !> %id %w %h
      iapply Hall $$ %id %w %h
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hacl]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, true, cm, wm, CM, WM
      simp only [named, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn⟩
    simp only [mvcc.storeWatchParams]
    imod Hloan $$ HPR with Hrt
    ihave Hrt : mvcc.api.mvccReaders (GF := GF) γ 1 $$ [Hrt]
    · iunfold mvcc.api.mvccReaders; (try rw [← hγ]); iexact Hrt
    imodintro
    iapply HΦ
    iframe Hrt
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hcl with ⟨%L, HCR, #HL, %Hcnt⟩
    ihave #Hpa := HprogAll $$ %wm %(DFrac.own 1) %WM %γc %true %ch %L
    wp_apply Hpa $$ [$Hwm $Hws2 $Hpf $HPR HCR]
      as %b ⟨Hwm, HPC, HPR⟩
    · iunfold mvcc.progCompl
      simp only [↓reduceIte]
      iframe HCR HL
    iunfold mvcc.progCompl at HPC
    simp only [↓reduceIte]
    icases HPC with ⟨HCR, -⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hacl HCR]
    · inext
      iunfold mvcc.watchStreamInv
      iexists nextID, false, cm, wm, CM, WM
      simp only [named, Bool.false_eq_true, ↓reduceIte]
      iframe
      iframe #
      ipureintro; exact ⟨Hdom, Hnn, Hcnt⟩
    simp only [mvcc.storeWatchParams]
    imod Hloan $$ HPR with Hrt
    ihave Hrt : mvcc.api.mvccReaders (GF := GF) γ 1 $$ [Hrt]
    · iunfold mvcc.api.mvccReaders; (try rw [← hγ]); iexact Hrt
    imodintro
    iapply HΦ
    iframe Hrt

end proof

end EtcdGrove
end Perennial
