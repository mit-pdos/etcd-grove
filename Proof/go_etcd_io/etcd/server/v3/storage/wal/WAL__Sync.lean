/-
`(*WAL).Sync` over `sync` (`w.mu.Lock(); defer w.mu.Unlock(); return w.sync()`; the lock since the
fork's 0006, 2026-11-15, issues/etcd-wal-sync-releaselockto-race.md). One proof since wal-link L1a
(2026-11-17, `notes/wal-link-scope.md` §8; the former `wp_proof` and `wp_proofNoErr` merged): after the lock
the share gives the handle (`walOpenWS_acquire`); the caller's `walLenLb w dir n` is at most the handle's
history (`walHandleIn_lenLb`), so `sync`'s `walSyncedLb dir |H|` gives `walSyncedLb dir n`; before the
unlock the handle goes back (`walOpenWS_release`), or, after an error, the whole share is spent
(`walOpenWS_finish`). The callee `sync` still has two specs (`sync.spec`, `sync.specNoErr`; its family is
left for the queued cleanup), so the proof chooses at the call by whether `Sio` covers every inode.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncNoErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_syncNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specNoErr (Sio := Sio) (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.spec (Sio := Sio) (W := W) P Mr := by
  intro R jr r w dir γ q n
  wp_start as ⟨#Harea, Hw, %hq, #Hn⟩
  icases walOpenWS_pers Sio P Mr w dir γ q $$ Hw with ⟨Hw, #Hpers⟩
  icases walShPers_facts Sio P Mr w dir γ $$ Hpers with ⟨#Hmu, #Hsync, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 1) sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  iapply fupd_wp
  imod walOpenWS_acquire Sio P Mr w dir γ q $$ [Hw Hlocked Hlc1] with ⟨-, Hheld, Hh⟩
  · iframe Hw Hlocked Hlc1
  imodintro
  icases walHdl_open Sio P Mr w dir γ.inc $$ Hh with ⟨%h, Hh, %hD, %hmd, Hr, %hroom, %hinc⟩
  by_cases hc : walCov Sio
  · -- every inode covered: no error, the room kept
    iapply (wp_notCrashed_acc _ _ rfl)
    iintro Hnc
    imod walHandleIn_lenLb walCodec Mr R jr r P ⊤ CoPset.subseteq_top w dir h n TailMetaW $$ Harea Hnc Hh Hn
      with ⟨Hnc, Hh, %hn⟩
    imodintro
    iframe Hnc
    (try wp_auto)
    wp_apply (wp_syncNE hc R jr r w dir h hD.1 (by have := hroom hc; omega)) $$ [Hh] as %err Hpost
    · iframe Harea Hh
    icases Hpost with ⟨%Herr, Hh, #Hs⟩
    iapply fupd_wp
    imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hh Hr] with ⟨Hw, Hlocked⟩
    · iframe Hpers Hheld
      iapply walHdl_close Sio P Mr w dir
        { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
        hD hmd (fun _ => by simp only [List.length_append, List.length_nil]; have := hroom hc; omega)
      ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
      iframe Hh Hr
    imodintro
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    ileft
    iframe Hw
    isplitr
    · ipureintro; exact Herr
    · iapply (WalFs.walSyncedLb_mono (W := W) dir h.H.length n hn) $$ Hs
  · -- some inode not covered: `sync.spec`, its error arm with the whole share
    iapply (wp_notCrashed_acc _ _ rfl)
    iintro Hnc
    imod walHandleIn_lenLb walCodec Mr R jr r P ⊤ CoPset.subseteq_top w dir h n TailMetaW $$ Harea Hnc Hh Hn
      with ⟨Hnc, Hh, %hn⟩
    imodintro
    iframe Hnc
    (try wp_auto)
    wp_apply (wp_sync R jr r w dir h hD.1) $$ [Hh] as %err Hpost
    · iframe Harea Hh
    icases Hpost with (⟨%Herr, Hh, #Hs⟩ | %Herr)
    · iapply fupd_wp
      imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hh Hr] with ⟨Hw, Hlocked⟩
      · iframe Hpers Hheld
        iapply walHdl_close Sio P Mr w dir
          { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
          hD hmd (fun h => absurd h hc)
        ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
        iframe Hh Hr
      imodintro
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      ileft
      iframe Hw
      isplitr
      · ipureintro; exact Herr
      · iapply (WalFs.walSyncedLb_mono (W := W) dir h.H.length n hn) $$ Hs
    · have hq1 : q = 1 := hq.resolve_left hc
      subst hq1
      iapply fupd_wp
      imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
      · iframe Hpers Hheld
      imodintro
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      iright
      ipureintro; exact ⟨Herr, hc⟩

end proof

end EtcdGrove
end Perennial
