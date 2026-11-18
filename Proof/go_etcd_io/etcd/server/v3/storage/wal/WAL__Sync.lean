/-
`(*WAL).Sync` over `sync` (`w.mu.Lock(); defer w.mu.Unlock(); return w.sync()`; the lock since the
fork's 0006, 2026-11-15, issues/etcd-wal-sync-releaselockto-race.md). Proved over the callee's spec:
the handle's mutex (`walHandleIn_lockFacts`, invariant `True`) is taken around `sync`; the caller's
`walLenLb w dir n` is at most the handle's history (`walHandleIn_lenLb`, the invariant opened right
after the lock), so `sync`'s `walSyncedLb dir |H|` gives `walSyncedLb dir n`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.spec (W := W) P Mr := by
  intro R jr r w dir n
  wp_start as ⟨#Harea, Hw, #Hn⟩
  icases (walOpenWF_iff P Mr w dir).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr⟩
  icases walHandleIn_lockFacts P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hmu, #Hsync, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_lenLb walCodec Mr R jr r P ⊤ CoPset.subseteq_top w dir h n TailMetaW $$ Harea Hnc Hh Hn
    with ⟨Hnc, Hh, %hn⟩
  imodintro
  iframe Hnc
  (try wp_auto)
  wp_apply (wp_sync R jr r w dir h hD.1) $$ [Hh] as %err Hpost
  · iframe Harea Hh
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
  (try wp_auto)
  icases Hpost with (⟨%Herr, Hh, #Hs⟩ | %Herr)
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Herr
    isplitl
    · iapply (walOpenWF_iff P Mr w dir).2
      iexists { h with out := h.out ++ h.pend, pend := [], sz := max h.sz (h.o0 + h.out.length + h.pend.length) }
      ihave Hh := walHandleIn_win P Mr w dir _ $$ Hh
      iframe Hh Hr
      ipureintro; exact ⟨hD, hmd⟩
    · iapply (WalFs.walSyncedLb_mono (W := W) dir h.H.length n hn) $$ Hs
  · iapply HΦ
    iright; ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
