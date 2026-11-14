/-
`(*WAL).Save` over its callees: `sync`, `saveEntry`, `saveState`, `cut` (their specs, hypotheses until
proved: `saveEntry`/`saveState`/`sync` wait for writes past the tail's preallocated size), the laws of
the client's raft messages (`WalPbIn.IsEmptyLaw`, `WalPbIn.MustSyncLaw`, `WalPbIn.ZeroLaw`: the part
cannot import the main tree's raft specs, plan §10), `WAL.tail`, and Perennial's `Mutex`. The update
commits at the call's first step (`walHandleIn_append`); then (S/wal.go:1093-1135): the lock, the
shortcut (an empty state and no entries: nothing written, the committed handle quiescent already), the
nil states replaced by fresh zero ones (`ZeroLaw`), `MustSync`, the entries' records (the loop's
invariant `SaveSt`, `SavePure.lean`), the state's, the tail's offset (`Seek`, always the encoder's
offset), then `sync` if `MustSync` and the tail is below `SegmentSizeBytes`, `cut` if it is not
(its pipeline bound from a step's receipt and the handle's, `walPc_bound`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cut
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveState
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SavePure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import LinuxFs.Proof.os.Off
public import Perennial.Proof.sync.Results
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.wp_proof [os.file.FieldAssumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_sync : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.spec (W := W) P Mr)
    (wp_saveEntry : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveEntry.spec (W := W) P Mr)
    (wp_saveState : go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr)
    (wp_cut : go_etcd_io.etcd.server.v3.storage.wal.WAL.cut.spec (W := W) P Mr)
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_empty : WalPbIn.IsEmptyLaw (GF := GF) (hG := hG) P)
    (wp_mustSync : WalPbIn.MustSyncLaw (GF := GF) (hG := hG) P)
    (hzero : WalPbIn.ZeroLaw (GF := GF) (hG := hG) P) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Save.spec (W := W) P Mr := by
  intro R jr r w dir hp hs sl esL es sized Q
  wp_start as ⟨#Harea, Hw, #Hhs, #Hsl, Hes, %hidx, %hsz, Hau⟩
  icases (walOpenWF_iff P Mr w dir).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr⟩
  ihave %hS := walAreaOk_encState walCodec Mr R jr r $$ Harea
  icases walHandleIn_idx P Mr w dir h $$ Hh with ⟨Hh, %hix⟩
  icases walHandleIn_lockFacts P Mr w dir h $$ Hh with ⟨Hh, #Hmu, #Hsync, #Hseg⟩
  have hix0 := hix.1 hD.1
  -- the commit, before the call's first step
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walHandleIn_append P Mr R jr r w dir h (WalOpG.save hs es).toRaw sized Q hD.1
    (saveOp_fit Mr hs es (hS hs) hsz) (fun a b => saveOp_idx Mr h.H hs es _ _ a b)
    $$ Harea Hnc Hh Hau with ⟨Hnc, Hh, #Hlb, HQ, %hcp⟩
  imodintro
  iframe Hnc
  have hcut : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => by
    rcases hcp.1 b hb with h0 | ⟨_, _, h1, _⟩
    · omega
    · have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
  have hs0 := SaveSt.init Mr h hs es
  generalize ({ h with H := h.H ++ [(WalOpG.save hs es).toRaw], rest := (opDs Mr (WalOpG.save hs es).toRaw.toM).length } : WalHS) = h1 at hs0 ⊢
  ihave %hlen := ownSlice_len $$ Hsl
  ihave %hlen2 : ⌜esL.length = es.length⌝ $$ [Hes]
  · iunfold walEntsIn at Hes
    iapply big_sepL2_length $$ Hes
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  sorry

end proof

end EtcdGrove
end Perennial
