/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/encoder__encodeTailNoErr.lean`:
`encoder.encode.specGNE` (a writer called only with bytes) over the tail's writer with no error
(`wal.tailWriterWNE`, its broken state false). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTailNoErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriterWNE

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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.wp_proofTailNoErr
    (Mr : WalMarshal)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specGNE (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTailNoErr (Sio := Sio) (W := W) Mr := by
  intro hS0 R jr r e f fd name dir γ i H md cuts o0 sz out pend c rp t d hrs hpre hosz hsz hroom
  iintro %Φ ⟨#Harea, #Henv, Henc, HW, Hrec⟩ HΦ
  icases ownEncoder_pend_le e (wal.fileWi f) c pend $$ Henc with ⟨%hpl, Henc⟩
  have hfr := frame_walRecEnc_lt ⟨t, hash.crc32.crc32c c d, d⟩ hrs
  have hok : tailOkWNE Mr H md cuts o0 (out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)) := by
    refine ⟨⟨hpre, ?_⟩, hroom⟩
    simp only [List.length_append] at hroom ⊢
    have : maxBytes = 0xffffffff000 := rfl
    omega
  ihave #Hwr := wal.tailWriterWNE (W := W) hS0 Mr R jr r f fd name dir γ i H md cuts o0 sz $$ Harea
  ihave #Hsp := wp_encode e (wal.fileWi f) (walTailWS (W := W) f fd name dir γ i H md cuts o0 sz)
    (fun _ _ => iprop(False)) (tailOkWNE Mr H md cuts o0) out pend c rp t d hrs
    (fun _ _ hp hy => tailOkWNE_prefix hp hy) hok $$ Hwr
  wp_apply Hsp $$ [Henc HW Hrec] as %err ⟨%pend', Henc, Hro, Hres⟩
  · iframe Henv Henc Hrec
    iunfold walTailWS
    rw [Nat.max_eq_left hosz]
    iframe HW
    ipureintro; exact Nat.le_trans hosz (Nat.le_max_left _ _)
  iapply HΦ
  iexists pend'
  iframe Henc Hro
  icases Hres with (⟨%ys, %hys, HW⟩ | ⟨%a, %b, %hab, HB⟩)
  · iunfold walTailWS at HW
    icases HW with ⟨HW, %hb⟩
    iexists (out ++ ys), max sz (o0 + (out ++ ys).length)
    iframe HW
    ipureintro
    refine ⟨hys.1, by rw [List.append_assoc, hys.2, List.append_assoc], Nat.le_max_right _ _, ?_⟩
    have : maxBytes = 0xffffffff000 := rfl
    omega
  · iexfalso; iexact HB

end proof

end EtcdGrove
end Perennial
