/-
The proof of `encoder.encode.specTail` (`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/encoder__encodeTail.lean`):
`encoder.encode.specG` over the tail's writer past the size (`wal.tailWriterW`, `TailWriterW.lean`), its state
`walTailWS` (the size `max sz (o0 + |out|)`), its guard `tailOkW` (the stream's end below 2^62: the encoder's
pending bytes at most its page writer's buffer, the frame below 2^48). W6 of `notes/wal-fsext-plan.md`, twenty-fifth
session; Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailWriterW

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

/-- **The encoder's pending bytes are at most its page writer's buffer** (`2 * wmBytes`: the buffer is
the watermark and a page). -/
theorem ownEncoder_pend_le (e : Loc) (wi : GoInterfaceOk) (c : w32) (pend : List w8) :
    ownEncoder (GF := GF) e wi c pend ⊢ ⌜pend.length ≤ 262144⌝ ∗ ownEncoder (GF := GF) e wi c pend := by
  refine (BI.and_intro ?_ .rfl).trans persistent_and_sep_mp
  unfold ownEncoder ioutil.ownPageWriter
  iintro ⟨%pw, %h, %b, %u, %bs, %us, -, -, ⟨%v, %bs', -, -, %hv⟩, -⟩
  ipureintro
  obtain ⟨-, -, hok, rfl⟩ := hv
  obtain ⟨-, h2, -, -, -, -, -, h8⟩ := hok
  rw [show ioutil.wmBytes = 131072 from rfl] at h2 h8
  rw [List.length_take]
  omega

/-- The frame of a record of protobuf size below 2^47 is below 2^48. -/
theorem frame_walRecEnc_lt (x : WalRec) (h : recSize (recOf x) < 2 ^ 47) :
    (frame (walRecEnc x)).length < 2 ^ 48 := by
  rw [frame_length, walRecEnc, recEnc_length]
  have := framePad_lt (recSize (recOf x))
  omega

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.wp_proofTail [os.file.FieldAssumptions]
    (Mr : WalMarshal)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr := by
  intro R jr r e f fd name dir γ i H md cuts o0 sz out pend c rp t d hrs hpre hosz hsz
  iintro %Φ ⟨#Harea, #Henv, Henc, HW, Hrec⟩ HΦ
  icases ownEncoder_pend_le e (wal.fileWi f) c pend $$ Henc with ⟨%hpl, Henc⟩
  have hfr := frame_walRecEnc_lt ⟨t, hash.crc32.crc32c c d, d⟩ hrs
  have hok : tailOkW Mr H md cuts o0 (out ++ pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c c d, d⟩)) := by
    refine ⟨hpre, ?_⟩
    simp only [List.length_append]
    omega
  ihave #Hwr := wal.tailWriterW (W := W) Mr R jr r f fd name dir γ i H md cuts o0 sz $$ Harea
  ihave #Hsp := wp_encode e (wal.fileWi f) (walTailWS (W := W) f fd name dir γ i H md cuts o0 sz)
    (fun _ _ => iprop(True)) (tailOkW Mr H md cuts o0) out pend c rp t d hrs
    (fun _ _ hp hy => tailOkW_prefix hp hy) hok $$ Hwr
  wp_apply Hsp $$ [Henc HW Hrec] as %err ⟨%pend', Henc, Hro, Hres⟩
  · iframe Henv Henc Hrec
    iunfold walTailWS
    rw [Nat.max_eq_left hosz]
    iframe HW
    ipureintro; exact Nat.le_trans hosz (Nat.le_max_left _ _)
  iapply HΦ
  iexists pend'
  iframe Henc Hro
  icases Hres with (⟨%ys, %hys, HW⟩ | ⟨%a, %b, %hab, -⟩)
  · ileft
    iunfold walTailWS at HW
    icases HW with ⟨HW, %hb⟩
    iexists (out ++ ys), max sz (o0 + (out ++ ys).length)
    iframe HW
    ipureintro
    refine ⟨hys.1, by rw [List.append_assoc, hys.2, List.append_assoc], Nat.le_max_right _ _, ?_⟩
    have : maxBytes = 0xffffffff000 := rfl
    omega
  · iright
    ipureintro; exact hab.1

end proof

end EtcdGrove
end Perennial
