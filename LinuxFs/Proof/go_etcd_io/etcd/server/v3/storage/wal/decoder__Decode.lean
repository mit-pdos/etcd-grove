/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__Decode.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Reset
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.wp_proof
    (HDecRec : go_etcd_io.etcd.server.v3.storage.wal.decoder.decodeRecord.spec (GF := GF) (hG := hG))
    (HReset : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Reset.spec (GF := GF) (hG := hG))
    (HLock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (HUnlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG) := by
  intro C d rp IoE eof ueof fs off c hC
  wp_start as ⟨#Henv, Hd, Hr⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply HReset $$ Hr as Hr
  iunfold ownDecoder at Hd
  icases Hd with ⟨%sl, %fbrs, %h, %rs, #Hmu, Hd⟩
  iunfold decEnv at Henv
  icases Henv with ⟨#Hio, #Hbin, #Hfmt, #Hsync, Henv⟩
  wp_apply HLock $$ [] as ⟨Hown, -⟩
  · iexact Hmu
  wp_apply HDecRec C d rp IoE eof ueof fs off c hC $$ [Hd Hr] as %err Hpost
  · isplitr
    · iunfold decEnv
      iframe #
    isplitl [Hd]
    · iunfold ownDecoder
      iexists sl, fbrs, h, rs
      iframe
      iexact Hmu
    · rw [pbRecordC_blank]
      iexact Hr
  wp_apply HUnlock $$ [Hown]
  · iframe
    isplitl []
    · iexact Hmu
    · inext; itrivial
  iapply HΦ
  iexact Hpost

end proof

end EtcdGrove
end Perennial
