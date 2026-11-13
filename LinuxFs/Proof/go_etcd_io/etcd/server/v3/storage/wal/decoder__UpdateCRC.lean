/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__UpdateCRC.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.New

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

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.wp_proof
    (HNew : go_etcd_io.etcd.pkg.v3.crc.New.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG) := by
  intro d IoE eof fs off c prev live
  wp_start as ⟨#Htab, Hd⟩
  iunfold ownDecoder at Hd
  icases Hd with ⟨%sl, %fbrs, %h, %rs, #Hmu, Hbrs, #Hsl, Hoff, Hcrc, Hcont, -, Hfbrs, %Hinv⟩
  iunfold walCrcTable at Htab
  icases Htab with ⟨%tab, #Hg, #Ht⟩
  wp_auto
  wp_apply HNew as %l Hl
  iapply HΦ
  iunfold ownDecoder
  iexists sl, fbrs, _, rs
  iframe
  iframe Hmu Hsl
  isplitl [Hl]
  · iunfold ownDecCrc
    iexists l, tab
    iframe
    iframe Ht
    ipureintro; rfl
  · ipureintro
    exact Hinv

end proof

end EtcdGrove
end Perennial
