/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__LastCRC.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.crc.digest__Sum32

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

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.wp_proof
    (HSum : go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.LastCRC.spec (GF := GF) (hG := hG) := by
  intro d IoE eof fs off c live
  wp_start as Hd
  iunfold ownDecoder at Hd
  icases Hd with ⟨%sl, %fbrs, %h, %rs, #Hmu, Hbrs, #Hsl, Hoff, Hcrc, Hcont, Hdc, Hfbrs, %Hinv⟩
  iunfold ownDecCrc at Hdc
  icases Hdc with ⟨%l, %tab, %Hh, Hl, #Htab⟩
  subst Hh
  wp_auto
  wp_apply HSum $$ [Hl] as Hl
  · iexact Hl
  iapply HΦ
  iunfold ownDecoder
  iexists sl, fbrs, _, rs
  iframe
  iframe Hmu Hsl
  isplitl [Hl]
  · iunfold ownDecCrc
    iexists l, tab
    iframe
    iframe Htab
    ipureintro; rfl
  · ipureintro
    exact Hinv

end proof

end EtcdGrove
end Perennial
