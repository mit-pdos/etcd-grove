/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__LastOffset.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastOffset


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

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.LastOffset.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.LastOffset.spec (GF := GF) (hG := hG) := by
  intro d IoE eof fs off c live
  wp_start as Hd
  iunfold ownDecoder at Hd
  icases Hd with ⟨%sl, %fbrs, %h, %rs, #Hmu, Hbrs, #Hsl, Hoff, Hcrc, Hcont, Hdc, Hfbrs, %Hinv⟩
  wp_auto
  iapply HΦ
  iunfold ownDecoder
  iexists sl, fbrs, h, rs
  iframe
  iframe Hmu Hsl
  ipureintro
  exact Hinv

end proof

end EtcdGrove
end Perennial
