/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/NewDecoder.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader
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

theorem go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.wp_proof
    (HNFB : go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader.spec (GF := GF) (hG := hG))
    (HNew : go_etcd_io.etcd.pkg.v3.crc.New.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG) := by
  intro sl fs IoE eof
  wp_start as ⟨#Htab, Hsl, Hfs⟩
  sorry

end proof

end EtcdGrove
end Perennial
