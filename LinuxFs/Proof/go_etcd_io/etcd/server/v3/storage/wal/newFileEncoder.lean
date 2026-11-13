/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/newFileEncoder.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newEncoder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
  [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] [os.file.FieldAssumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder.wp_proof
    (wp_newEncoder : go_etcd_io.etcd.server.v3.storage.wal.newEncoder.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf o prev hfd h0 hmax
  wp_start as ⟨#Htab, Hf, Ho⟩
  try wp_auto
  wp_apply (os.File.Seek.wp_cur f fd name dqf o hfd h0 hmax) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  try wp_auto
  wp_apply (wp_newEncoder (wal.fileWi f) prev o (by exact h0)
    (by have : sint.Z o ≤ 0xffffffff000 := hmax; omega))
    $$ [] as %e He
  · iframe #
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
