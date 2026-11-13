/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__Validate.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate


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
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.wp_proof
    (HErrorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (HGetCrc : True) :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Validate.spec (GF := GF) (hG := hG) := by
  intro l r crc e
  wp_start as ⟨#HE, #He, Hr⟩
  sorry

end proof

end EtcdGrove
end Perennial
