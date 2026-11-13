/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/encodeFrameSize.lean`: the
translated body.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start as -
  wp_auto
  -- open: `srem (8 - srem n 8) 8 = W64 (framePad (sint.nat n))` for `n ≥ 0`, `n = ofNat (sint.nat n)`,
  -- then the two branches of `padBytes != 0` against `WalEnc.encodeFrameSize`
  sorry

end proof

end EtcdGrove
end Perennial
