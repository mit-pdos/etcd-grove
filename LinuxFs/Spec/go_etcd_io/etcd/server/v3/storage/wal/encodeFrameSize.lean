/-
`encodeFrameSize(dataBytes)` (`server/storage/wal/encoder.go:100-108`, translated with its body in
the part): for `dataBytes ≥ 0`, the pure layer's `encodeFrameSize` (`WalEncFrame.lean`): the length
word and the padding `framePad`. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/encodeFrameSize.lean`. Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFrame

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n →
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.encodeFrameSize)) (Val #n))
  {{ RET (PairV #(WalEnc.encodeFrameSize (sint.nat n)).1 #(W64 (WalEnc.framePad (sint.nat n)))); True }}

end spec

end EtcdGrove
end Perennial
