/-
`decodeFrameSize(lenField)` (`server/storage/wal/decoder.go:160-169`, translated with its body in
the part): the pure layer's `decodeFrameSize` (`WalEncFrame.lean`): the record's byte count (the
low 56 bits) and the padding (the low 3 bits of the top byte of a negative word). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/decodeFrameSize.lean`. W3a; Lean-first.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize.spec : Prop :=
  ∀ (l : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.decodeFrameSize)) (Val #l))
  {{ RET (PairV #(W64 (WalEnc.decodeFrameSize l).1) #(W64 (WalEnc.decodeFrameSize l).2)); True }}

end spec

end EtcdGrove
end Perennial
