/-
`prepareDataWithPadding(data)` (`server/storage/wal/encoder.go:116-122`): the frame's length word
(`encodeFrameSize`) and `data` padded with `framePad` zero bytes by `append` (in `data`'s array if it
fits, else in a new one). The post hands back a way to recover `data` and its capacity from the
result (Go's `append` leaves `data`'s elements where they are): `encode` gets its scratch buffer back
that way. Premise: `len(data) < 2^62` (`append`'s length does not overflow). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/prepareDataWithPadding.lean`. W6; Lean-first.
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w8), xs.length < 2 ^ 62 →
  {{ s ↦* xs ∗ ownSliceCap (GF := GF) w8 s (DFrac.own 1) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.prepareDataWithPadding)) (Val #s))
  {{ (s' : GoSlice), RET (PairV #s' #(WalEnc.encodeFrameSize xs.length).1);
      s' ↦* (xs ++ List.replicate (WalEnc.framePad xs.length) (0#8)) ∗
      ownSliceCap w8 s' (DFrac.own 1) ∗
      (s' ↦* (xs ++ List.replicate (WalEnc.framePad xs.length) (0#8)) ∗
        ownSliceCap w8 s' (DFrac.own 1) -∗ s ↦* xs ∗ ownSliceCap w8 s (DFrac.own 1)) }}

end spec

end EtcdGrove
end Perennial
