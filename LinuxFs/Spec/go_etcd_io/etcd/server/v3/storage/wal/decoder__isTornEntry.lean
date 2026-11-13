/-
`d.isTornEntry(data)` (decoder.go:173-206): the pure layer's `isTorn` (`WalEncFrame.lean`), `last`
being `len(d.brs) == 1` and the frame at `lastValidOff`. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/decoder__isTornEntry.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.decoder.isTornEntry.spec : Prop :=
  ∀ (d : Loc) (sl : GoSlice) (off : Nat) (data : GoSlice) (xs : List w8) (dq dq' dq'' : DFrac),
  off < 2 ^ 62 → xs.length < 2 ^ 62 →
  {{ (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"brs" d ↦{dq} sl : IProp GF) ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"lastValidOff" d ↦{dq'} W64 off ∗ data ↦*{dq''} xs }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty @!! go!"isTornEntry")) (Val #data))
  {{ RET #(isTorn (decide (sl.len = W64 1)) off xs);
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"brs" d ↦{dq} sl ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.decoder go!"lastValidOff" d ↦{dq'} W64 off ∗ data ↦*{dq''} xs }}

end spec

end EtcdGrove
end Perennial
