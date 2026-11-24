/-
`(*bootstrappedWAL).MemoryStorage()` (`bootstrap.go:748-760` at the etcd pin `edc800c6f`) of a WAL record
with nothing read (no snapshot, no hard state, no entries: `bootstrapNewWAL`'s), claim #34 stage 4
(2026-11-25): `raft.NewMemoryStorage()`, nothing applied, set or appended. The restart's spec
(`bootstrappedWAL__MemoryStorage.lean`) takes a set snapshot. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `wal.MemoryStorage()` with nothing read: `NewMemoryStorage`'s post (for a caller's flag `sz`). -/
abbrev bootstrappedWAL.MemoryStorage.specFresh : Prop :=
  ∀ (sz : Bool) (w : Loc) (dq : DFrac) (bw : bootstrappedWAL),
  bw.snapshot' = null → bw.st' = null → bw.ents' = slice.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ w ↦{dq} bw }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"MemoryStorage")) (Val #()))
  {{ (ms : Loc) (γs : MemStorNames), RET #ms; w ↦{dq} bw ∗ ⌜γs.sz = sz⌝ ∗
      memStorLock ms γs ∗ memLog γs 0 DFrac.discard [zero_val EntryM] ∗ memEnd γs 1 ∗
      memSnapNone γs memSnapEmpty ∗ memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memStorFresh ms γs 0 memSnapEmpty }}

end spec

end EtcdGrove
end Perennial
