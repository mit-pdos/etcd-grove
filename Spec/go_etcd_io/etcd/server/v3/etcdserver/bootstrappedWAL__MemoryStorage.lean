/-
`(*bootstrappedWAL).MemoryStorage()` (`bootstrap.go`, as etcd-io/etcd#19693 changes it;
pr-verify, 2026-10-17): the raft storage of a member restarting from its WAL. Lean-first (no Rocq
counterpart); see `InvBootWAL.lean`.

**The code.** `s := raft.NewMemoryStorage()`; if `wal.confstate != nil`, `s.ApplySnapshot` of a
fresh `&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(wal.pos.Index), Term:
new(wal.pos.Term), ConfState: wal.confstate}}`; if `wal.st != nil`, `s.SetHardState(wal.st)`; if
`len(wal.ents) != 0`, `s.Append(wal.ents)`; return `s`. (Before the PR the snapshot was the WAL's
latest snapshot record, `wal.snapshot`, applied as is.)

**The premises.** The entries continue the base: the first is at the base's index plus one (the
snapshot's `pos.Index`, or `0` without a conf state). This is what `Append` needs not to panic on a
gap (`"missing log entry"`) nor drop entries, and what `WAL.ReadAll` guarantees of the entries it
returns after the position it was opened at (its `ErrSliceOutOfRange` check). The last index is
below `2^61` (raft's storage bound; `Append`'s premise) and so is `pos.Index` (`ApplySnapshot`'s).
The conf state, when set, is owned (`ApplySnapshot` takes the snapshot, and with it the conf state
the snapshot points at, at full ownership: `EnsureSnapshot` may fill its nil fields); the hard
state is `nil` or read-only (`hsOpt`), the entries read-only log entries (`entsPts`, as `Append`
takes them). `ErrSnapOutOfDate`'s address is given (`ApplySnapshot.spec`'s premise; raft's package
facts do not hold it), although a fresh storage never returns it.

**The post.** A fresh `MemoryStorage` at `bwalStor wal.pos wal.confstate cs p` -- the snapshot at
`pos` with `cs` (or none), then the entries `p` -- under fresh ghost names, with the application's
part at the hard state `hs` (`memStorMeta`), what `raft.RestartNode`'s config takes; the receiver
and the entries come back. The conf state is the storage's (its clone's; the caller's pointer is
not returned).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWAL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. (Its proof is over raft's `StorageModel`, as raft's `MemoryStorage` results
are linked: the hand-out and absorb laws are stated in a section over it.) -/
abbrev bootstrappedWAL.MemoryStorage.spec : Prop :=
  ∀ (w : Loc) (dqw : DFrac) (v : bootstrappedWAL) (cs : ConfStateM) (hs : HardStateM)
    (p : List EntryM) (dq : DFrac) (eood : GoInterface),
  (∀ e0, p.head? = some e0 →
    uint.Z e0.Index' = uint.Z (bwalBase v.pos' v.confstate' cs).prev.index' + 1) →
  (∀ e0, p.head? = some e0 → uint.Z e0.Index' + (p.length : Int) ≤ 2^61) →
  uint.Z v.pos'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hw" ∷ w ↦{dqw} v ∗
      "Hcs" ∷ (⌜v.confstate' = null⌝ ∨ ownCSM v.confstate' (DFrac.own 1) cs) ∗
      "#Hst" ∷ hsOpt v.st' hs ∗
      "Hents" ∷ entsPts v.ents' dq p ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"MemoryStorage")) (Val #()))
  {{ (ms : Loc), RET #ms; ∃ γs : MemStorNames,
      w ↦{dqw} v ∗ entsPts v.ents' dq p ∗
      ownMemoryStorage ms γs (bwalStor v.pos' v.confstate' cs p) ∗ memStorMeta ms γs hs }}

end spec

end EtcdGrove
end Perennial
