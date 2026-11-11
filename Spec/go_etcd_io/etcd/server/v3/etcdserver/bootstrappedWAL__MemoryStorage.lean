/-
`(*bootstrappedWAL).MemoryStorage()` (`bootstrap.go:741-753`). Lean-first (no Rocq counterpart);
restart S3 (2026-11-11), D2 (b): the restarted raft storage as this method's post, not a trusted
definition.

Takes the record read-only, the snapshot `bootstrap` built at the WAL's base with the backend's conf
state (`walSnapCS σ cs`, set: `bootstrap.go:107-115`), the read hard state (`nil`: zero) and entries;
the entries numbered from the base, the last index at most `2^61 - 1` (`Append`'s and
`ApplySnapshot`'s bounds), and at base `0` the term `0` (the dummy `NewMemoryStorage` froze at `0`
stays: `ApplySnapshot` at index `0`). Gives a new storage, its lock and `memStorRestarted`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseRestartStor
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append

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

/-- `wal.MemoryStorage()`: from the WAL's records `σ` and the backend's conf state `cs`, the storage
`memStorRestarted` describes, with its lock. -/
abbrev bootstrappedWAL.MemoryStorage.spec : Prop :=
  ∀ (w : Loc) (dq : DFrac) (bw : bootstrappedWAL) (σ : StorContents) (cs : ConfStateM)
    (sdq edq : DFrac),
  (∀ (j : Nat) (e : EntryM), σ.ents[j]? = some e → uint.nat e.Index' = σ.b + 1 + j) →
  σ.last < 2^61 →
  (σ.b = 0 → σ.base.term' = W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      w ↦{dq} bw ∗ snapArg bw.snapshot' sdq (walSnapCS σ cs) ∗ hsOpt bw.st' σ.hs ∗
      entsPts bw.ents' edq σ.ents }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"MemoryStorage")) (Val #()))
  {{ (ms : Loc) (γs : MemStorNames), RET #ms;
      w ↦{dq} bw ∗ ownSnapM bw.snapshot' sdq (walSnapCS σ cs) ∗ entsPts bw.ents' edq σ.ents ∗
      memStorLock ms γs ∗ memStorRestarted ms γs σ cs }}

end spec

end EtcdGrove
end Perennial
