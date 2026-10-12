/- `MemoryStorage.InitialState` (`storage.go:121`), specified 2026-10-12 (Lean-first: no
Rocq counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.InitialState()`: the hard state last set (`SetHardState`) and the `ConfState` of
the snapshot, and no error. It takes no lock (it reads `hardState` and `snapshot` and
increments `callStats.initialState` bare), so it is stated on `memStorMeta`, whose
halves of the two fields and whose counter make those accesses race-free (the lock's
halves are only read under it, the writers need `memStorMeta`): `InitialState` cannot
run concurrently with `SetHardState`, `ApplySnapshot` or `CreateSnapshot`, with which
it races in Go although the mutex is documented to protect all fields
(issues/raft-memorystorage-initialstate-unlocked.md). -/
abbrev MemoryStorage.InitialState.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (hs : raftpb.HardState) (snap : raftpb.Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hmeta" ∷ memStorMeta ms γs hs snap }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"InitialState")) (Val #()))
  {{ RET (PairV (PairV #hs #snap.Metadata'.ConfState') #interface.nil);
      memStorMeta ms γs hs snap }}

end spec

end EtcdGrove
end Perennial
