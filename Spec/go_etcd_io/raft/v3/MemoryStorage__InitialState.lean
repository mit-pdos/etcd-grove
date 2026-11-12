/- `MemoryStorage.InitialState` (`storage.go:121`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). It takes no lock and reads (and may write the `AutoLeave` of) the stored snapshot, which the locked `Snapshot` writes (`issues/raft-memorystorage-initialstate-unlocked.md`): it is specified before the storage's invariant exists, on the allocation's fuel (`memStorFresh`, which holds the snapshot), with `memStorMeta`. The conf state is returned read-only for good with its `AutoLeave` set (D7).

Durability stage I (I-5, 2026-10-31): detached mode only (`memStorFresh ms γs c sv`, at any compaction point and stored snapshot `sv`, whose conf state it returns). An attached-mode spec cannot be proved: once a node runs, it races with the locked writers. -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.InitialState()`. -/
abbrev MemoryStorage.InitialState.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (hs : HardStateM) (c : Nat) (sv : SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorMeta ms γs hs ∗ memStorFresh ms γs c sv }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp hs ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs c sv ∗
      csPts cs DFrac.discard sv.Metadata'.ConfState' true }}

end spec

end EtcdGrove
end Perennial
