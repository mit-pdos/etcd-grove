/-
`EnsureConfState(cs)` (`raftpb/util.go:20`).

Users: raft's `MemoryStorage.InitialState` (`storage.go:132`, unlocked: on the stored snapshot's full
conf state, R1), `raft.restore` (`raft.go:1898`) and `appliedSnap` (`raft.go:774`) on a full
snapshot's conf state (shared read-only), `EnsureSnapshotMetadata`. Snippet:
`examples/specreq/raftpb/snapshot.go` (`ReqEnsure`).

Proof sketch: `nil`: `new(ConfState)` (`pbRest_zero`), a fresh `AutoLeave` cell: the empty, full
conf state. Owned: `confStatePts_unfold`; if `AutoLeave` is `nil`, store a fresh cell (`false`, what
the getter read): `confStateFull_unfold`. Full: `AutoLeave` is set, nothing is written.

Changes: from `specs-ref/.../raftpb/EnsureConfState.lean`: over `confStatePts`/`confStateFull` (the
old `ownCS*` variants).
Margin: none.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `EnsureConfState(p)` of `nil` or an owned `ConfState`: a full one holding the same model (the
empty one for `nil`), `p` itself when it was not `nil`; of a full one (any fraction): `p`, nothing
written. -/
def EnsureConfState.spec : Prop :=
  (∀ (p : Loc) (o : Option ConfState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        match o with
        | none => ⌜p = null⌝
        | some cs => confStatePts p (DFrac.own 1) cs }}
      (App (Val (@! go_etcd_io.raft.v3.raftpb.EnsureConfState)) (Val #p))
    {{ (r : Loc), RET #r; confStateFull r (DFrac.own 1) (o.getD ConfState.empty) ∗
        ⌜o ≠ none → r = p⌝ }}) ∧
  (∀ (p : Loc) (dq : DFrac) (cs : ConfState),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ confStateFull p dq cs }}
      (App (Val (@! go_etcd_io.raft.v3.raftpb.EnsureConfState)) (Val #p))
    {{ RET #p; confStateFull p dq cs }})

end spec

end RaftPb
end EtcdGrove
end Perennial
