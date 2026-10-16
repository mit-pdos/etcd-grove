/-
New with raft#243 (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `pr.OnSnapshotApplied(i)` (raft#243, `tracker.Progress.OnSnapshotApplied.impl`):

    pr.Match = appliedSnapshotIndex
    pr.Next = pr.Match + 1

Exact: the new record is `progressOnSnapshotApplied p i` (`Defs.lean`). Nothing relates `i`
to the old `Match` (it may lower it) or to the follower (it may raise it past what the
follower acknowledged): a caller that holds the leader's invariants must supply that
(`stepLeader`'s `MsgSnapStatus`). `i + 1` is `uint64` arithmetic and wraps. -/
abbrev tracker.Progress.OnSnapshotApplied.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"OnSnapshotApplied"))
      (Val #i))
  {{ RET #(); ownProgress pr (progressOnSnapshotApplied p i) }}

end spec

end EtcdGrove
end Perennial
