/- (D22 S-d1, 2026-10-20) Lean-first. -/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `u.stableSnapTo(i)` (`log_unstable.go:178`):

    if u.snapshot != nil && u.snapshot.GetMetadata().GetIndex() == i {
        u.snapshot = nil
        u.snapshotInProgress = false
    }

On a hit (`snapHit`: a snapshot pending at index `i`) the snapshot is dropped and no longer in
progress; otherwise nothing changes (`unstableSnapTo`). Whether the storage holds the snapshot
by then is the caller's business (`raft.appliedSnap`'s, stage S-d2). -/
abbrev unstable.stableSnapTo.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"stableSnapTo")) (Val #i))
  {{ RET #(); ownUnstable u (unstableSnapTo us i) }}

end spec

end EtcdGrove
end Perennial
