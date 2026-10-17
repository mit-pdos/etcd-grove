/- New in etcd-io/raft#132 (no Rocq counterpart). -/
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

/-- `pr.UpdateCommit(index)` (etcd-io/raft#132: "moves the known commit index for this
follower forward"; `tracker.Progress.UpdateCommit.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`):
`pr.Commit = max(pr.Commit, min(index, pr.Match))`, no other field written, no panic --
`progressUpdateCommit p index` (`Defs.lean`). What the PR documents of the field follows from
the record: `Commit` does not regress (`progressUpdateCommit_mono`), stays at most `Match`
(`progressUpdateCommit_ok`), and is at least the reported index capped at `Match`
(`progressUpdateCommit_ge`). -/
abbrev tracker.Progress.UpdateCommit.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (index : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"UpdateCommit"))
      (Val #index))
  {{ RET #(); ownProgress pr (progressUpdateCommit p index) }}

end spec

end EtcdGrove
end Perennial
