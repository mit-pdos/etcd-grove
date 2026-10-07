/-
Port of `election_proof/spec_raftLog__hasNextCommittedEnts.v` (857d09190).
-/
import EtcdGrove.Raft.InvReadylog

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

/-- `l.hasNextCommittedEnts(allowUnstable)` (`log.go:246`): the cheap check for
`nextCommittedEnts` -- `false` when applying is paused or a snapshot is pending, else
whether `applying < maxAppliableIndex`. The paused flag is not in `LogState`, so the
answer is pinned only when it is `true`: then there is something to apply. -/
abbrev raftLog.hasNextCommittedEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (au : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"hasNextCommittedEnts"))
      (Val #au))
  {{ (b : Bool), RET #b;
      ownRaftLog l ls ∗
      ⌜b = true → ls.snap = none ∧ uint.Z ls.applying < uint.Z ls.committed⌝ }}

end spec

end EtcdGrove
end Perennial
