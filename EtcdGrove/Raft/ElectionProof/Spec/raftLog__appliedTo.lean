/- Port of election_proof/spec_raftLog__appliedTo.v (857d09190). -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `l.appliedTo(i, size)` advances `applied` to `i`, and `applying` to
`max(applying, i)` (since 2026-10-05, when `applying` joined `LogState` for `Ready`),
and releases `size` of `applyingEntsSize` (saturating at `0`). It `Panicf`s unless
`applied ≤ i ≤ committed`, hence the premise; `applyingEntsPaused` (also written) is
not part of `LogState`. -/
abbrev raftLog.appliedTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64),
  uint.Z ls.applied ≤ uint.Z i ∧ uint.Z i ≤ uint.Z ls.committed →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"appliedTo")) (Val #i))
      (Val #size))
  {{ RET #(); ownRaftLog l
      { ls with
          applied := i,
          applying := w64Max ls.applying i,
          apsize := if uint.Z size < uint.Z ls.apsize then ls.apsize - size else W64 0 } }}

end spec

end EtcdGrove
end Perennial
