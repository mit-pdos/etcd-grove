/-
Port of `election_proof/spec_raftLog__nextUnstableEnts.v` (857d09190).
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

/-- `l.nextUnstableEnts()` (`log.go:196`) is `l.unstable.nextEntries()`: the unstable
entries no `Ready` has handed out yet (`nextUnstable`, `InvReadylog.lean`), read-only
and without their capacity (the slice shares `unstable.entries`' slack). The log is
unchanged. -/
abbrev raftLog.nextUnstableEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"nextUnstableEnts")) (Val #()))
  {{ (s : GoSlice), RET #s; ownRaftLog l ls ∗ s ↦*□ nextUnstable ls }}

end spec

end EtcdGrove
end Perennial
