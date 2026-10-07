/-
Port of `election_proof/spec_raftLog__hasNextUnstableEnts.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.InvReadylog

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

/-- `l.hasNextUnstableEnts()` (`log.go:202`): `len(l.nextUnstableEnts()) > 0` -- whether
a `Ready` has unstable entries left to hand out. -/
abbrev raftLog.hasNextUnstableEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"hasNextUnstableEnts")) (Val #()))
  {{ (b : Bool), RET #b; ownRaftLog l ls ∗ ⌜b = decide (nextUnstable ls ≠ [])⌝ }}

end spec

end EtcdGrove
end Perennial
