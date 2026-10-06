/-
Port of `election_proof/spec_raftLog__hasNextOrInProgressSnapshot.v`.
-/
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

/-- Added back 2026-09-16: deleted earlier that day as "reachable from no proof", which
was only true because `promotable` was an axiom. `promotable`'s body calls this, and
its postcondition `b = decide (id ∈ cfg)` is only derivable if this returns `false`. -/
abbrev raftLog.hasNextOrInProgressSnapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"hasNextOrInProgressSnapshot"))
      (Val #()))
  {{ (b : Bool), RET #b; ownRaftLog l ls ∗ ⌜b = false⌝ }}

end spec

end EtcdGrove
end Perennial
