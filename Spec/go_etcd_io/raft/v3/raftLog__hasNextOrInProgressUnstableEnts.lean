/-
Port of `election_proof/spec_raftLog__hasNextOrInProgressUnstableEnts.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.hasNextOrInProgressUnstableEnts()` (`log.go:209`): `len(l.unstable.entries) > 0`
-- whether the log has an unstable suffix at all, handed out or not. -/
abbrev raftLog.hasNextOrInProgressUnstableEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"hasNextOrInProgressUnstableEnts")) (Val #()))
  {{ (b : Bool), RET #b;
      ownRaftLog l ls ∗ ⌜b = decide (ls.uents ≠ [])⌝ }}

end spec

end EtcdGrove
end Perennial
