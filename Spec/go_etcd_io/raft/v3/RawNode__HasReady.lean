/-
Port of `election_proof/spec_RawNode__HasReady.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

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

/-- `rn.HasReady()` (`rawnode.go:453`): whether `Ready` would hand out anything -- a new
`SoftState`, a new non-empty `HardState`, a snapshot, messages, unstable entries,
committed entries to apply, read states. Read-only.

Pinned for `false`: the soft state is the previous one, the hard state is empty or the
previous one, the outbox is empty and every unstable entry is already handed out.
Committed entries are not part of the answer's meaning: `hasNextCommittedEnts` is also
`false` while applying is paused, which `LogState` does not record. `r.softState()`,
`r.hardState()` and `rn.applyUnstableEntries()` are stepped through inline (the raft
struct is open, `ownRaftPhys_view`, for the queue lengths). -/
abbrev RawNode.HasReady.spec : Prop :=
  ∀ (cfg : GSet w64) (rn : Loc) (id : w64) (rs : RNState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hrn" ∷ ownRawNode cfg rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"HasReady")) (Val #()))
  {{ (b : Bool), RET #b;
      ownRawNode cfg rn id rs ∗
      ⌜b = false →
        nodeSoftstate rs.raft = rs.soft ∧
        (hsEmptyAbs (nodeHardstate rs.raft) = true ∨ nodeHardstate rs.raft = rs.hard) ∧
        rs.raft.outbox = [] ∧
        nextUnstable rs.raft.logst = []⌝ }}

end spec

end EtcdGrove
end Perennial
