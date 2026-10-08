/- Port of election_proof/spec_Progress__IsPaused.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `pr.IsPaused()` -- "should the leader hold off sending log entries to this peer".
The body (`tracker.Progress.IsPaused.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`)
switches on `pr.State`:

    StateProbe, StateReplicate -> pr.MsgAppFlowPaused
    StateSnapshot              -> true
    anything else              -> panic("unexpected state")

The fourth arm is why `ownProgress`'s record has an inductive state (`progressAbs`,
`Defs.lean`): `bcastAppend` reaches `IsPaused` on every peer, so the panic has to be
ruled out by an invariant rather than by inspection.

The answer is `progressIsPaused p` (`Defs.lean`), a function of the record, and
`maybeSendAppend` needs to know which branch it took: a `false` answer tells it
`state ≠ .snapshot`, which is what makes the later `SentEntries` call legal (that one
panics in `StateSnapshot`). -/
abbrev tracker.Progress.IsPaused.spec : Prop :=
  ∀ (pr : Loc) (p : Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"IsPaused")) (Val #()))
  {{ RET #(progressIsPaused p); ownProgress pr p }}

end spec

end EtcdGrove
end Perennial
