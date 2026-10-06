/- Port of election_proof/spec_Progress__SentEntries.v. -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys
import EtcdGrove.Raft.ElectionProof.Spec.Inflights__Full

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

/-- `pr.SentEntries(entries, bytes)` records a `MsgApp` carrying `entries` entries
(`tracker.Progress.SentEntries.impl`, `Perennial/Code/go_etcd_io/raft/v3/tracker.lean`).
It switches on `pr.State`:

    StateReplicate: Next += entries (if entries > 0), then
                    Inflights.Add(Next-1, bytes), then
                    MsgAppFlowPaused = Inflights.Full()
    StateProbe:     MsgAppFlowPaused = true (if entries > 0)
    otherwise:      panic("sending append in unhandled state %s")

Hence the two premises. `State ≠ StateSnapshot` rules out the panic (with
`ProgressStateOk` from `ownProgress`, that leaves Probe and Replicate), and the second
premise is `Inflights.Add`'s: `Add` panics on a full window. Both are exactly what
`maybeSendAppend` has when it gets here -- it only reaches this line after `IsPaused()`
returned `false` (so the state is not Snapshot) and, in `StateReplicate`, entries are
non-empty only when `!pr.Inflights.Full()` was the branch that fetched them.

The resulting `Progress` is existential: `Next`, `MsgAppFlowPaused` and the window all
move, and nothing above reads them back within one `bcastAppend`. -/
abbrev tracker.Progress.SentEntries.spec : Prop :=
  ∀ (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights) (entries bytes : w64),
  pv.State' ≠ W64 2 →
  (pv.State' = W64 1 → 0 < sint.Z entries → inflightsFull iv = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr pv iv }}
    (App (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"SentEntries"))
      (Val #entries)) (Val #bytes))
  {{ RET #(); ∃ pv' iv', ownProgress pr pv' iv' }}

end spec

end EtcdGrove
end Perennial
