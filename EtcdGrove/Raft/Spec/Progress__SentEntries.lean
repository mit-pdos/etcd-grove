/- Port of election_proof/spec_Progress__SentEntries.v (feb5c73d4). -/
import EtcdGrove.Raft.InvRaftPhys
import EtcdGrove.Raft.Spec.Inflights__Full

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

/-- `pr.SentEntries(entries, bytes)` records a `MsgApp` carrying `entries` entries
(`tracker.Progress.SentEntries.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`).
It switches on `pr.State`:

    StateReplicate: Next += entries (if entries > 0), then
                    Inflights.Add(Next-1, bytes), then
                    MsgAppFlowPaused = Inflights.Full()
    StateProbe:     MsgAppFlowPaused = true (if entries > 0)
    otherwise:      panic("sending append in unhandled state %s")

Hence the two premises. `state ≠ .snapshot` rules out the panic, and the second premise
is `Inflights.Add`'s: `Add` panics on a full window. Both are exactly what
`maybeSendAppend` has when it gets here -- it only reaches this line after `IsPaused()`
returned `false` (so the state is not Snapshot) and, in `StateReplicate`, entries are
non-empty only when `!pr.Inflights.Full()` was the branch that fetched them.

The new record is `progressSentEntries p entries bytes` (`Defs.lean`); it leaves
`matched` alone (Match discipline, notes/raft-replication-model.md). (Until 2026-10-02
the result was existential, with only `Match` pinned.) -/
abbrev tracker.Progress.SentEntries.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (entries bytes : w64),
  p.state ≠ .snapshot →
  (p.state = .replicate → 0 < sint.Z entries → inflightsFull p.infl = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"SentEntries"))
      (Val #entries)) (Val #bytes))
  {{ RET #(); ownProgress pr (progressSentEntries p entries bytes) }}

end spec

end EtcdGrove
end Perennial
