/- Port of election_proof/spec_readOnly__AckedIndex.v (feb5c73d4).

Lean notes: Rocq's `default (W64 0) x` is `x.getD (W64 0)`, and
`bool_decide (is_Some x)` is `x.isSome` (the form `isAckedIndexer`'s contract uses).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `ro.AckedIndex(voterID)` (`readOnly.AckedIndex.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3.lean`; `read_only.go:72`), the read-only object seen
as a `quorum.AckedIndexer`:

    idx, found := ro.acks[voterID]
    return quorum.Index(idx), found

No panic, no call. The result is the voter's ack in the `(value-or-0, ok)` form of
`isAckedIndexer`'s contract (`InvTracker.lean`), which is what this triple exists to
discharge for `maybeAdvance`. -/
abbrev readOnly.AckedIndex.spec : Prop :=
  ∀ (ro : Loc) (r : ReadOnly) (voterID : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hown" ∷ ownReadOnly ro r }}
    (App (Val (ro @!! go.GoType.PointerType readOnly.ty @!! go!"AckedIndex")) (Val #voterID))
  {{ RET (PairV #((r.acks !! voterID).getD (W64 0)) #((r.acks !! voterID).isSome));
      ownReadOnly ro r }}

end spec

end EtcdGrove
end Perennial
