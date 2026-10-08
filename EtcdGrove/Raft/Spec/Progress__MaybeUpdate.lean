/- Port of election_proof/spec_Progress__MaybeUpdate.v (feb5c73d4). -/
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

/-- `pr.MaybeUpdate(n)` records that the peer has acknowledged index `n`
(`tracker.Progress.MaybeUpdate.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`;
progress.go:205):

    if n <= pr.Match { return false }          // exit 1: stale ack
    pr.Match = n
    pr.Next = max(pr.Next, n+1)
    pr.MsgAppFlowPaused = false
    return true                                // exit 2

No panic, no call (`max` is the builtin). `n+1` is `uint64` arithmetic and wraps at
`n = 2^64-1`, where Go's `max` then keeps `pr.Next`; the postcondition says exactly
that, with `w64` addition and `w64Max` (`Defs.lean`, Goose's `max` verbatim).
`Inflights` is untouched.

`progressMaybeUpdate p n` (`Defs.lean`) is the new record; it is `p` itself when the ack
is stale. `matched` becomes `n` exactly when it grows. -/
abbrev tracker.Progress.MaybeUpdate.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"MaybeUpdate"))
      (Val #n))
  {{ RET #(decide (uint.Z p.matched < uint.Z n));
      ownProgress pr (progressMaybeUpdate p n) }}

end spec

end EtcdGrove
end Perennial
