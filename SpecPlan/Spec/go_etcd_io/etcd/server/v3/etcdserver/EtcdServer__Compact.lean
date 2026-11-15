/-
## `(*EtcdServer).Compact(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:144`), the auto-compactors (`api/v3compactor/
periodic.go:142`, `revision.go:92`: `Compactable.Compact` with an update built from W0's `envUpd`
(an `EnvStep.compact`, the identity aborted), the caller's context `s.ctx`), Kubernetes' compactor
through the client. Snippet: `examples/specreq/etcdserverreq/kv.go` (`ReqCompactorCompact`).
**The premise `rev ≠ 0`, its sources**: the compactors (`revision.go:82` skips `rev <= 0`; periodic's
revisions are `Rev()` values `≥ 1`), W0's client contract (`KV.CompactTriple`), and for a raw gRPC
client 2a's contract of `/etcdserverpb.KV/Compact` (requested: `req/…api_v3rpc.md`, "from 2c" round
1). It is needed: at a never-compacted store mvcc's `compactMainRev` is `-1`, so `Compact(0)`
succeeds where W0's model answers `ErrCompacted`
(`issues/etcd-restore-scheduled-compact-zero.md`).

**Proof sketch.** The span, `EnsureTrace`, `processInternalRaftRequestOnce(ctx, {Compaction: r})`
(`processInternalRaftRequestOnce.spec` at `.req (.compact rev phys)`): on a result, its trace's
steps (`applyResult`'s owned `traceOpt`, 4b), then, if `physical`, a receive on `result.Physc` (`applyResult`'s `recvAny`:
closed once mvcc's compaction finished, 3e) and `s.be.ForceCommit()` under `s.bemu`'s read lock
(the reader slot from the caller's `threadTok`; 4a's `ForceCommit`); `result.Err` (the answer's
error, fired; or a refusal given back); else the response (a `*pb.CompactionResponse`, made if
`nil`), its header made if `nil`, `Header.Revision = s.kv.Rev()` (3e's `Rev`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Compact.lean`, the pilot's: `kvRevLb γ rev`
excluding `ErrFutureRev`, `compact-client.md`) restated: `ErrFutureRev` and `ErrCompacted` are
fired answers of W0's `Step`, so no revision certificate is needed; `rev ≠ 0` is W0's scope
restriction (`issues/etcd-restore-scheduled-compact-zero.md`: a member crashing during a compaction
at `0` restores a different compaction revision), taken here because this is the only proposer of
compaction entries.

**Margin.** The reply's header revision (the member's store revision after the apply) is not stated
(W0's `compactReply` does not model it); with `physical`, the call returns only after the compaction
is done and committed to the backend, not stated either.

Changes: verify-round (A7-completeness F1, F2): a share of `srvGate` only for a physical compaction (`phys = true`: `s.be.ForceCommit()` reads the backend `Cleanup` closes); the auto-compactor's non-physical compactions, which run until `Cleanup` stops the compactor, need none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Compact(ctx, r)`**: the compaction at `rev` (not `0`), as `Put`. -/
def EtcdServer.Compact.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac) (rev : w64) (phys : Bool),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Compact")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ (if phys then srvGate s q else iprop(True)) ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ compactReqOwn r dq (sint.Z rev) phys ∗ ⌜rev ≠ W64 0⌝)
    iprop((if phys then srvGate s q else iprop(True)) ∗ threadTok ∗ compactReqOwn r dq (sint.Z rev) phys) γ p tls (.compact (sint.Z rev) phys) false (ClientV3.compactReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
