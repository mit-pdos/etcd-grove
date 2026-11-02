/-
`(*clientv3.kv).Compact(ctx, rev, opts...)` (`client/v3/kv.go`; the client's `kv.Compact`,
2026-11-01, `examples/compactkv`; the approved spec, `.claude/skills/spec/examples/compact-client.md`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Compact(ctx, rev)` on a `*kv` of etcd's KV `γ` (`isKv`), with no options (`nil`, what a
call with no variadic arguments passes: not physical; `WithCompactPhysical` makes the server wait
for the physical deletion, which its spec does not cover): a compaction at `rev`, a revision past
`0` (M2's scope, `EtcdServer.Compact.spec`'s `1 ≤ r`,
`issues/etcd-restore-scheduled-compact-zero.md`) the KV has reached (`kvRevLb`, from a `Put`'s
reply or at the start's revisions; the scope restriction that keeps `ErrFutureRev` out of the
server's model: Go answers a future revision with that error and changes nothing), on a compacting
cluster (`γ.cmp`, M2's scope); (C3's server stage, 2026-11-02, the user's) at least the cluster's
retention (`γ.cret`) behind the revision reached (`kvRevLbZ`). It changes nothing of `γ`'s state as clients see it (`KVState`: a
compaction is not a state change, M2's A4), so it takes no atomic update and may be delivered more
than once. Returns `nil` and the reply's message (its header), or a client error (`kvErr`; among
them the server's `ErrCompacted` when `rev` is at or below the compaction revision, the
auto-compactor's or an earlier client's) and no reply.

Margin: Go also guarantees that after a `nil` answer every read below `rev` fails with
`ErrCompacted`, and that the error is `ErrCompacted` exactly when `rev` is at or below the
compaction revision; neither is stated (the clients' state does not record the compaction
revision, A4). The header's revision is the member's current one (not stated). -/
abbrev kv.Compact.spec : Prop :=
  ∀ (kv : Loc) (γ : KVNames) (dup : Bool) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (rev : w64),
  1 ≤ sint.Z rev → γ.cmp = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv kv γ dup ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ kvRevLbZ γ (sint.Z rev + γ.cret) }}
    (App (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Compact")) (Val #(GoInterface.ok ctx))) (Val #rev)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ m : CompactRespM, compactRespMsg resp m) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }}

end spec

end EtcdGrove
end Perennial
