/-
`concurrency.waitDeletes(ctx, client, pfx, maxCreateRev)` (`client/v3/concurrency/key.go`). Lean-first (no Rocq counterpart); see
`InvMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`waitDeletes(ctx, client, pfx, waitKey, maxCreateRev)`**, on the client's prefix, for a
non-negative `maxCreateRev` (`0` is no filter: `WithMaxCreateRev(0)`), a key `waitKey` under the
prefix (the waiter's own, etcd#22387) and a cancelable context, knowing etcd has reached `lo`:
* `nil` only when, at some revision `R ≥ lo` (its last `Get`'s, which found nothing), no key under
  the prefix has a create revision at most `maxCreateRev`;
* `errWaitKeyDeleted` only when `waitKey` is absent at some revision `r ≥ lo` (its first `Get`
  found nothing, or its watch of `waitKey` saw it deleted);
* otherwise an error. -/
abbrev waitDeletes.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (client : Loc) (pfx waitKey : GoString)
    (maxCreateRev lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdMutexClient client pfx ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs ∗ etcdReached lo ∗
      ⌜pfx ≠ [] ∧ 0 ≤ sint.Z maxCreateRev ∧ pfx <+: waitKey⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.waitDeletes))
      (Val #(GoInterface.ok ctx))) (Val #client)) (Val #pfx)) (Val #waitKey)) (Val #maxCreateRev))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (R : w64) (s : List EtcdKv), etcdReached R ∗
        □ etcdState R pfx s ∗ ⌜sint.Z lo ≤ sint.Z R ∧
          ∀ v ∈ s, sint.Z maxCreateRev < sint.Z v.createRev⌝) ∨
      (isPkgErr errWaitKeyDeleted err ∗ ∃ r : w64, etcdReached r ∗ etcdAbsent pfx waitKey r ∗
        ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
