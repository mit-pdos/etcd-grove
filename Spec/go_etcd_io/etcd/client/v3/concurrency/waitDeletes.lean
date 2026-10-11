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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`waitDeletes(ctx, client, pfx, maxCreateRev)`**, on the client's prefix, for a non-negative
`maxCreateRev` (`0` is no filter: `WithMaxCreateRev(0)`) and a cancelable context, knowing etcd has reached `lo`: `nil` only when, at some
revision `R ≥ lo` (its last `Get`'s, which found nothing), no key under the prefix has a create
revision at most `maxCreateRev`; otherwise an error. -/
abbrev waitDeletes.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (client : Loc) (pfx : GoString)
    (maxCreateRev lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdMutexClient client pfx ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs ∗ etcdReached lo ∗ ⌜pfx ≠ [] ∧ 0 ≤ sint.Z maxCreateRev⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.waitDeletes))
      (Val #(GoInterface.ok ctx))) (Val #client)) (Val #pfx)) (Val #maxCreateRev))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (R : w64) (s : List EtcdKv), etcdReached R ∗
        □ etcdState R pfx s ∗ ⌜sint.Z lo ≤ sint.Z R ∧
          ∀ v ∈ s, sint.Z maxCreateRev < sint.Z v.createRev⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
