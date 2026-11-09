/-
`concurrency.waitDeletes(ctx, client, pfx, maxCreateRev)` (`client/v3/concurrency/key.go`),
internal.

Users: `Mutex.Lock` (`myRev - 1`), `Election.Campaign` (`leaderRev - 1`).

Proof sketch: `WithLastCreate.spec`, `WithMaxCreateRev.spec`, `append` (W0's option models: a
prefix get sorted by create revision, descending, limit 1, create revisions at most `n`); a loop
of the KV contract's `Get` (a linearizable read, its update from `etcdPeek`; `etcdLb_reach` inside
it gives `Reach σ0`): an empty answer at `σ` means no key under the prefix has a create revision at
most `n` (`RangeReq.answers` with the filter, `n > 0` so the filter is on): return `nil` with
`etcdLb γ σ`; else `waitDelete.spec` on the newest such key from the reply's revision, an error
returned.

Changes: from `specs-ref`'s `waitDeletes.lean`: over the cluster's states; round 1: `σ0`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `waitDeletes(ctx, c, pfx, n)` (`n > 0`): `nil` and, at a state the cluster reached after `σ0`, no key under `pfx` is older than `n + 1`; or an error. -/
def waitDeletes.spec : Prop :=
  ∀ (ctx : GoInterface) (c : Loc) (γ : Cluster) (dflt who : Principal) (pfx : GoString) (n : w64)
    (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isClient c γ dflt ∗ Context.ctxOk ctx ∗ ctxPrin dflt ctx who ∗ etcdPeek γ ∗ etcdLb γ σ0 ∗ ⌜0 < sint.Z n⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.waitDeletes)) (Val #ctx)) (Val #c)) (Val #pfx)) (Val #n))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : State, etcdLb γ σ ∗
          ⌜Reach σ0 σ ∧ noOlder pfx ((sint.Z n).toNat + 1) σ.kv.store⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Concurrency
end EtcdGrove
end Perennial
