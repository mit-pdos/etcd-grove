/-
`(*clientv3.Client).Do`: the `KV` method promoted through `Client`'s embedded `KV` field.

Users: leasing (`leasing/kv.go:244` `Do` of every operation it forwards, `leasing/cache.go`), the
cache (`cache/cache.go`, `cache/watcher.go` `Do(OpGet(...))`), Kubernetes' compactor
(`etcd3/compact.go`). Snippet: `clientv3kv/ops.go` (`ReqDo`).

Proof sketch: `isClient_KV`: the field `c.KV` holds `v` with `kvAt v γ who`, read-only; the promoted
method loads it and calls `v.Do` (Go's method set of `*Client`); `kvAt_methods`' `Do` at `v`.

Changes: none (no old spec): the users call the KV methods on the client; added so that their proofs need no dispatch lemma.

Margin: as the KV method.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Do(...)` on a client (`isClient`): the method of its `KV` field, promoted (`Client` embeds
`KV`): the KV contract's `Do` (`KV.DoTriple`). -/
def Client.Do.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  KV.DoTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Do")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
