/-
`clientv3.RetryKVClient` (`client/v3/retry.go`).

Users: `NewKV`.

Proof sketch: `etcdserverpb.NewKVClient(c.conn)` (the generated stub over the client's connection: `remoteKVAt` from `connOk`, 3h/2a's `req`); the fresh `*retryKVClient` persisted.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/RetryKVClient.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
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

/-- `RetryKVClient(c)`: a `*retryKVClient` over the client's connection. -/
def RetryKVClient.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientConnOk c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryKVClient)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ rkv : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv⌝ ∗ retryKVHandle rkv c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
