/-
`clientv3.NewKV` (`client/v3/kv.go`).

Users: `client.go`'s `newClient` (`client.KV = NewKV(client)`), leasing (`leasing.NewKV`, over a client).

Proof sketch: `RetryKVClient.spec` from `clientConnOk` (the connection), the client's `callOpts` read from
`clientConnOk`'s field (`callOptsOk _ false`); the fresh `*kv` persisted: `kvHandle`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewKV.lean`: over `clientConnOk` (was the client's members), the result a `kvHandle` (was `isKv`).

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

/-- `NewKV(c)` of a client under construction (`clientConnOk`): a `*kv` of its cluster. -/
def NewKV.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientConnOk c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewKV)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ kv : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #kv⌝ ∗ kvHandle kv γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
