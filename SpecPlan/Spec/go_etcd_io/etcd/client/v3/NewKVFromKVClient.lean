/-
`clientv3.NewKVFromKVClient` (`client/v3/kv.go`).

Users: the in-process client (`server/etcdserver/api/v3client/v3client.go:34`, `c.KV =
clientv3.NewKVFromKVClient(kvc, c)` on `NewCtxClient`'s client: v3lock, v3election); the gRPC proxy
and tests (`server/proxy/grpcproxy`), a caller that brings its own `KVClient`. Snippet:
`clientv3client/inproc.go` (`ReqInProcClient`).

Proof sketch: the `*kv` with `remote` the caller's value (`remoteKVAt`) and, if `c` is not nil, `c`'s call
options (`clientBase`'s, `callOptsOk _ false`), else none (`callOptsOk slice.nil false`, 1c's law).

Changes: none (no old spec): added for the users named above.
verify-round: the client needs only `clientBase` (as the other `From*Client` constructors), not
`clientConnOk` (A2-completeness F3: `NewCtxClient`'s client has no connection, so the in-process
client could not be built); `clientBase`'s realization lists the call options (`ApiClient.lean`).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiClient

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

/-- `NewKVFromKVClient(remote, c)`: a `*kv` over the caller's `remote`. -/
def NewKVFromKVClient.spec : Prop :=
  ∀ (remote : GoInterface) (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ remoteKVAt remote γ who ∗
      (⌜c = null⌝ ∨ ∃ who' : Principal, clientBase c who') }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewKVFromKVClient)) (Val #remote)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ kv : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #kv⌝ ∗ kvHandle kv null γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
