/-
`leasing.NewKV(cl, pfx, opts...)` (`client/v3/leasing/kv.go`).

Users: `server/etcdmain/grpc_proxy.go:488` (`client.KV, _, _ = leasing.NewKV(client, prefix)`: no
options, the close function and the error ignored, the KV served by the proxy's `kvProxy`); the
integration tests (`tests/integration/clientv3/lease/leasing_test.go`: `NewKV(cli, "pfx/")`, some
with `concurrency.WithTTL(1)`, `defer closeLKV()`). Snippets: `leasing/lifecycle.go`
(`ReqNewKVProxy`, `ReqNewKVClose`).

Proof sketch: `cl.Ctx()` (1c: `ctxOk` and `ctxPrin _ who`, `req/go_etcd_io_etcd_client_v3.md`, from 1e),
`Context.WithCancel.spec` of it (W0), `ctxPrin_child`; allocates the `leasingKV` (its fields
from `isClient_KV`'s `kvAt` of `cl.KV`, the options read-only), the `revokes` map (`entries` nil
until the session monitor makes it), `sessionc`; allocates the cache's lock invariant (`lcAt`: no
entry, `sessionc` open, the session nil), the wait group's invariant with the open token's
authority (`lkvOpen γL 1` handed out), `isLeasingKV` from these and `protoUpd`, `sessOptsOk`;
`wg.Add(2)` (the two goroutines' thread tokens deposited, as `WaitGroup`'s bounds discipline asks),
forks `monitorSession` (`leasingKV.monitorSession.spec`, with `sessMonitor`) and `clearOldRevokes`
(`leaseCache.clearOldRevokes.spec`); `waitSession(cctx)` (`leasingKV.waitSession.spec`, the thread
token borrowed and given back); `isLeasingKV_lkvAt` for the interface value, and the method value
`lkv.Close` meets `closeFnAt` (`leasingKV.Close.spec`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/NewKV.lean`: **relaxed**: any
prefix (was non-empty and at most `2 ^ 26` bytes: the bound was for the old payload premise, gone
with W0's gRPC boundary; an empty prefix makes every key a lease key, which only widens what
`protoUpd` permits, the program's choice), any client of the cluster as any principal (was a client
of the old `isLeasingEtcdClient` contracts at prefix `[]`), session options through 1d's slot (was
a cancelable-context premise on them); no `ThreadBoundLe GF (2 ^ 29)` (the pool of reader slots is
the bounds machinery's, `notes/bounds-plan.md`: an open question in the batch report); no
`closedChInit` (the package's `init.spec`, from `isPkgInit`); **new**: `protoUpd` (the protocol's
writes are now steps of the program's `etcdState`).

Margin: `err` is `nil` once the first session was created, or the client's context's error (the
client was closed before): unstated, since the KV works the same either way (its calls then fail)
and the proxy ignores it.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`NewKV(cl, pfx, opts...)`**: for a client of `γ` as `who`, the program's permission for the
protocol's steps with prefix `pfx` and session options for `cl`: a `v3.KV` value meeting the leasing
contract (`lkvAt`), the whole open token, the close function. -/
def NewKV.spec : Prop :=
  ∀ (cl : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (osl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isClient cl γ who ∗ protoUpd γ who pfx ∗ sessOptsOk osl cl ∗ threadTok }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.NewKV)) (Val #cl)) (Val #pfx)) (Val #osl))
  {{ (kv : GoInterface) (cf : GoFunc) (err : GoInterface), RET (PairV (PairV #kv #cf) #err);
      threadTok ∗ ∃ γL : LeasingNames, lkvAt kv γ who pfx γL ∗ lkvOpen γL 1 ∗ closeFnAt cf γL }}

end spec

end Leasing
end EtcdGrove
end Perennial
