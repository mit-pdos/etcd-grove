/-
The exported results of Kubernetes' etcd3 store (`k8s.io/apiserver/pkg/storage/etcd3`), from
`Link.lean`, with the trust base of each printed in the build log (`#print axioms`).

* **`store.wp_Watch`** (k8s 7f-5, `notes/k8s-7f5-scope.md` §1): `store.Watch.spec`
  (`Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean`): the store's `Watch` over the
  client's watch (`WithPrevKV`, `WithRequireLeader`), with both of the consumer's branches proved
  (serial, and the concurrent decoding Kubernetes runs by default: no `concurrentDecodeOff`
  premise).
* **`wp_New`**: `New.spec`, the store from its configuration, and (k8s 7f-5b) the store's
  watcher (`storeWatchOk`), which `store.Watch.spec` takes.

The store's other methods (`Get`, `Create`, `Delete`, `GuaranteedUpdate`, `GetList`) are used by
the driver's results (`examples/k8s/etcd3/Results.lean`), which print their trust base.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Link

@[expose] public section

set_option pp.fullNames true

namespace Perennial
namespace EtcdGrove
namespace k8s

#print axioms store.wp_Watch
#print axioms wp_New

end k8s
end EtcdGrove
end Perennial
