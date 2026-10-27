/-
The results of client-go's local cache (`k8s.io/client-go/tools/cache`; DaemonSet plan phase 2),
from `Link.lean`: the thread-safe store's methods, logically atomic over the abstract state
`storeSt γ σ` (`StoreModel.lean`, `TSDefs.lean`: items, resource version, indexers), its
constructor, the store keys, and (phase 4) the `cache` store over it (`store.go`: each method the
key function's key, then the thread-safe store's).

`#print axioms` on a result is its trust base: the trust boundary's names-only `strconv.ParseInt`
(the resource-version metric) and Perennial's. The object accessor (`meta.Accessor`) is a premise
of the writers' specs (`rvAcc`), not an axiom.
-/
module

public import Proof.k8s_io.client_go.tools.cache.Link

@[expose] public section

set_option pp.fullNames true

namespace Perennial
namespace EtcdGrove
namespace k8scache

-- the thread-safe store
#print axioms cache.wp_NewThreadSafeStore
#print axioms cache.threadSafeMap.wp_Add
#print axioms cache.threadSafeMap.wp_Update
#print axioms cache.threadSafeMap.wp_Delete
#print axioms cache.threadSafeMap.wp_DeleteWithObject
#print axioms cache.threadSafeMap.wp_Replace
#print axioms cache.threadSafeMap.wp_Bookmark
#print axioms cache.threadSafeMap.wp_Get
#print axioms cache.threadSafeMap.wp_List
#print axioms cache.threadSafeMap.wp_ListKeys
#print axioms cache.threadSafeMap.wp_ByIndex
#print axioms cache.threadSafeMap.wp_Resync
#print axioms cache.threadSafeMap.wp_Index
#print axioms cache.threadSafeMap.wp_LastStoreSyncResourceVersion
-- the store over it (`store.go`'s `cache`; phase 4)
#print axioms cache.cache.wp_Add
#print axioms cache.cache.wp_Update
#print axioms cache.cache.wp_Delete
#print axioms cache.cache.wp_Replace
#print axioms cache.cache.wp_Bookmark
#print axioms cache.cache.wp_Get
#print axioms cache.cache.wp_GetByKey
#print axioms cache.cache.wp_List
#print axioms cache.cache.wp_ListKeys
#print axioms cache.cache.wp_ByIndex
#print axioms cache.cache.wp_Resync
#print axioms cache.cache.wp_Index
#print axioms cache.cache.wp_LastStoreSyncResourceVersion
-- the indexers' additions (phase 4)
#print axioms cache.threadSafeMap.wp_AddIndexers
#print axioms cache.threadSafeMap.wp_GetIndexers
#print axioms cache.cache.wp_AddIndexers
#print axioms cache.cache.wp_GetIndexers
-- the listers' paths through the store (phase 4)
#print axioms cache.wp_ListAll
#print axioms cache.wp_ListAllByNamespace
-- the processing of a popped delta (phase 4)
#print axioms cache.wp_reconcileReplacement
#print axioms cache.wp_processReplacedAllInfo
#print axioms cache.wp_processDeltas
#print axioms cache.sharedIndexInformer.wp_handleDeltas
-- the informers' FIFO (`RealFIFO`, atomic events; phase 4)
#print axioms cache.RealFIFO.wp_Add
#print axioms cache.RealFIFO.wp_Update
#print axioms cache.RealFIFO.wp_Delete
#print axioms cache.RealFIFO.wp_Replace
#print axioms cache.RealFIFO.wp_Bookmark
#print axioms cache.RealFIFO.wp_Close
#print axioms cache.RealFIFO.wp_IsClosed
#print axioms cache.RealFIFO.wp_HasSynced
#print axioms cache.RealFIFO.wp_Pop
-- the store keys
#print axioms cache.ObjectName.wp_String
#print axioms cache.wp_SplitMetaNamespaceKey

end k8scache
end EtcdGrove
end Perennial
