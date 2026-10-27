/-
The results of client-go's local cache (`k8s.io/client-go/tools/cache`; DaemonSet plan phase 2),
from `Link.lean`: the thread-safe store's methods, logically atomic over the abstract state
`storeSt γ σ` (`StoreModel.lean`, `TSDefs.lean`: items, resource version, indexers), its
constructor, and the store keys.

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
-- the store keys
#print axioms cache.ObjectName.wp_String
#print axioms cache.wp_SplitMetaNamespaceKey

end k8scache
end EtcdGrove
end Perennial
