/-
The results of client-go's informers above the store (`k8s.io/client-go/listers`,
`k8s.io/client-go/informers`; DaemonSet plan phase 4), from `Link.lean`: the generic lister's
`Get` and `List` over the cache store (`tools/cache`'s `Link.lean`).

`#print axioms` on a result is its trust base: the store's (`tools/cache/Results.lean`) and the
trust boundary's names-only `schema.GroupResource.String` (`NewNotFound`'s message) and
`apps/v1.Resource`, `core/v1.Resource` (the typed listers' `GroupResource`s).
-/
module

public import Proof.k8s_io.client_go.informers.Link

@[expose] public section

set_option pp.fullNames true

namespace Perennial
namespace EtcdGrove
namespace k8sinformers

-- the generic lister
#print axioms listers.ResourceIndexer.wp_Get
#print axioms listers.ResourceIndexer.wp_List
#print axioms listers.wp_New
#print axioms listers.wp_NewNamespaced
-- the DaemonSet lister (listers/apps/v1)
#print axioms appslisters.wp_NewDaemonSetLister
#print axioms appslisters.daemonSetLister.wp_DaemonSets
#print axioms appslisters.daemonSetNamespaceLister.wp_Get
#print axioms appslisters.daemonSetNamespaceLister.wp_List
#print axioms appslisters.daemonSetLister.wp_GetPodDaemonSets
#print axioms appslisters.daemonSetLister.wp_GetHistoryDaemonSets
-- the ControllerRevision lister (listers/apps/v1)
#print axioms appslisters.wp_NewControllerRevisionLister
#print axioms appslisters.controllerRevisionLister.wp_ControllerRevisions
#print axioms appslisters.controllerRevisionNamespaceLister.wp_Get
#print axioms appslisters.controllerRevisionNamespaceLister.wp_List
-- the Pod and Node listers (listers/core/v1)
#print axioms corelisters.wp_NewPodLister
#print axioms corelisters.podLister.wp_Pods
#print axioms corelisters.podNamespaceLister.wp_Get
#print axioms corelisters.podNamespaceLister.wp_List
#print axioms corelisters.wp_NewNodeLister
#print axioms corelisters.nodeLister.wp_Get
#print axioms corelisters.nodeLister.wp_List

end k8sinformers
end EtcdGrove
end Perennial
