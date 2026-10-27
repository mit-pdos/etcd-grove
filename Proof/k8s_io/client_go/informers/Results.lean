/-
The results of client-go's informers above the store (`k8s.io/client-go/listers`,
`k8s.io/client-go/informers`; DaemonSet plan phase 4), from `Link.lean`: the generic lister's
`Get` and `List` over the cache store (`tools/cache`'s `Link.lean`).

`#print axioms` on a result is its trust base: the store's (`tools/cache/Results.lean`) and the
trust boundary's names-only `schema.GroupResource.String` (`NewNotFound`'s message).
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

end k8sinformers
end EtcdGrove
end Perennial
