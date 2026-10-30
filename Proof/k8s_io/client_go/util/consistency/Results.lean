/-
The results of client-go's consistency store (`k8s.io/client-go/util/consistency`; DaemonSet plan
phase 2), from `Link.lean`: `WroteAt`, `Clear` and `EnsureReady`, logically atomic over the
abstract state `consState γ M` (`Proof/k8s_io/client_go/util/consistency/Model.lean`, `Defs.lean`),
the constructors, the no-op store; and apimachinery's `CompareResourceVersion`.

`#print axioms` on a result is its trust base: the trust boundary's names-only functions
(`resourceversion.isWellFormed`, gap C1; `schema.GroupResource.String`) and Perennial's.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Link

@[expose] public section

set_option pp.fullNames true

namespace Perennial
namespace EtcdGrove
namespace consistency

-- the store's methods and constructor
#print axioms consistencyStore.wp_WroteAt
#print axioms consistencyStore.wp_Clear
#print axioms consistencyStore.wp_EnsureReady
#print axioms wp_NewConsistencyStore
-- the no-op store
#print axioms wp_NewNoopConsistencyStore
#print axioms noopConsistencyStore.wp_EnsureReady
-- the error's message
#print axioms ConsistencyError.wp_Error
-- resource versions
#print axioms resourceversion.wp_CompareResourceVersion

end consistency
end EtcdGrove
end Perennial
