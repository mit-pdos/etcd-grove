/-
The results of client-go's work queue (`k8s.io/client-go/util/workqueue`; DaemonSet plan phase 2),
from `Link.lean`: the typed queue (`Typed[T]`'s methods and constructors), the rate limiters, and
the delaying and rate-limiting queues.

`#print axioms` on a result is its trust base: the trust boundary's names-only functions (their
`wp_proof` axioms: `k8s.io/utils/clock`, `klog`, `x/time/rate`, `container/heap`, `math.Pow`,
`time.Duration.Nanoseconds`, `utilruntime.HandleCrashWithLogger`) and Perennial's; no `sorry`. The
methods the delaying and rate-limiting queues promote from their embedded interfaces are proved
(each the embedded queue's), so every result is linked.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Link

@[expose] public section

set_option pp.fullNames true

namespace Perennial
namespace EtcdGrove
namespace workqueue

-- the typed queue: no axioms of this repository
#print axioms Typed.wp_Add
#print axioms Typed.wp_Get
#print axioms Typed.wp_Done
#print axioms Typed.wp_ShutDown
#print axioms Typed.wp_ShutDownWithDrain
#print axioms wp_NewTypedWithConfig
-- the rate limiters
#print axioms wp_DefaultTypedControllerRateLimiter
-- the delaying and rate-limiting queues
#print axioms delayingType.wp_waitingLoop
#print axioms rateLimitingType.wp_Get
#print axioms rateLimitingType.wp_Done
#print axioms rateLimitingType.wp_AddRateLimited
#print axioms wp_NewTypedRateLimitingQueueWithConfig

end workqueue
end EtcdGrove
end Perennial
