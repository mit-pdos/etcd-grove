/-
The results of the model API server (`examples/k8sdaemonset/apimodel`; DaemonSet plan phase 3),
from `Link.lean`: `NewServer` (the empty state), the server's operations (`create`, `get`, `list`,
`update`, `remove`, `watch`), logically atomic over its abstract state `apiState γ σ`
(`State.lean`, `Defs.lean`), a watch's `Stop` and `ResultChan`, and the typed clients over them,
each linearizing at the server's operation.

The model is trusted Go (D50): these specs are an internal layer of the DaemonSet controller's
proof, not part of its spec boundary. `#print axioms` on a result is its trust base: the trust
boundary's names-only functions (the API types' `DeepCopyObject`, apimachinery's
`NewInternalError`, `NewConflict`, `schema.GroupResource.String`) and Perennial's; no `sorry`
(`copyObject`'s assertion to `object`, gap C8, is proved since the Perennial pin `ad74ee4f6`). The results in `links_pending` take as hypotheses the specs not
proved yet: the watcher's goroutine (`watcher.run`, whose precondition `runPre` is what `watch`
hands it), the pod and DaemonSet create strategies, the status strategy
(`updateDaemonSetStatus`, `daemonSetStatusEqual`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Link

@[expose] public section

set_option pp.fullNames true

namespace Perennial
namespace EtcdGrove
namespace apimodel

-- the server
#print axioms wp_NewServer
#print axioms Server.wp_create
#print axioms Server.wp_get
#print axioms Server.wp_list
#print axioms Server.wp_update
#print axioms Server.wp_remove
-- a watch's handle
#print axioms watcher.wp_Stop
#print axioms watcher.wp_ResultChan
-- the typed clients
#print axioms podClient.wp_Get
#print axioms podClient.wp_List
#print axioms podClient.wp_Delete
#print axioms nodeClient.wp_Create
#print axioms nodeClient.wp_Get
#print axioms nodeClient.wp_List
#print axioms daemonSetClient.wp_Get
#print axioms daemonSetClient.wp_List
#print axioms revisionClient.wp_Create
#print axioms revisionClient.wp_Get
#print axioms revisionClient.wp_List
#print axioms revisionClient.wp_Update
#print axioms revisionClient.wp_Delete
-- the watch and the typed clients over the specs not proved yet (`links_pending`)
#print axioms Server.wp_watch
#print axioms podClient.wp_Create
#print axioms podClient.wp_Watch
#print axioms nodeClient.wp_Watch
#print axioms daemonSetClient.wp_Create
#print axioms daemonSetClient.wp_UpdateStatus
#print axioms daemonSetClient.wp_Watch
#print axioms revisionClient.wp_Watch
-- the clientsets
#print axioms Server.wp_Clientset
#print axioms Server.wp_AdminClientset
#print axioms Clientset.wp_CoreV1
#print axioms Clientset.wp_AppsV1

end apimodel
end EtcdGrove
end Perennial
