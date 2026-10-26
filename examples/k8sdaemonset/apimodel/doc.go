// Package apimodel is a model of the Kubernetes API server behind client-go's clientset
// (k8s.io/client-go/kubernetes.Interface), for running the real DaemonSet controller and
// client-go's informers against it. It covers only what the DaemonSet controller and its
// informers call (notes/k8s-daemonset-plan.md, D49, D50).
//
// The model is part of the trusted computing base: a theorem about a program that runs over it
// is a theorem about the real controller only insofar as this package behaves like
// kube-apiserver. Its code is written to be read, by people comparing it with the API server
// and by the proofs that step through it: one lock, plain maps, one append-only change log per
// resource, and nondeterminism only through math/rand's Int63n (Config says where).
//
// # State
//
// One Server holds, per resource (pods, nodes, daemonsets, controllerrevisions), the stored
// objects keyed by namespace and name, and the log of every change to the resource. Resource
// versions are global, as etcd's revisions are: every change takes the next number, its string
// form (strconv.FormatUint in base 10, injective) is written into the stored object, and the model
// keeps the numbers it issued by string, so it never parses a resource version.
//
// # Operations (at client-go's signatures)
//
//   - Create: the object is copied; a namespaced object gets the request's namespace (a
//     different one is a 400); an empty name is generated from GenerateName (the prefix and a
//     fresh number; kube-apiserver uses random characters), an empty name and GenerateName are a
//     400; a set ResourceVersion is a 400; an existing name is a 409 AlreadyExists. The server
//     sets the UID, CreationTimestamp and ResourceVersion, then applies the resource's create
//     strategy (below).
//   - Get: a copy of the stored object, or 404.
//   - List: copies of the objects in the namespace (all namespaces for ""), in an arbitrary
//     order (kube-apiserver: by key), with ListMeta.ResourceVersion the current resource
//     version: a consistent snapshot, whatever ResourceVersion the request gives (a list may be
//     served at any version at least the one requested; the newest always qualifies). Limit is
//     ignored and no continue token is returned (a server may ignore Limit). Label and field
//     selectors are rejected with a 400 (nothing here uses them).
//   - Watch: every change to the resource after the requested version, in order (a Deleted
//     event carries the object's last state at the deletion's version). For "" or "0", the
//     current objects as Added events, then every later change. An unknown version (not issued
//     by this server) is a 410 Expired, as for a compacted one; with Config.ExpireWatches an
//     issued but old version may be too. With AllowWatchBookmarks and Config.Bookmarks, a watch
//     that has sent every change may send a Bookmark at the current version. With
//     Config.EndWatches the server may end a watch at any point (close its channel), as a real
//     server does on a timeout or restart; client-go's reflector then watches again from the
//     last version it saw. SendInitialEvents (the watch-list mode) is a 400: run the informers
//     with client-go's WatchListClient off.
//   - Update (controllerrevisions) and UpdateStatus (daemonsets): 404 if the object is gone, 409
//     Conflict if the request's ResourceVersion is set and is not the stored one (an empty one is
//     an unconditional update, which both resources' strategies allow). The stored object's
//     identity (name, namespace, UID, CreationTimestamp) is kept. UpdateStatus replaces only the
//     status (the status strategy keeps the stored spec; this model also keeps the stored
//     metadata); an UpdateStatus that leaves the status unchanged writes nothing and returns the
//     stored object at its current version, as kube-apiserver skips no-op writes. Update always
//     writes (kube-apiserver would skip an unchanged object; the DaemonSet controller does not
//     reach Update).
//   - Delete: 404 if the object is gone; 409 if DeleteOptions.Preconditions (UID,
//     ResourceVersion) do not hold. A pod is deleted gracefully (kept, with DeletionTimestamp
//     and DeletionGracePeriodSeconds set, a Modified event) when it is bound to a node, has not
//     finished, and its grace period (the options', else the pod's
//     TerminationGracePeriodSeconds) is positive, as pod's CheckGracefulDelete decides; with no
//     kubelet in the model it then stays. An object with finalizers is likewise kept with
//     DeletionTimestamp set. Otherwise it is removed (a Deleted event). Deleting an object that
//     is already being deleted changes nothing.
//   - Events (core/v1): accepted and dropped (the controller's event recorder writes them; no
//     one reads them).
//
// Every other method of client-go's interfaces is absent: the clients embed client-go's
// interfaces with a nil value, so calling one panics, and a no-panic theorem shows none is
// called.
//
// # Create strategies (what kube-apiserver does to a created object)
//
//   - DaemonSet: the defaults of SetDefaults_DaemonSet (k8s.io/kubernetes/pkg/apis/apps/v1:
//     UpdateStrategy RollingUpdate, MaxUnavailable 1, MaxSurge 0, RevisionHistoryLimit 10); the
//     create strategy (pkg/registry/apps/daemonset): Status cleared, Generation 1, the template
//     generation at least 1 (in apps/v1, the annotation DeprecatedTemplateGeneration: set to "1"
//     if absent; a present value is kept as is, where kube-apiserver would parse it and raise
//     values below 1). The pod template's own defaults are not applied.
//   - Pod: Generation 1, Status {Phase: Pending} (pkg/registry/core/pod); the defaults
//     TerminationGracePeriodSeconds 30, RestartPolicy Always, DNSPolicy ClusterFirst,
//     SchedulerName "default-scheduler" when unset. Not modeled: the containers' defaults,
//     admission (ServiceAccount, Priority, ...), scheduling gates.
//   - Node, ControllerRevision: stored as given.
//
// No validation beyond the above: the caller that creates the DaemonSet and the nodes (the test
// program) is trusted to create valid objects; the objects the controller creates are its own.
//
// # Failures (Config)
//
//   - FailWrites: a write may fail before taking effect (500).
//   - AmbiguousWrites: a write may take effect and still report failure (a timeout after the
//     commit). Off by default: the theorem's premise "a failed write had no effect" is this flag
//     off (notes/k8s-daemonset-plan.md, the suspected bug).
//   - FailReads: a Get or List may fail (500); a Watch may fail to start (500).
//   - EndWatches, ExpireWatches, Bookmarks: above.
//
// A client from AdminClientset never sees a failure (the test program's own setup and checks).
// In Go, a flagged choice happens with probability Config.FaultPercent / 100; a proof treats
// every flagged choice as arbitrary, so the percentage matters only for testing.
//
// Not modeled: request contexts (cancellation is ignored), authentication and authorization,
// admission webhooks, server-side apply and patches, field managers, the watch cache's own
// staleness (a list or watch here is never older than the last write), and any resource other
// than the four.
package apimodel
