// Package dsmain is the program of the DaemonSet controller's closed theorem
// (notes/k8s-daemonset-plan.md, phase 0; D49, D50): the real DaemonSet controller of
// k8s.io/kubernetes (pkg/controller/daemon) and client-go's real informers, running over the
// model API server (examples/k8sdaemonset/apimodel), with a checker that panics if the server
// ever holds two pods of the DaemonSet bound to one node (S1, MaxOnePodPerNode: the safety
// invariant of the controller robustness test, kubernetes/kubernetes#139657,
// test/integration/daemonset/robustness_test.go).
//
// The scenario is the robustness test's: one Ready node, one DaemonSet "ds-1" in "default"
// whose pods run nginx. The model may fail any request of the controller and its informers,
// end or expire any watch, and send bookmarks (every Config flag but AmbiguousWrites: the
// theorem's premise "a failed write had no effect", D50; with it on the controller does put two
// pods on the node, issues/k8s-daemonset-ambiguous-create-duplicate-pod.md).
//
// The adequacy theorem to prove (phase 6): for every number of checks, no thread of
// Main(checks) panics or is stuck.
package dsmain

import (
	"context"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	"k8s.io/client-go/informers"
	informersapps "k8s.io/client-go/informers/apps"
	appsinformers "k8s.io/client-go/informers/apps/v1"
	informerscore "k8s.io/client-go/informers/core"
	coreinformers "k8s.io/client-go/informers/core/v1"
	"k8s.io/client-go/kubernetes"
	appsclient "k8s.io/client-go/kubernetes/typed/apps/v1"
	coreclient "k8s.io/client-go/kubernetes/typed/core/v1"
	"k8s.io/client-go/util/flowcontrol"
	"k8s.io/kubernetes/pkg/controller/daemon"
	"k8s.io/kubernetes/pkg/controller/daemon/util"

	"github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/apimodel"
)

const (
	namespace = "default"
	nodeName  = "target-node"
	dsName    = "ds-1"
)

// serverConfig is the model's configuration: every failure but ambiguous writes.
func serverConfig() apimodel.Config {
	return apimodel.Config{FailWrites: true, FailReads: true, EndWatches: true,
		ExpireWatches: true, Bookmarks: true, FaultPercent: 20}
}

// setFeatureGates sets the gates the scenario needs, as kube-controller-manager's
// --feature-gates=WatchListClient=false,AtomicFIFO=true,StaleControllerConsistencyDaemonSet=true
// would. k8s.io/kubernetes/pkg/features' init makes client-go's gates an adapter over this gate
// (utilfeature.DefaultMutableFeatureGate), so these are also the gates client-go's reflector and
// stores read (an environment variable, KUBE_FEATURE_WatchListClient, would not be: it is read
// only by client-go's own gates, which that init replaces). WatchListClient off: the reflector
// lists, then watches (the model rejects a watch-list request). AtomicFIFO on: the stores report
// the resource version they have synced to, which the consistency store needs.
// StaleControllerConsistencyDaemonSet on: the controller uses the consistency store. The last two
// are on by default; setting them states the configuration in the program rather than in the
// default table pkg/features' init registers.
func setFeatureGates() {
	if err := utilfeature.DefaultMutableFeatureGate.SetFromMap(map[string]bool{
		"WatchListClient":                     false,
		"AtomicFIFO":                          true,
		"StaleControllerConsistencyDaemonSet": true,
	}); err != nil {
		panic(err)
	}
}

// newNode is the scenario's node: Ready.
func newNode() *corev1.Node {
	return &corev1.Node{
		ObjectMeta: metav1.ObjectMeta{Name: nodeName},
		Status: corev1.NodeStatus{Conditions: []corev1.NodeCondition{
			{Type: corev1.NodeReady, Status: corev1.ConditionTrue}}},
	}
}

// newDaemonSet is the scenario's DaemonSet, its pod template with the defaults kube-apiserver
// would give it (k8s.io/kubernetes/pkg/apis/core/v1: SetDefaults_PodSpec, SetDefaults_Container;
// the model defaults the DaemonSet's own fields but not its template, apimodel's doc.go).
func newDaemonSet() *appsv1.DaemonSet {
	grace := int64(corev1.DefaultTerminationGracePeriodSeconds)
	return &appsv1.DaemonSet{
		ObjectMeta: metav1.ObjectMeta{Name: dsName, Namespace: namespace},
		Spec: appsv1.DaemonSetSpec{
			Selector: &metav1.LabelSelector{MatchLabels: map[string]string{"app": "nginx"}},
			Template: corev1.PodTemplateSpec{
				ObjectMeta: metav1.ObjectMeta{Labels: map[string]string{"app": "nginx"}},
				Spec: corev1.PodSpec{
					Containers: []corev1.Container{{
						Name:                     "nginx",
						Image:                    "nginx",
						ImagePullPolicy:          corev1.PullAlways,
						TerminationMessagePath:   corev1.TerminationMessagePathDefault,
						TerminationMessagePolicy: corev1.TerminationMessageReadFile,
					}},
					RestartPolicy:                 corev1.RestartPolicyAlways,
					TerminationGracePeriodSeconds: &grace,
					DNSPolicy:                     corev1.DNSClusterFirst,
					SecurityContext:               &corev1.PodSecurityContext{},
					SchedulerName:                 corev1.DefaultSchedulerName,
				},
			},
		},
	}
}

// controlledBy reports whether the pod's controller is the object with this UID.
func controlledBy(pod *corev1.Pod, uid types.UID) bool {
	for _, ref := range pod.OwnerReferences {
		if ref.UID == uid && ref.Controller != nil && *ref.Controller {
			return true
		}
	}
	return false
}

// check lists the pods and panics if two pods controlled by the DaemonSet (UID uid) are bound,
// by node name or node affinity (the controller's util.GetTargetNodeName), to one node; pods
// being deleted count too, as in the robustness test. It returns the number of such pods
// bound to a node (0 if the list fails).
func check(ctx context.Context, admin kubernetes.Interface, uid types.UID) int {
	var core coreclient.CoreV1Interface = admin.CoreV1()
	var podClient coreclient.PodInterface = core.Pods(namespace)
	pods, err := podClient.List(ctx, metav1.ListOptions{})
	if err != nil {
		return 0
	}
	bound := make(map[string]bool)
	n := 0
	for i := range pods.Items {
		pod := &pods.Items[i]
		if !controlledBy(pod, uid) {
			continue
		}
		node, err := util.GetTargetNodeName(pod)
		if err != nil {
			continue
		}
		if bound[node] {
			panic("MaxOnePodPerNode: two pods of the DaemonSet bound to node " + node)
		}
		bound[node] = true
		n++
	}
	return n
}

// run is Main over the model's configuration cfg: it starts the model API server, creates the
// node, starts the informers and the controller (two workers, as kube-controller-manager's
// default --concurrent-daemonset-syncs; its failed-pods backoff), creates the DaemonSet, then
// checks `checks` times, a millisecond apart, and stops everything. It returns the number of
// the DaemonSet's bound pods at the last check.
func run(cfg apimodel.Config, checks int) int {
	setFeatureGates()
	s := apimodel.NewServer(cfg)
	admin := s.AdminClientset()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	var adminCore coreclient.CoreV1Interface = admin.CoreV1()
	var adminNodes coreclient.NodeInterface = adminCore.Nodes()
	if _, err := adminNodes.Create(ctx, newNode(), metav1.CreateOptions{}); err != nil {
		panic(err)
	}

	// The informers and the controller over the (non-admin) clientset. Each intermediate value
	// is named with its interface type, which Goose needs imported (gap D2 of
	// notes/k8s-daemonset-goose.md).
	clients := s.Clientset()
	factory := informers.NewSharedInformerFactory(clients, 0)
	var appsGroup informersapps.Interface = factory.Apps()
	var apps appsinformers.Interface = appsGroup.V1()
	var coreGroup informerscore.Interface = factory.Core()
	var core coreinformers.Interface = coreGroup.V1()
	dsc, err := daemon.NewDaemonSetsController(ctx,
		apps.DaemonSets(), apps.ControllerRevisions(), core.Pods(), core.Nodes(),
		clients, flowcontrol.NewBackOff(time.Second, 15*time.Minute))
	if err != nil {
		panic(err)
	}
	factory.Start(ctx.Done())
	go dsc.Run(ctx, 2)

	var adminApps appsclient.AppsV1Interface = admin.AppsV1()
	var adminDaemonSets appsclient.DaemonSetInterface = adminApps.DaemonSets(namespace)
	ds, err := adminDaemonSets.Create(ctx, newDaemonSet(), metav1.CreateOptions{})
	if err != nil {
		panic(err)
	}

	n := 0
	for i := 0; i < checks; i++ {
		n = check(ctx, admin, ds.UID)
		time.Sleep(time.Millisecond)
	}
	return n
}

// Main is the theorem's program: the scenario with `checks` checks.
func Main(checks int) {
	run(serverConfig(), checks)
}
