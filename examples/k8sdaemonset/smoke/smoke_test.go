//go:build k8ssmoke

// Package smoke runs the real DaemonSet controller and client-go's informers over the model API
// server (examples/k8sdaemonset/apimodel), checking MaxOnePodPerNode as the robustness test of
// kubernetes/kubernetes#139657 does (one Ready node, one DaemonSet "ds-1"; a checker lists the
// pods every millisecond).
//
// It needs a Kubernetes checkout (the controller is k8s.io/kubernetes, which another module can
// only import with its staging modules replaced): generate this directory's go.mod from one,
// then run with the build tag:
//
//	python3 -I gen-gomod.py /path/to/kubernetes
//	go mod tidy
//	go test -tags k8ssmoke -v .                       # SMOKE_RUNS=n, SMOKE_SETTLE_SECONDS=s
//
// Checked at kubernetes/kubernetes#139657's head 13ecb9cc (2026-10-26):
//   - TestNoFaults: 5 of 5 runs converge to one pod.
//   - TestNoEffectFailures (failures that have no effect, 20%): no run ever has two pods (30 runs);
//     the status converges given time (the reflectors back off under 20% failures).
//   - TestAmbiguousWrites (a write may also commit and still fail): 4 of 50 runs had two pods at
//     once, each after one ambiguous pod create (issues/k8s-daemonset-ambiguous-create-duplicate-pod.md).
package smoke

import (
	"context"
	"os"
	"strconv"
	"sync/atomic"
	"testing"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	clientfeatures "k8s.io/client-go/features"
	clientfeaturestesting "k8s.io/client-go/features/testing"
	"k8s.io/client-go/informers"
	"k8s.io/client-go/kubernetes"
	corev1client "k8s.io/client-go/kubernetes/typed/core/v1"
	"k8s.io/client-go/util/flowcontrol"
	"k8s.io/klog/v2"
	"k8s.io/kubernetes/pkg/controller/daemon"
	"k8s.io/kubernetes/pkg/features"

	"github.com/mit-pdos/etcd-grove/examples/k8sdaemonset/apimodel"
)

// recClient counts the controller's pod creates that report a timeout (the model's ambiguous
// failure) although the pod was stored.
type recClient struct {
	kubernetes.Interface
	ambiguousPodCreates *atomic.Int64
}

func (c recClient) CoreV1() corev1client.CoreV1Interface {
	return recCore{c.Interface.CoreV1(), c.ambiguousPodCreates}
}

type recCore struct {
	corev1client.CoreV1Interface
	n *atomic.Int64
}

func (c recCore) Pods(ns string) corev1client.PodInterface {
	return recPods{c.CoreV1Interface.Pods(ns), c.n}
}

type recPods struct {
	corev1client.PodInterface
	n *atomic.Int64
}

func (c recPods) Create(ctx context.Context, pod *corev1.Pod, opts metav1.CreateOptions) (*corev1.Pod, error) {
	p, err := c.PodInterface.Create(ctx, pod, opts)
	if apierrors.IsTimeout(err) {
		c.n.Add(1)
	}
	return p, err
}

var lastAmbiguousPodCreates int64

func run(t *testing.T, cfg apimodel.Config, settle time.Duration) (maxPods int64, scheduled bool) {
	s := apimodel.NewServer(cfg)
	var ambiguous atomic.Int64
	defer func() { lastAmbiguousPodCreates = ambiguous.Load() }()
	controllerClient := recClient{s.Clientset(), &ambiguous}
	admin := s.AdminClientset()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	node := &corev1.Node{
		ObjectMeta: metav1.ObjectMeta{Name: "target-node"},
		Status:     corev1.NodeStatus{Conditions: []corev1.NodeCondition{{Type: corev1.NodeReady, Status: corev1.ConditionTrue}}},
	}
	if _, err := admin.CoreV1().Nodes().Create(ctx, node, metav1.CreateOptions{}); err != nil {
		t.Fatal(err)
	}

	factory := informers.NewSharedInformerFactory(s.Clientset(), 0)
	dc, err := daemon.NewDaemonSetsController(ctx,
		factory.Apps().V1().DaemonSets(), factory.Apps().V1().ControllerRevisions(),
		factory.Core().V1().Pods(), factory.Core().V1().Nodes(),
		controllerClient, flowcontrol.NewBackOff(100*time.Millisecond, time.Second))
	if err != nil {
		t.Fatal(err)
	}
	factory.Start(ctx.Done())
	go dc.Run(ctx, 2)

	var max atomic.Int64
	done := make(chan struct{})
	go func() {
		defer close(done)
		for ctx.Err() == nil {
			l, err := admin.CoreV1().Pods("default").List(ctx, metav1.ListOptions{})
			if err == nil && int64(len(l.Items)) > max.Load() {
				max.Store(int64(len(l.Items)))
			}
			time.Sleep(time.Millisecond)
		}
	}()

	ds := &appsv1.DaemonSet{
		ObjectMeta: metav1.ObjectMeta{Name: "ds-1", Namespace: "default"},
		Spec: appsv1.DaemonSetSpec{
			Selector: &metav1.LabelSelector{MatchLabels: map[string]string{"app": "nginx"}},
			Template: corev1.PodTemplateSpec{
				ObjectMeta: metav1.ObjectMeta{Labels: map[string]string{"app": "nginx"}},
				Spec:       corev1.PodSpec{Containers: []corev1.Container{{Name: "nginx", Image: "nginx"}}},
			},
		},
	}
	if _, err := admin.AppsV1().DaemonSets("default").Create(ctx, ds, metav1.CreateOptions{}); err != nil {
		t.Fatal(err)
	}

	deadline := time.Now().Add(settle)
	for time.Now().Before(deadline) {
		got, err := admin.AppsV1().DaemonSets("default").Get(ctx, "ds-1", metav1.GetOptions{})
		if err == nil && got.Status.CurrentNumberScheduled == 1 {
			scheduled = true
		}
		time.Sleep(10 * time.Millisecond)
	}
	cancel()
	<-done
	return max.Load(), scheduled
}

func runs() int {
	n, err := strconv.Atoi(os.Getenv("SMOKE_RUNS"))
	if err != nil || n <= 0 {
		return 5
	}
	return n
}

func settle() time.Duration {
	n, err := strconv.Atoi(os.Getenv("SMOKE_SETTLE_SECONDS"))
	if err != nil || n <= 0 {
		return 3 * time.Second
	}
	return time.Duration(n) * time.Second
}

func setup(t *testing.T) {
	klog.SetOutput(os.Stderr)
	clientfeaturestesting.SetFeatureDuringTest(t, clientfeatures.WatchListClient, false)
	clientfeaturestesting.SetFeatureDuringTest(t, clientfeatures.AtomicFIFO, true)
	if !utilfeature.DefaultFeatureGate.Enabled(features.StaleControllerConsistencyDaemonSet) {
		t.Fatal("StaleControllerConsistencyDaemonSet is off")
	}
}

// Failures that have no effect: MaxOnePodPerNode must hold, and the DaemonSet converges.
func TestNoEffectFailures(t *testing.T) {
	setup(t)
	cfg := apimodel.Config{FailWrites: true, FailReads: true, EndWatches: true, ExpireWatches: true,
		Bookmarks: true, FaultPercent: 20}
	for i := 0; i < runs(); i++ {
		max, scheduled := run(t, cfg, settle())
		t.Logf("run %d: max pods %d, scheduled %v", i, max, scheduled)
		if max > 1 {
			t.Errorf("run %d: MaxOnePodPerNode violated: %d pods", i, max)
		}
		if !scheduled {
			t.Errorf("run %d: status never reached CurrentNumberScheduled == 1", i)
		}
	}
}

func TestNoFaults(t *testing.T) {
	setup(t)
	for i := 0; i < runs(); i++ {
		max, scheduled := run(t, apimodel.Config{}, 2*time.Second)
		t.Logf("run %d: max pods %d, scheduled %v", i, max, scheduled)
		if max != 1 || !scheduled {
			t.Errorf("run %d: max pods %d, scheduled %v", i, max, scheduled)
		}
	}
}

// Writes that may take effect and still fail: does MaxOnePodPerNode still hold?
func TestAmbiguousWrites(t *testing.T) {
	setup(t)
	cfg := apimodel.Config{FailWrites: true, AmbiguousWrites: true, FailReads: true, EndWatches: true,
		ExpireWatches: true, Bookmarks: true, FaultPercent: 20}
	violations := 0
	for i := 0; i < runs(); i++ {
		max, _ := run(t, cfg, 3*time.Second)
		if max > 1 {
			violations++
			t.Logf("run %d: %d pods at once; ambiguous pod creates in the run: %d", i, max, lastAmbiguousPodCreates)
		}
	}
	t.Logf("%d of %d runs had more than one pod at once", violations, runs())
}
