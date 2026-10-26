package apimodel

import (
	"context"
	"testing"
	"time"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/types"
	"k8s.io/apimachinery/pkg/watch"
	clientfeatures "k8s.io/client-go/features"
	clientfeaturestesting "k8s.io/client-go/features/testing"
	"k8s.io/client-go/informers"
	"k8s.io/client-go/kubernetes"
	"k8s.io/client-go/tools/cache"
)

var _ kubernetes.Interface = &Clientset{}

var ctx = context.Background()

func newPod(generateName string) *corev1.Pod {
	return &corev1.Pod{
		ObjectMeta: metav1.ObjectMeta{GenerateName: generateName, Labels: map[string]string{"app": "x"}},
		Spec:       corev1.PodSpec{Containers: []corev1.Container{{Name: "c", Image: "i"}}},
	}
}

func TestCreateGeneratesNamesAndVersions(t *testing.T) {
	c := NewServer(Config{}).AdminClientset()
	p1, err := c.CoreV1().Pods("default").Create(ctx, newPod("ds-1-"), metav1.CreateOptions{})
	if err != nil {
		t.Fatal(err)
	}
	p2, err := c.CoreV1().Pods("default").Create(ctx, newPod("ds-1-"), metav1.CreateOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if p1.Name == p2.Name || p1.Name == "" || p1.UID == p2.UID || p1.UID == "" {
		t.Fatalf("names/UIDs not fresh: %q %q %q %q", p1.Name, p2.Name, p1.UID, p2.UID)
	}
	if p1.ResourceVersion != "1" || p2.ResourceVersion != "2" {
		t.Fatalf("resource versions: %q %q", p1.ResourceVersion, p2.ResourceVersion)
	}
	if p1.Namespace != "default" || p1.Status.Phase != corev1.PodPending || p1.Generation != 1 ||
		p1.Spec.TerminationGracePeriodSeconds == nil || *p1.Spec.TerminationGracePeriodSeconds != 30 {
		t.Fatalf("create strategy not applied: %+v", p1)
	}
	l, err := c.CoreV1().Pods("default").List(ctx, metav1.ListOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if len(l.Items) != 2 || l.ResourceVersion != "2" {
		t.Fatalf("list: %d items at %q", len(l.Items), l.ResourceVersion)
	}
	other, err := c.CoreV1().Pods("other").List(ctx, metav1.ListOptions{})
	if err != nil || len(other.Items) != 0 {
		t.Fatalf("namespaced list: %v %v", other, err)
	}
}

func TestCreateErrors(t *testing.T) {
	c := NewServer(Config{}).AdminClientset()
	pods := c.CoreV1().Pods("default")
	if _, err := pods.Create(ctx, &corev1.Pod{}, metav1.CreateOptions{}); !apierrors.IsBadRequest(err) {
		t.Fatalf("no name: %v", err)
	}
	withRV := newPod("p-")
	withRV.ResourceVersion = "5"
	if _, err := pods.Create(ctx, withRV, metav1.CreateOptions{}); !apierrors.IsBadRequest(err) {
		t.Fatalf("resource version set: %v", err)
	}
	wrongNS := newPod("p-")
	wrongNS.Namespace = "other"
	if _, err := pods.Create(ctx, wrongNS, metav1.CreateOptions{}); !apierrors.IsBadRequest(err) {
		t.Fatalf("namespace mismatch: %v", err)
	}
	named := &corev1.Pod{ObjectMeta: metav1.ObjectMeta{Name: "p"}}
	if _, err := pods.Create(ctx, named, metav1.CreateOptions{}); err != nil {
		t.Fatal(err)
	}
	if _, err := pods.Create(ctx, named, metav1.CreateOptions{}); !apierrors.IsAlreadyExists(err) {
		t.Fatalf("duplicate: %v", err)
	}
	if _, err := pods.Get(ctx, "q", metav1.GetOptions{}); !apierrors.IsNotFound(err) {
		t.Fatalf("missing: %v", err)
	}
	if _, err := pods.List(ctx, metav1.ListOptions{LabelSelector: "a=b"}); !apierrors.IsBadRequest(err) {
		t.Fatalf("selector: %v", err)
	}
}

func newDaemonSet() *appsv1.DaemonSet {
	return &appsv1.DaemonSet{
		ObjectMeta: metav1.ObjectMeta{Name: "ds-1"},
		Spec: appsv1.DaemonSetSpec{
			Selector: &metav1.LabelSelector{MatchLabels: map[string]string{"app": "x"}},
			Template: corev1.PodTemplateSpec{
				ObjectMeta: metav1.ObjectMeta{Labels: map[string]string{"app": "x"}},
				Spec:       corev1.PodSpec{Containers: []corev1.Container{{Name: "c", Image: "i"}}},
			},
		},
		Status: appsv1.DaemonSetStatus{NumberReady: 7},
	}
}

func TestDaemonSetCreateAndStatus(t *testing.T) {
	c := NewServer(Config{}).AdminClientset()
	dss := c.AppsV1().DaemonSets("default")
	ds, err := dss.Create(ctx, newDaemonSet(), metav1.CreateOptions{})
	if err != nil {
		t.Fatal(err)
	}
	ru := ds.Spec.UpdateStrategy.RollingUpdate
	if ds.Spec.UpdateStrategy.Type != appsv1.RollingUpdateDaemonSetStrategyType || ru == nil ||
		ru.MaxUnavailable.IntValue() != 1 || ru.MaxSurge.IntValue() != 0 ||
		*ds.Spec.RevisionHistoryLimit != 10 || ds.Generation != 1 || ds.Status.NumberReady != 0 ||
		ds.Annotations[appsv1.DeprecatedTemplateGeneration] != "1" {
		t.Fatalf("defaults/create strategy not applied: %+v", ds)
	}

	stale := ds.DeepCopy()
	upd := ds.DeepCopy()
	upd.Status.CurrentNumberScheduled = 1
	upd.Spec.MinReadySeconds = 99 // ignored: status updates keep the spec
	upd2, err := dss.UpdateStatus(ctx, upd, metav1.UpdateOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if upd2.Status.CurrentNumberScheduled != 1 || upd2.Spec.MinReadySeconds != 0 || upd2.ResourceVersion == ds.ResourceVersion || upd2.UID != ds.UID {
		t.Fatalf("status update: %+v", upd2)
	}
	stale.Status.NumberReady = 3
	if _, err := dss.UpdateStatus(ctx, stale, metav1.UpdateOptions{}); !apierrors.IsConflict(err) {
		t.Fatalf("stale update: %v", err)
	}
	same, err := dss.UpdateStatus(ctx, upd2.DeepCopy(), metav1.UpdateOptions{})
	if err != nil || same.ResourceVersion != upd2.ResourceVersion {
		t.Fatalf("no-op status update wrote: %v %v", same, err)
	}
}

func TestPodDelete(t *testing.T) {
	c := NewServer(Config{}).AdminClientset()
	pods := c.CoreV1().Pods("default")
	unbound, _ := pods.Create(ctx, newPod("u-"), metav1.CreateOptions{})
	if err := pods.Delete(ctx, unbound.Name, metav1.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	if _, err := pods.Get(ctx, unbound.Name, metav1.GetOptions{}); !apierrors.IsNotFound(err) {
		t.Fatalf("unbound pod not deleted at once: %v", err)
	}
	b := newPod("b-")
	b.Spec.NodeName = "n"
	bound, _ := pods.Create(ctx, b, metav1.CreateOptions{})
	wrong := types.UID("nope")
	if err := pods.Delete(ctx, bound.Name, metav1.DeleteOptions{Preconditions: &metav1.Preconditions{UID: &wrong}}); !apierrors.IsConflict(err) {
		t.Fatalf("precondition: %v", err)
	}
	if err := pods.Delete(ctx, bound.Name, metav1.DeleteOptions{}); err != nil {
		t.Fatal(err)
	}
	got, err := pods.Get(ctx, bound.Name, metav1.GetOptions{})
	if err != nil || got.DeletionTimestamp == nil || *got.DeletionGracePeriodSeconds != 30 {
		t.Fatalf("bound pod not deleted gracefully: %+v %v", got, err)
	}
	if err := pods.Delete(ctx, "missing", metav1.DeleteOptions{}); !apierrors.IsNotFound(err) {
		t.Fatalf("missing: %v", err)
	}
}

func next(t *testing.T, w watch.Interface) watch.Event {
	t.Helper()
	select {
	case ev, ok := <-w.ResultChan():
		if !ok {
			t.Fatal("watch closed")
		}
		return ev
	case <-time.After(5 * time.Second):
		t.Fatal("no event")
	}
	return watch.Event{}
}

func TestWatch(t *testing.T) {
	c := NewServer(Config{}).AdminClientset()
	pods := c.CoreV1().Pods("default")
	first, _ := pods.Create(ctx, newPod("a-"), metav1.CreateOptions{})
	l, _ := pods.List(ctx, metav1.ListOptions{})

	w, err := pods.Watch(ctx, metav1.ListOptions{ResourceVersion: l.ResourceVersion})
	if err != nil {
		t.Fatal(err)
	}
	defer w.Stop()
	second, _ := pods.Create(ctx, newPod("a-"), metav1.CreateOptions{})
	_ = pods.Delete(ctx, first.Name, metav1.DeleteOptions{})
	ev := next(t, w)
	if ev.Type != watch.Added || ev.Object.(*corev1.Pod).Name != second.Name {
		t.Fatalf("first event: %v", ev)
	}
	ev = next(t, w)
	if ev.Type != watch.Deleted || ev.Object.(*corev1.Pod).Name != first.Name || ev.Object.(*corev1.Pod).ResourceVersion != "3" {
		t.Fatalf("second event: %v", ev)
	}

	all, err := pods.Watch(ctx, metav1.ListOptions{})
	if err != nil {
		t.Fatal(err)
	}
	defer all.Stop()
	ev = next(t, all)
	if ev.Type != watch.Added || ev.Object.(*corev1.Pod).Name != second.Name {
		t.Fatalf("initial event: %v", ev)
	}

	if _, err := pods.Watch(ctx, metav1.ListOptions{ResourceVersion: "12345"}); !apierrors.IsResourceExpired(err) {
		t.Fatalf("unknown version: %v", err)
	}
}

func TestWatchStopCloses(t *testing.T) {
	c := NewServer(Config{}).AdminClientset()
	w, err := c.CoreV1().Nodes().Watch(ctx, metav1.ListOptions{})
	if err != nil {
		t.Fatal(err)
	}
	w.Stop()
	select {
	case _, ok := <-w.ResultChan():
		if ok {
			t.Fatal("event after Stop")
		}
	case <-time.After(5 * time.Second):
		t.Fatal("result channel not closed after Stop")
	}
}

// The real informers over the model, with every failure but ambiguous writes: the caches
// converge to the server's state and report its resource version.
func TestInformersConverge(t *testing.T) {
	clientfeaturestesting.SetFeatureDuringTest(t, clientfeatures.WatchListClient, false)
	clientfeaturestesting.SetFeatureDuringTest(t, clientfeatures.AtomicFIFO, true)
	s := NewServer(Config{FailWrites: true, FailReads: true, EndWatches: true, ExpireWatches: true,
		Bookmarks: true, FaultPercent: 20})
	admin := s.AdminClientset()

	runCtx, cancel := context.WithCancel(ctx)
	defer cancel()
	factory := informers.NewSharedInformerFactory(s.Clientset(), 0)
	podInf := factory.Core().V1().Pods().Informer()
	dsInf := factory.Apps().V1().DaemonSets().Informer()
	factory.Start(runCtx.Done())

	if _, err := admin.AppsV1().DaemonSets("default").Create(ctx, newDaemonSet(), metav1.CreateOptions{}); err != nil {
		t.Fatal(err)
	}
	var last string
	for i := 0; i < 30; i++ {
		p, err := admin.CoreV1().Pods("default").Create(ctx, newPod("p-"), metav1.CreateOptions{})
		if err != nil {
			t.Fatal(err)
		}
		last = p.ResourceVersion
		if i%3 == 0 {
			if err := admin.CoreV1().Pods("default").Delete(ctx, p.Name, metav1.DeleteOptions{}); err != nil {
				t.Fatal(err)
			}
		}
	}
	final, _ := admin.CoreV1().Pods("default").List(ctx, metav1.ListOptions{})
	_ = last

	deadline := time.Now().Add(20 * time.Second)
	for {
		store := podInf.GetStore()
		if len(store.List()) == len(final.Items) && store.LastStoreSyncResourceVersion() == final.ResourceVersion &&
			cache.WaitForCacheSync(runCtx.Done(), podInf.HasSynced, dsInf.HasSynced) {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("pod cache: %d objects at %q, server: %d at %q", len(store.List()),
				store.LastStoreSyncResourceVersion(), len(final.Items), final.ResourceVersion)
		}
		time.Sleep(10 * time.Millisecond)
	}
	for _, item := range final.Items {
		got, ok, _ := podInf.GetStore().GetByKey("default/" + item.Name)
		if !ok || got.(*corev1.Pod).ResourceVersion != item.ResourceVersion {
			t.Fatalf("pod %s: cached %v", item.Name, got)
		}
	}
}
