// Package k8s is the Go harness of sweep repairs 1, group b1, item B5: the k8s feature
// initializers' new premises (a registered feature for Enabled; a constructed client and a context
// for CheckClient). A module of its own, as examples/k8s/compactor (whose go.mod and go.sum it
// copies). Not committed.
package k8s

import (
	"context"
	"fmt"
	"sort"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"k8s.io/apiserver/pkg/features"
	"k8s.io/apiserver/pkg/storage"
	etcdfeature "k8s.io/apiserver/pkg/storage/feature"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
	"k8s.io/component-base/featuregate"
)

func panics(f func()) (msg string, ok bool) {
	defer func() {
		if r := recover(); r != nil {
			msg, ok = fmt.Sprint(r), true
		}
	}()
	f()
	return "", false
}

// registered is the Go meaning of `featureKnown f`: f is a key of the default gate's known map.
func registered(f featuregate.Feature) bool {
	_, ok := utilfeature.DefaultMutableFeatureGate.GetAll()[f]
	return ok
}

// The features etcd3's verified code asks (New, store.Delete: AllowUnsafeMalformedObjectDeletion;
// NewCompactor: ListFromCacheSnapshot), and the others the package's unverified code asks.
var queried = []featuregate.Feature{features.AllowUnsafeMalformedObjectDeletion, features.ListFromCacheSnapshot,
	features.EtcdRangeStream, features.WatchList, features.ConcurrentWatchObjectDecode}

func TestB5Registered(t *testing.T) {
	all := utilfeature.DefaultMutableFeatureGate.GetAll()
	keys := make([]string, 0, len(all))
	for k := range all {
		keys = append(keys, string(k))
	}
	sort.Strings(keys)
	t.Logf("registered features after init (%d): %v", len(keys), keys)
	for _, f := range queried {
		if !registered(f) {
			t.Fatalf("%s is not registered", f)
		}
		var b bool
		if msg, p := panics(func() { b = utilfeature.DefaultFeatureGate.Enabled(f) }); p {
			t.Fatalf("Enabled(%s) panicked: %s", f, msg)
		}
		t.Logf("featureKnown %-36s holds; Enabled = %v", f, b)
	}
	for _, k := range keys {
		if _, p := panics(func() { utilfeature.DefaultFeatureGate.Enabled(featuregate.Feature(k)) }); p {
			t.Fatalf("Enabled(%s) panicked", k)
		}
	}
	t.Logf("Enabled of each of the %d registered features: 0 panics", len(keys))
}

func TestB5Counterexample(t *testing.T) {
	f := featuregate.Feature("NoSuchFeature")
	if registered(f) {
		t.Fatal("NoSuchFeature registered")
	}
	msg, p := panics(func() { utilfeature.DefaultFeatureGate.Enabled(f) })
	t.Logf("featureKnown NoSuchFeature = false (premise violated); Enabled panics=%v %q", p, msg)
	if !p {
		t.Error("no panic")
	}
	msg, p = panics(func() { etcdfeature.DefaultFeatureSupportChecker.CheckClient(nil, nil, storage.RequestWatchProgress) })
	t.Logf("CheckClient(nil ctx, nil client): checkClientOk = false (nil client); panics=%v %q", p, msg)
	var nc *kubernetes.Client
	msg, p = panics(func() {
		etcdfeature.DefaultFeatureSupportChecker.CheckClient(context.Background(), nc, storage.RequestWatchProgress)
	})
	t.Logf("CheckClient(Background, typed-nil *kubernetes.Client): checkClientOk = false; panics=%v %q", p, msg)
}

// The client etcd3.New passes: a kubernetes.Client from kubernetes.New, with its own context.
func TestB5CheckClientReal(t *testing.T) {
	for i := 0; i < 20; i++ {
		c, err := kubernetes.New(clientv3.Config{Endpoints: []string{fmt.Sprintf("127.0.0.1:%d", 1+i), "127.0.0.1:2"},
			DialTimeout: 50 * time.Millisecond})
		if err != nil {
			t.Fatal(err)
		}
		if msg, p := panics(func() {
			etcdfeature.DefaultFeatureSupportChecker.CheckClient(c.Ctx(), c, storage.RequestWatchProgress)
		}); p {
			t.Fatalf("CheckClient of a real client panicked: %s", msg)
		}
		time.Sleep(100 * time.Millisecond) // the per-endpoint goroutines poll Status (unreachable: errors)
		c.Close()
	}
	time.Sleep(300 * time.Millisecond)
	t.Logf("CheckClient(c.Ctx(), c, RequestWatchProgress) of 20 kubernetes.New clients: returned, no crash of the polling goroutines")
}

// TestB5SetOff (sweep repairs 1, B5 joint with k8s 7e; 2026-11-08): featureGateOk's two triples and
// the attacks 81 listed. One process: Set is global state, so this test runs alone (-run).
func TestB5SetOff(t *testing.T) {
	// the two variables hold one gate (the same *featureGate behind two interface types)
	if fmt.Sprintf("%p", utilfeature.DefaultMutableFeatureGate) != fmt.Sprintf("%p", utilfeature.DefaultFeatureGate) {
		t.Fatalf("DefaultMutableFeatureGate and DefaultFeatureGate differ")
	}
	t.Logf("both globals hold %p", utilfeature.DefaultFeatureGate)
	// attack (i): Enabled of an unregistered feature panics; the spec only covers k8sQueriedFeatures
	if msg, ok := panics(func() { utilfeature.DefaultFeatureGate.Enabled("NoSuchFeature") }); !ok {
		t.Fatalf("Enabled(NoSuchFeature) did not panic")
	} else {
		t.Logf("Enabled(NoSuchFeature) panics: %s", msg)
	}
	// Set(false) succeeds at the pin's binary version, then Enabled is false
	if err := utilfeature.DefaultMutableFeatureGate.Set(string(features.EtcdRangeStream) + "=false"); err != nil {
		t.Fatalf("Set(EtcdRangeStream=false): %v", err)
	}
	// attack (ii): a second Set(false) after the first
	if err := utilfeature.DefaultMutableFeatureGate.Set("EtcdRangeStream=false"); err != nil {
		t.Fatalf("second Set(EtcdRangeStream=false): %v", err)
	}
	done := make(chan bool)
	for g := 0; g < 8; g++ {
		go func() {
			ok := true
			for i := 0; i < 100; i++ {
				if utilfeature.DefaultFeatureGate.Enabled(features.EtcdRangeStream) {
					ok = false
				}
			}
			done <- ok
		}()
	}
	for g := 0; g < 8; g++ {
		if !<-done {
			t.Fatalf("Enabled(EtcdRangeStream) returned true after Set(false)")
		}
	}
	t.Logf("after Set(EtcdRangeStream=false) (twice): 800 Enabled calls from 8 goroutines, all false")
	// a failing Set changes nothing Enabled reads; it does poison later Sets (enabledRaw keeps the bad
	// key, SetFromMapWithLogger:500-504), which the spec's error disjunct covers
	if err := utilfeature.DefaultMutableFeatureGate.Set("NoSuchFeature=false"); err == nil {
		t.Fatalf("Set(NoSuchFeature=false) succeeded")
	} else {
		t.Logf("Set(NoSuchFeature=false) errs: %v", err)
	}
	if utilfeature.DefaultFeatureGate.Enabled(features.EtcdRangeStream) {
		t.Fatalf("a failing Set changed EtcdRangeStream")
	}
	err2 := utilfeature.DefaultMutableFeatureGate.Set("EtcdRangeStream=false")
	t.Logf("Set(EtcdRangeStream=false) after the failing Set: err=%v; Enabled(EtcdRangeStream)=%v", err2,
		utilfeature.DefaultFeatureGate.Enabled(features.EtcdRangeStream))
	// attack (iii): SetEmulationVersion after Set (no caller in the closure; observation only)
	v := utilfeature.DefaultMutableFeatureGate.EmulationVersion()
	err := utilfeature.DefaultMutableFeatureGate.SetEmulationVersion(v)
	t.Logf("SetEmulationVersion(%v) after Set: err=%v, Enabled(EtcdRangeStream)=%v", v, err,
		utilfeature.DefaultFeatureGate.Enabled(features.EtcdRangeStream))
}
