package watcherctx

// k8s 7f-5a-P (decided by etcd-grove-81, 2026-11-15): the Go evidence for the candidate trusted
// text `klog.Verbose.InfoS.spec` (Spec/k8s_io/klog/v2/Verbose__InfoS.lean), the call
// blockLogger.recordWait makes (block_logger.go:69-75):
//
//	klog.V(3).InfoS(l.msg, "objectType", l.objectType, "groupResource", l.groupResource,
//		"eventCount", l.eventCount, "timeWaiting", l.timeWaiting, "window", window)
//
// The text claims: for keys and values whose dynamic types are string, int, time.Duration or
// schema.GroupResource, InfoS returns (whatever the message and the values), leaving the argument
// slice unchanged. The configuration assumed is klog's default flags (stderr output) and no
// SetLogger/SetOutput, as for klog.Warningf (T5-f): with a logger set, klog runs foreign code; the
// Verbose value is klog's own (its fields are unexported, so a caller gets one only from klog.V).
// The tests run the call both with V(3) disabled (the default verbosity, 0: InfoS returns at once)
// and enabled (-v=3: klog's text serializer formats every key and value), over adversarial values:
// empty and invalid-UTF-8 strings, quotes and newlines, the extreme ints and durations.

import (
	"flag"
	"math"
	"testing"
	"time"

	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/klog/v2"
)

var infoSStrings = []string{"", "pods", "storage-watch-incoming", "a\"b\nc\td", "\xff\xfe", "\\", "%v %d %!", "ü✓"}

var infoSInts = []int{0, 1, -1, math.MaxInt, math.MinInt}

var infoSDurations = []time.Duration{0, time.Nanosecond, -time.Second, math.MaxInt64, math.MinInt64}

func infoSCalls(t *testing.T) {
	t.Helper()
	n := 0
	for _, s := range infoSStrings {
		for _, gs := range infoSStrings {
			gr := schema.GroupResource{Group: gs, Resource: s}
			for _, i := range infoSInts {
				for _, d := range infoSDurations {
					args := []interface{}{"objectType", s, "groupResource", gr, "eventCount", i,
						"timeWaiting", d, "window", -d}
					before := append([]interface{}(nil), args...)
					klog.V(3).InfoS(s, args...)
					for j := range args {
						if args[j] != before[j] {
							t.Fatalf("InfoS changed its argument %d: %v -> %v", j, before[j], args[j])
						}
					}
					n++
				}
			}
		}
	}
	// an odd number of keys and values, and a key of another listed type (still the listed types)
	klog.V(3).InfoS("odd", "objectType")
	klog.V(3).InfoS("int key", 7, "x", time.Second, schema.GroupResource{})
	t.Logf("%d InfoS calls returned", n)
}

// TestKlogInfoSDisabledReturns: the default verbosity (0), so V(3) is disabled.
func TestKlogInfoSDisabledReturns(t *testing.T) {
	if klog.V(3).Enabled() {
		t.Fatalf("V(3) enabled at the default verbosity")
	}
	infoSCalls(t)
}

// TestKlogInfoSEnabledReturns: -v=3, so V(3) is enabled and every call is serialized to stderr.
func TestKlogInfoSEnabledReturns(t *testing.T) {
	fs := flag.NewFlagSet("klog", flag.ContinueOnError)
	klog.InitFlags(fs)
	if err := fs.Set("v", "3"); err != nil {
		t.Fatal(err)
	}
	defer fs.Set("v", "0")
	if !klog.V(3).Enabled() {
		t.Fatalf("V(3) not enabled at -v=3")
	}
	infoSCalls(t)
}
