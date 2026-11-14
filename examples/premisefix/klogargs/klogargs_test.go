// Package klogargs checks what this repository's klog trust-boundary specs assume of the arguments
// of klog.Errorf and klog.Verbose.Infof (klog v2.140.0; Spec/k8s_io/klog/v2/{Errorf,
// Verbose__Infof}.lean, notes/klog-args-fix.md).
//
// Until 2026-11-14 both specs said the call returns for any format and any arguments. Go refutes
// that two ways (the k8s 7f-5a review, lens T5-f, found it on klog.Warningf; the same code path,
// loggingT.printfDepth, serves Errorf and an enabled Verbose's Infof):
//
//   - an argument whose Error() panics with a value whose String() also panics: fmt's catchPanic
//     recovers the first panic, prints the panic value with %v, and re-panics when that panics too
//     (p.panicking); printfDepth does not recover, so the panic escapes klog
//     (TestErrorfNestedPanicEscapes, TestInfofNestedPanicEscapes);
//   - a map argument written concurrently: fmt iterates the map by reflection and the runtime throws
//     "concurrent map iteration and map write", a fatal error no recover catches
//     (TestErrorfConcurrentMapFatal).
//
// The fixed specs take, per argument and under its directive, fmt.argOkAt (Spec/fmt/Errorf.lean:
// nil, a predeclared basic value, an integer under a non-method verb, or an error/Stringer whose
// method returns under a method verb other than %#v) or a []string the caller owns (klog.argOkAt,
// Spec/k8s_io/klog/v2/Args.lean). TestCallersArgs runs the callers' calls (the compactor's and the
// store's formats, with the kinds of arguments they pass) and sees them return.
package klogargs

import (
	"errors"
	"flag"
	"os"
	"os/exec"
	"strings"
	"testing"

	"k8s.io/klog/v2"
)

// badStr's String panics: as a panic value, fmt prints it with %v and calls String.
type badStr struct{}

func (badStr) String() string { panic("String panics") }

// nestErr's Error panics with a badStr value: fmt's catchPanic prints the panic value, whose
// String panics again while p.panicking is set, so fmt re-panics out of Fprintf.
type nestErr struct{}

func (nestErr) Error() string { panic(badStr{}) }

// plainErr's Error panics with a string: fmt recovers it and prints %!v(PANIC=Error method: ...).
type plainErr struct{}

func (plainErr) Error() string { panic("Error panics") }

func recovered(f func()) (p any) {
	defer func() { p = recover() }()
	f()
	return nil
}

// The compactor's own format: the panic escapes klog.Errorf.
func TestErrorfNestedPanicEscapes(t *testing.T) {
	p := recovered(func() {
		klog.Errorf("etcd: endpoint (%v) compact failed: %v", []string{"a"}, error(nestErr{}))
	})
	if p == nil {
		t.Fatalf("expected the panic to escape klog.Errorf")
	}
	t.Logf("klog.Errorf panicked: %v", p)
}

// A panic fmt recovers (one level) does not escape: the spec's argument condition (a method that
// returns) is stronger than needed, which is sound.
func TestErrorfPlainPanicRecovered(t *testing.T) {
	if p := recovered(func() { klog.Errorf("x: %v", error(plainErr{})) }); p != nil {
		t.Fatalf("unexpected escape: %v", p)
	}
}

// Verbose.Infof, when the verbosity enables it (-v=4: the store's and Compact's klog.V(4)), takes
// the same path.
func TestInfofNestedPanicEscapes(t *testing.T) {
	fs := flag.NewFlagSet("klog", flag.ContinueOnError)
	klog.InitFlags(fs)
	if err := fs.Set("v", "4"); err != nil {
		t.Fatal(err)
	}
	defer fs.Set("v", "0")
	v := klog.V(4)
	if !v.Enabled() {
		t.Fatalf("V(4) not enabled")
	}
	p := recovered(func() {
		v.Infof("etcd: compacted rev (%d), endpoints (%v)", int64(1), error(nestErr{}))
	})
	if p == nil {
		t.Fatalf("expected the panic to escape Verbose.Infof")
	}
	t.Logf("Verbose.Infof panicked: %v", p)
}

// A map written concurrently while klog formats it: the runtime's fatal throw (not recoverable),
// observed in a child process.
func TestErrorfConcurrentMapFatal(t *testing.T) {
	if os.Getenv("KLOGARGS_CHILD") == "1" {
		m := map[int]int{}
		for i := 0; i < 1000; i++ {
			m[i] = i
		}
		go func() {
			for i := 0; ; i++ {
				m[i%1000] = i
			}
		}()
		for {
			klog.Errorf("etcd: endpoint (%v): %v", m, errors.New("x"))
		}
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestErrorfConcurrentMapFatal$")
	cmd.Env = append(os.Environ(), "KLOGARGS_CHILD=1")
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("child returned normally")
	}
	const want = "fatal error: concurrent map iteration and map write"
	i := strings.Index(string(out), want)
	if i < 0 {
		i = strings.Index(string(out), "fatal error")
		if i < 0 {
			t.Fatalf("no fatal error in the child's output; err=%v", err)
		}
	}
	t.Logf("child: %v: %s", err, string(out[i:min(len(out), i+len(want))]))
}

// The callers' calls, with the kinds of arguments the fixed specs admit: the client's endpoints (a
// fresh []string, Client.Endpoints), an error whose Error() returns (the client's errors: status
// errors, rpctypes.EtcdError; here errors.New), a string key, an int64 revision.
func TestCallersArgs(t *testing.T) {
	eps := []string{"http://127.0.0.1:2379", "http://127.0.0.1:2380"}
	err := errors.New("etcdserver: mvcc: required revision has been compacted")
	fs := flag.NewFlagSet("klog", flag.ContinueOnError)
	klog.InitFlags(fs)
	_ = fs.Set("v", "4")
	defer fs.Set("v", "0")
	klog.Errorf("etcd: endpoint (%v) compact failed: %v", eps, err) // compact.go:207
	klog.Errorf("etcd: endpoint (%v): %v", eps, err)                // compact.go:265, 273
	klog.V(4).Infof("compactor already exists for endpoints %v", eps)                  // compact.go:60
	klog.V(4).Infof("etcd: compacted rev (%d), endpoints (%v)", int64(42), eps)         // compact.go:250
	klog.V(4).Infof("deletion of %s failed because of a conflict, going to retry", "/k") // store.go:478
	klog.V(4).Infof("GuaranteedUpdate of %s failed because of a conflict, going to retry", "/k")
	// a nil slice and a nil error are admitted too
	klog.Errorf("etcd: endpoint (%v): %v", []string(nil), error(nil))
}
