package klogargs

// The format parser's gaps (klog-args-fix, the axiom review's MAJOR, 2026-11-14; pre-existing in
// fmt.fmtDirectives / fmt.argOkAt, Spec/fmt/Errorf.lean, shared by fmt.argsOk's users):
//
//   - a width or precision whose digit run passes 1e6: Go's parsenum (fmt/print.go:350-362, go1.27.3)
//     gives up ("crazy long number"), doPrintf writes %!(NOVERB) and stops, and every argument is
//     printed as EXTRA under %v, calling its String(). The parser now refuses a digit run of more
//     than 7 digits (TestWidthOverflow*, TestPrecisionOverflow*; 7 digits never trips tooLarge,
//     TestSevenDigitWidth).
//
// Checked and not a gap: a verb that is not one of the integer's (%z) reaches badVerb, which prints
// the argument under %v with p.erroring set, so handleMethods calls no method (print.go:374-393,
// 614-617): fmt.argOkAt's integer disjunct is right for every non-method verb (TestBadVerbNoString);
// under the integer verbs String is not called either (TestIntVerbsNoString).

import (
	"fmt"
	"testing"
	"time"

	"k8s.io/klog/v2"
)

// hangInt's String never returns; called only if fmt prints the value with a method verb.
type hangInt int64

func (hangInt) String() string { select {} }

// nestInt's String panics with a value whose String panics (escapes fmt's catchPanic).
type nestInt int64

func (nestInt) String() string { panic(badStr{}) }

// cntInt counts its String calls.
type cntInt int64

var cntCalls int

func (cntInt) String() string { cntCalls++; return "s" }

func returnsWithin(f func(), d time.Duration) bool {
	done := make(chan struct{})
	go func() { defer close(done); f() }()
	select {
	case <-done:
		return true
	case <-time.After(d):
		return false
	}
}

func TestSevenDigitWidth(t *testing.T) {
	if !returnsWithin(func() { klog.Errorf("%1234567d|", hangInt(5)) }, 5*time.Second) {
		t.Fatal("a 7-digit width did not return")
	}
	if !returnsWithin(func() { klog.Errorf("%.9999999d|", hangInt(5)) }, 5*time.Second) {
		t.Fatal("a 7-digit precision did not return")
	}
}

func TestWidthOverflowHangs(t *testing.T) {
	if returnsWithin(func() { klog.Errorf("rev %99999999d", hangInt(5)) }, 2*time.Second) {
		t.Fatal("returned")
	}
}

func TestPrecisionOverflowHangs(t *testing.T) {
	if returnsWithin(func() { klog.Errorf("rev %.99999999d", hangInt(5)) }, 2*time.Second) {
		t.Fatal("returned")
	}
}

func TestWidthOverflowPanicEscapes(t *testing.T) {
	if p := recovered(func() { klog.Errorf("rev %99999999d", nestInt(5)) }); p == nil {
		t.Fatal("no panic escaped")
	}
}

func TestWidthOverflowNoVerb(t *testing.T) {
	if got := fmt.Sprintf("rev %99999999d", int64(5)); got != "rev %!(NOVERB)%!(EXTRA int64=5)" {
		t.Fatalf("got %q", got)
	}
}

// badVerbFmt is a variable: vet refuses a literal unknown verb.
var badVerbFmt = "rev %z|"

func TestBadVerbNoString(t *testing.T) {
	if !returnsWithin(func() { klog.Errorf(badVerbFmt, hangInt(5)) }, 5*time.Second) {
		t.Fatal("String called under %z")
	}
	if p := recovered(func() { klog.Errorf(badVerbFmt, nestInt(5)) }); p != nil {
		t.Fatalf("panic under %%z: %v", p)
	}
}

func TestIntVerbsNoString(t *testing.T) {
	cntCalls = 0
	for _, v := range []string{"d", "b", "o", "O", "c", "U"} {
		_ = fmt.Sprintf("%"+v, cntInt(65))
	}
	if cntCalls != 0 {
		t.Fatalf("String called %d times", cntCalls)
	}
}
