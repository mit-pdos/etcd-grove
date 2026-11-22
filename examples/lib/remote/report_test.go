package remote

import (
	"fmt"
	"math/rand/v2"
	"testing"
	"time"
)

// strCodec is a codec of strings (inputs and outputs: the bytes themselves).
func strCodec() Codec {
	return Codec{
		EncIn:  func(in any) []byte { return []byte(in.(string)) },
		DecIn:  func(b []byte) (any, bool) { return string(b), true },
		EncOut: func(out any) []byte { return []byte(out.(string)) },
		DecOut: func(b []byte) (any, bool) { return string(b), true },
	}
}

// TestReport: Report gets each node's answer (a loop's report: here the input
// repeated), and an attempt at an address nobody serves fails.
func TestReport(t *testing.T) {
	base := 7400 + 10*rand.IntN(100)
	var addrs []string
	var ins []any
	for c := 0; c < 3; c++ {
		a := fmt.Sprintf("127.0.0.1:%d", base+c)
		addrs = append(addrs, a)
		ins = append(ins, fmt.Sprintf("in%d", c))
		op := func(_ any, in any) any {
			time.Sleep(50 * time.Millisecond)
			return in.(string) + in.(string)
		}
		go ServeClient(c, a, func(int) any { return nil }, op, strCodec(), time.Second)
	}
	time.Sleep(100 * time.Millisecond)
	out, ok := Report(addrs[0], "x", strCodec(), time.Second)
	if !ok || out.(string) != "xx" {
		t.Fatalf("Report: %v %v", out, ok)
	}
	for c := range addrs {
		out, ok := Report(addrs[c], ins[c], strCodec(), time.Second)
		if !ok || out.(string) != ins[c].(string)+ins[c].(string) {
			t.Fatalf("Report %d: %v %v", c, out, ok)
		}
	}
	if _, ok := Report(fmt.Sprintf("127.0.0.1:%d", base+9), "x", strCodec(), 200*time.Millisecond); ok {
		t.Fatalf("Report answered from nobody")
	}
	// an attempt shorter than the operation: no answer
	if _, ok := Report(addrs[1], "x", strCodec(), 10*time.Millisecond); ok {
		t.Fatalf("Report answered after its deadline")
	}
}
