// Package sprintfclientptr is the Go evidence against the trust-boundary axiom
// fmt.SprintfClientPtr.wp_proof as it stood until 2026-11-20 (Spec/fmt/SprintfClientPtr.lean,
// notes/axiom-review/sprintfclientptr.md): it admitted any format string for arguments that are
// basic values or a *clientv3.Client, with no ownership of the client, and said Sprintf returns.
// Go formats a pointer to a struct under %v or %s (and as an EXTRA argument, under %v) by printing
// the struct's fields (fmt/print.go:902-911), reading the client's memory and calling the
// String/Error methods of the values in its exported fields (printValue at depth > 0,
// print.go:756-763): a concurrent writer races with it. Only %p (print.go:686-693, before
// handleMethods) formats the pointer itself. The axiom's one caller, clientv3's dial
// (client.go:327, "%s://%p/%s"), uses %p; the fixed spec requires that.
// Tests only, no Goose project.
package sprintfclientptr

import (
	"fmt"
	"strings"
	"testing"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// spyKV is a clientv3.KV whose String() records that fmt called it.
type spyKV struct {
	clientv3.KV
	called *bool
}

func (k spyKV) String() string { *k.called = true; return "spy" }

func TestPercentVReadsClientFields(t *testing.T) {
	called := false
	c := &clientv3.Client{KV: spyKV{called: &called}, Username: "alice"}
	out := fmt.Sprintf("%v", c)
	if !strings.HasPrefix(out, "&{") || !strings.Contains(out, "alice") {
		t.Fatalf("%%v of *Client did not print its fields: %q", out)
	}
	if !called {
		t.Fatalf("%%v of *Client did not call its KV field's String(): %q", out)
	}
	// As an EXTRA argument (no directive left), it is printed under %v too.
	called = false
	noDirective := "x"
	if out := fmt.Sprintf(noDirective, c); !called || !strings.Contains(out, "EXTRA") {
		t.Fatalf("EXTRA *Client: %q, String called %v", out, called)
	}
}

func TestPercentPReadsNothing(t *testing.T) {
	called := false
	c := &clientv3.Client{KV: spyKV{called: &called}}
	out := fmt.Sprintf("%s://%p/%s", "etcd-endpoints", c, "localhost:2379")
	if called || !strings.HasPrefix(out, "etcd-endpoints://0x") {
		t.Fatalf("%%p of *Client: %q, String called %v", out, called)
	}
}
