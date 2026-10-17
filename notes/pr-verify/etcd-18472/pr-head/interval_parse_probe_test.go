// Probe of etcd#18472's parseCompactionInterval (package embed, at the PR head
// 7842e283ce2e591e78e9c59f5ed287722782ab08): a negative or tiny duration is accepted.
package embed

import (
	"testing"
	"time"
)

func TestProbeParseCompactionIntervalAcceptsNegative(t *testing.T) {
	for _, s := range []string{"-1s", "-5m", "1ns", "0s"} {
		d, err := parseCompactionInterval(s)
		t.Logf("parseCompactionInterval(%q) = %v, %v", s, d, err)
		if err != nil {
			t.Fatalf("%q rejected: %v", s, err)
		}
	}
	if d, _ := parseCompactionInterval("-1s"); d != -time.Second {
		t.Fatalf("got %v", d)
	}
}
