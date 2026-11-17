//go:build with_tla

package tracecheck

import (
	"bytes"
	"go.etcd.io/raft/v3"
	"reflect"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft/ndjson"
)

type raftEvent = raft.TracingEvent

// TestConvertMatchesNDJSON: ConvertEvents (Main's path, in memory) gives the events the NDJSON
// path (WriteNDJSON, then ndjson.ReadNDJSON: what TLC's comparison reads) gives, on the traces of
// both harnesses, the full configurations included (configuration changes: the cc property).
func TestConvertMatchesNDJSON(t *testing.T) {
	for seed := uint64(1); seed <= 3; seed++ {
		s, err := New(FullConfig(seed))
		if err != nil {
			t.Fatal(err)
		}
		if err := s.Run(); err != nil {
			t.Fatal(err)
		}
		c, err := RunConcurrent(FullCConfig())
		if err != nil {
			t.Fatal(err)
		}
		for name, events := range map[string][]any{"sim": {s.Events()}, "concurrent": {c.Events()}} {
			raw := events[0].([]raftEvent)
			var buf bytes.Buffer
			if err := WriteNDJSON(&buf, raw); err != nil {
				t.Fatal(err)
			}
			viaJSON, err := ndjson.ReadNDJSON(&buf)
			if err != nil {
				t.Fatal(err)
			}
			direct := ConvertEvents(raw)
			if len(direct) != len(viaJSON) {
				t.Fatalf("%s seed %d: %d events converted, %d read back", name, seed, len(direct), len(viaJSON))
			}
			for k := range direct {
				if !reflect.DeepEqual(direct[k], viaJSON[k]) {
					t.Fatalf("%s seed %d, event %d: converted %+v, read back %+v", name, seed, k+1, direct[k], viaJSON[k])
				}
			}
		}
	}
}

// TestMainRuns runs the closed program: it must not panic.
func TestMainRuns(t *testing.T) {
	Main()
}
