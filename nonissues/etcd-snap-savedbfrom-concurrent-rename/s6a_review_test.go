package snap

import (
	"bytes"
	"io"
	"os"
	"path/filepath"
	"sync"
	"testing"

	"go.uber.org/zap"
	"go.uber.org/zap/zaptest/observer"
)

type gateReader struct {
	data []byte
	gate chan struct{}
	done bool
}

func (g *gateReader) Read(p []byte) (int, error) {
	if !g.done {
		<-g.gate
		g.done = true
		n := copy(p, g.data)
		return n, nil
	}
	return 0, io.EOF
}

// Two snapshotters (two incarnations) on one directory, saving the same index
// concurrently: count iterations where both took the rename branch.
func TestS6aTwoSnapshottersDoubleRename(t *testing.T) {
	both := 0
	N := 3000
	for it := 0; it < N; it++ {
		dir := t.TempDir()
		core, logs := observer.New(zap.InfoLevel)
		lg := zap.New(core)
		s1 := New(lg, dir)
		s2 := New(lg, dir)
		gate := make(chan struct{})
		var wg sync.WaitGroup
		for k, s := range []*Snapshotter{s1, s2} {
			wg.Add(1)
			r := &gateReader{data: bytes.Repeat([]byte{byte('A' + k)}, 64), gate: gate}
			go func(s *Snapshotter) {
				defer wg.Done()
				if _, err := s.SaveDBFrom(r, 5); err != nil {
					t.Errorf("err %v", err)
				}
			}(s)
		}
		close(gate)
		wg.Wait()
		if logs.FilterMessage("saved database snapshot to disk").Len() == 2 {
			both++
		}
		_ = filepath.Join
		_ = os.Remove
	}
	t.Logf("both renamed (TOCTOU) in %d of %d iterations", both, N)
}
